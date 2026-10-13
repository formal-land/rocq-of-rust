#!/usr/bin/env python3

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from argparse import Namespace
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch


SCRIPT_PATH = Path(__file__).with_name("revm_state_fixture_test.py")
SPEC = importlib.util.spec_from_file_location("revm_state_fixture_test", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
fixture_test = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = fixture_test
SPEC.loader.exec_module(fixture_test)


class RevmStateFixtureTestTest(unittest.TestCase):
    def test_fixture_root_default_and_relative_override(self) -> None:
        probe = (
            "import runpy, sys; "
            "print(runpy.run_path(sys.argv[1])['FIXTURE_ROOT'])"
        )
        with tempfile.TemporaryDirectory() as directory:
            environment = os.environ.copy()
            environment.pop("REVM_FIXTURE_ROOT", None)
            for override in (None, "relative-fixtures/../GeneralStateTests"):
                with self.subTest(override=override):
                    if override is not None:
                        environment["REVM_FIXTURE_ROOT"] = override
                    result = subprocess.run(
                        [sys.executable, "-c", probe, str(SCRIPT_PATH.resolve())],
                        cwd=directory,
                        env=environment,
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    expected = (
                        fixture_test.REPO_ROOT / "tests/revm-testdata/GeneralStateTests"
                        if override is None
                        else Path(directory) / "GeneralStateTests"
                    )
                    self.assertEqual(Path(result.stdout.strip()), expected.resolve())

    def test_run_coqc_uses_standalone_load_path(self) -> None:
        source = Path("/tmp/fixture-check.v")
        with patch.object(fixture_test.subprocess, "run") as compile_fixture:
            fixture_test.run_coqc(source)
        compile_fixture.assert_called_once_with(
            ["coqc", "-R", str(fixture_test.ROCQ_ROOT), "RocqOfRust",
             "-I", str(fixture_test.ROCQ_ROOT / "plugin"),
             "-impredicative-set", str(source)],
            cwd=fixture_test.ROCQ_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )

    def test_missing_selected_fixture_fails_before_compilation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "missing.json"
            args = Namespace(fixture=[missing], emit=None, fork="Cancun")
            with patch.object(fixture_test, "parse_args", return_value=args), \
                 patch.object(fixture_test, "run_coqc") as compile_fixture, \
                 patch("builtins.print"):
                self.assertEqual(fixture_test.main(), 1)
                compile_fixture.assert_not_called()

    def test_default_selection_rejects_partial_glob_family(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            partial = Path(directory)
            (partial / "one.json").write_text("{}")
            with patch.object(fixture_test, "SHIFT_FIXTURE_ROOT", partial):
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.select_fixtures(Namespace(fixture=None, emit=None, fork="Cancun"))

    def test_explicit_selection_does_not_require_default_families(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            custom = root / "custom.json"
            custom.write_text("{}")
            with patch.object(fixture_test, "SHIFT_FIXTURE_ROOT", root / "absent"):
                self.assertEqual(
                    fixture_test.select_fixtures(Namespace(fixture=[custom], emit=None, fork="Cancun")),
                    (custom,),
                )

    def test_osaka_selection_is_separate_from_historical_forks(self) -> None:
        args = Namespace(fixture=None, emit=None, fork="Osaka")
        self.assertEqual(fixture_test.select_fixtures(args), fixture_test.OSAKA_FIXTURES)
        self.assertEqual(len(fixture_test.OSAKA_FIXTURES), 2)
        for fork in ("Cancun", "Prague"):
            args.fork = fork
            self.assertEqual(fixture_test.select_fixtures(args), fixture_test.DEFAULT_FIXTURES)
        self.assertTrue(set(fixture_test.OSAKA_FIXTURES).isdisjoint(fixture_test.DEFAULT_FIXTURES))
        with self.assertRaises(fixture_test.FixtureError):
            fixture_test.load_state_cases(fixture_test.ADD11_FIXTURE, "Osaka")
        for path in fixture_test.OSAKA_FIXTURES:
            with self.assertRaises(fixture_test.FixtureError):
                fixture_test.load_state_cases(path, "Prague")

    def test_osaka_preserves_all_named_cases_and_exact_success(self) -> None:
        names = set()
        for path, count in zip(fixture_test.OSAKA_FIXTURES, (1, 6)):
            cases = fixture_test.load_state_cases(path, "Osaka")
            self.assertEqual(len(cases), count)
            self.assertEqual({case.name for case in cases}, set(json.loads(path.read_text())))
            for case in cases:
                names.add(case.name)
                self.assertEqual(case.fork, "Osaka")
                self.assertEqual(case.spec_id, "OSAKA")
                self.assertEqual(case.call_value, 0)
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.transaction_gas_limit, 200_000)
                self.assertIn(0x100, fixture_test.initial_warm_accounts(case))
                self.assertTrue(set(range(1, 18)).issubset(fixture_test.initial_warm_accounts(case)))
                parent = next(a for a in case.accounts if a.address == case.target_address)
                self.assertEqual(parent.storage, ((0, 0xdeadbeef),))
                self.assertEqual(parent.balance, 0)
                self.assertFalse(case.expected_accounts)
                source = fixture_test.render_rocq(path, case)
                self.assertIn("SpecId.OSAKA", source)
                self.assertIn("InterpreterDispatch.run_plain_stateful_fuel", source)
                self.assertNotIn("CallRunner.run", source)
                if count == 1:
                    self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                    self.assertIn("InstructionResult.Stop => true", source)
                else:
                    self.assertIn("run_fixture =", source)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, replace(case, call_value=1))
        self.assertEqual(len(names), 7)

    def test_osaka_clz_has_independent_storage_and_bounded_code_oracles(self) -> None:
        gas_path, memory_path = fixture_test.OSAKA_FIXTURES
        gas_case, = fixture_test.load_state_cases(gas_path, "Osaka")
        # Two GAS readings cancel the initial budget; the stored delta isolates CLZ.
        self.assertEqual(bytes(gas_case.code).hex(), "5a60011e5a905090036005900360005500600055")
        self.assertEqual(gas_case.expected_storage, ((0, 5),))
        combinations = set()
        for case in fixture_test.load_state_cases(memory_path, "Osaka"):
            bits = int(case.name.rsplit("bits_", 1)[1].rstrip("]"))
            operation = "EXTCODECOPY" if "opcode_EXTCODECOPY" in case.name else "CODECOPY"
            combinations.add((operation, bits))
            self.assertIn(bits, (0, 64, 255))
            value = 1 << bits
            word = value.to_bytes(32, "big")
            operand = value.to_bytes((value.bit_length() + 7) // 8, "big")
            code = b"\x7f" + word + bytes([0x5f + len(operand)]) + operand
            code += bytes.fromhex("1e600055602060016000")
            if operation == "EXTCODECOPY":
                other, = (a for a in case.accounts
                          if a.address != case.target_address and a.code)
                self.assertEqual(bytes(other.code), b"\x7f" + word)
                code += b"\x73" + other.address.to_bytes(20, "big") + b"\x3c"
                copied = bytes(other.code)[1:33]
            else:
                code += b"\x39"
                copied = code[1:33]
            code += bytes.fromhex("6000511e600155")
            self.assertEqual(bytes(case.code), code)
            self.assertLessEqual(len(code), 105)
            self.assertEqual(len(copied), 32)
            result = 256 - int.from_bytes(copied, "big").bit_length()
            self.assertEqual(result, 255 - bits)
            expected = ((0, result), (1, result)) if result else ()
            self.assertEqual(case.expected_storage, expected)
        self.assertEqual(combinations, {(op, bits) for op in ("CODECOPY", "EXTCODECOPY")
                                        for bits in (0, 64, 255)})

    def test_osaka_main_runs_every_named_case_without_legacy_prerequisites(self) -> None:
        args = Namespace(fixture=None, emit=None, fork="Osaka")
        with patch.object(fixture_test, "parse_args", return_value=args), \
             patch.object(fixture_test, "run_coqc",
                          return_value=subprocess.CompletedProcess([], 0, "")) as compile_case, \
             patch.object(fixture_test, "check_exceptional_halt_regression") as exceptional, \
             patch.object(fixture_test, "check_access_list_regressions") as access_list, \
             patch("builtins.print") as report:
            self.assertEqual(fixture_test.main(), 0)
        exceptional.assert_not_called()
        access_list.assert_not_called()
        self.assertEqual(compile_case.call_count, 7)
        messages = [call.args[0] for call in report.call_args_list]
        self.assertEqual(len(messages), 7)
        for path in fixture_test.OSAKA_FIXTURES:
            for case in fixture_test.load_state_cases(path, "Osaka"):
                self.assertEqual(sum(case.name in message for message in messages), 1)
        self.assertTrue(all(message.endswith("fork Osaka, post case 0") for message in messages))

    def test_osaka_rejects_modified_pinned_fixture(self) -> None:
        source = fixture_test.OSAKA_FIXTURES[0]
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / source.name
            changed.write_bytes(source.read_bytes() + b"\n")
            with patch.dict(fixture_test.OSAKA_SELECTION,
                            {changed: fixture_test.OSAKA_SELECTION[source]}):
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.load_state_cases(changed, "Osaka")

    def test_modexp_selection_and_independent_storage_oracles(self) -> None:
        expected_outputs = (bytes(31) + b"\x01", b"\x00", b"\x01", b"\x00",
                            b"\x00\x02", b"\x02", b"\x00\x00", b"\x00\x00")
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.MODEXP_FIXTURES:
                cases = fixture_test.load_state_cases(path, fork)
                return_sizes = "returndatasize" in path.name
                self.assertEqual(len(cases), 4 if return_sizes else 8)
                code = ("36600060003760206103e8366000600060055af2600155"
                        "6103e851600255" + ("3d600355" if return_sizes else "") + "00")
                for index, case in enumerate(cases):
                    self.assertEqual(bytes(case.code), bytes.fromhex(code))
                    self.assertEqual(case.call_value, 0)
                    self.assertEqual(case.transaction_gas_limit,
                                     1000000000 if return_sizes else 90000)
                    self.assertEqual(case.target_address, 2**156)
                    parent = next(a for a in case.accounts if a.address == case.target_address)
                    self.assertEqual(parent.balance, 0)
                    self.assertEqual(parent.storage, ((3, 0xffffffff),) if return_sizes else ())
                    self.assertLessEqual(len(case.calldata), 480)
                    data = bytes(case.calldata)
                    lengths = tuple(int.from_bytes(data[j:j + 32], "big")
                                    for j in (0, 32, 64))
                    self.assertLessEqual(max(lengths), 256)
                    base_len, exp_len, mod_len = lengths
                    body = data[96:].ljust(sum(lengths), b"\x00")
                    base = int.from_bytes(body[:base_len], "big")
                    exp = int.from_bytes(body[base_len:base_len + exp_len], "big")
                    modulus = int.from_bytes(body[base_len + exp_len:], "big")
                    output = (pow(base, exp, modulus) if modulus else 0).to_bytes(mod_len, "big")
                    if return_sizes:
                        self.assertEqual(mod_len, (0, 1, 100, 256)[index])
                        self.assertEqual(output, bytes(mod_len))
                    else:
                        self.assertEqual(output, expected_outputs[index])
                    storage = {1: 1}
                    first_word = int.from_bytes(output[:32].ljust(32, b"\x00"), "big")
                    if first_word:
                        storage[2] = first_word
                    if return_sizes and mod_len:
                        storage[3] = mod_len
                    self.assertEqual(case.expected_storage, tuple(sorted(storage.items())))
                    self.assertFalse(case.expected_accounts)
                    source = fixture_test.render_rocq(path, case)
                    self.assertIn("CallRunner.run", source)
                    self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                    self.assertIn("InstructionResult.Stop => true", source)
                    with self.assertRaises(fixture_test.FixtureError):
                        fixture_test.render_rocq(path, case, "OutOfGas")

    def test_modexp_rejects_changed_pinned_file_and_unsupported_fork(self) -> None:
        path = fixture_test.MODEXP_FIXTURES[0]
        with patch.object(Path, "read_bytes", return_value=b"{}"):
            with self.assertRaisesRegex(fixture_test.FixtureError, "pinned audited"):
                fixture_test.load_state_cases(path, "Cancun")
        with self.assertRaisesRegex(fixture_test.FixtureError, "only Cancun and Prague"):
            fixture_test.load_state_cases(path, "Osaka")

    def test_modexp_never_loads_unselected_stress_cases(self) -> None:
        for path, (_, indices) in fixture_test.MODEXP_SELECTION.items():
            with patch.object(fixture_test, "load_state_case", return_value=None) as load:
                fixture_test.load_state_cases(path, "Cancun")
                self.assertEqual([call.args[2] for call in load.call_args_list], list(indices))

    def test_mcopy_cases_require_exact_stop_and_zero_entry_value(self) -> None:
        path = fixture_test.MCOPY_FIXTURE
        self.assertIn(path, fixture_test.DEFAULT_FIXTURES)
        for fork in ("Cancun", "Prague"):
            cases = fixture_test.load_state_cases(path, fork)
            self.assertEqual(len(cases), 20)
            for case in cases:
                source = fixture_test.render_rocq(path, case)
                self.assertIn("InterpreterDispatch.run_plain_stateful_fuel", source)
                self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                predicate = source.split("Definition run_fixture_exact_halt", 1)[1].split(
                    "Definition run_fixture_out_of_gas", 1)[0]
                self.assertIn("InstructionResult.Stop => true", predicate)
                self.assertIn("| _ => false", predicate)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, replace(case, call_value=1))

    def test_mcopy_fixture_matches_bounded_snapshot_copy(self) -> None:
        # The bytecode initializes 96 bytes, performs one MCOPY, then stores
        # all three words. It reads neither absolute gas nor account balances.
        initial_memory = bytes(range(0xa0, 0x100))
        code = (
            "7f" + initial_memory[:32].hex() + "5f52"
            "7f" + initial_memory[32:64].hex() + "602052"
            "7f" + initial_memory[64:].hex() + "604052"
            "60786040356020355f35608a565b5f515f55602051600155604051600255005b5e56"
        )
        for fork in ("Cancun", "Prague"):
            coverage = set()
            for case in fixture_test.load_state_cases(fixture_test.MCOPY_FIXTURE, fork):
                self.assertEqual(bytes(case.code), bytes.fromhex(code))
                self.assertEqual(case.call_value, 0)
                self.assertEqual(case.transaction_gas_limit, 1_000_000)
                self.assertEqual(len(case.calldata), 96)
                parent = next(a for a in case.accounts if a.address == case.target_address)
                self.assertEqual(parent.storage, ())
                self.assertNotIn(case.target_address, (case.caller_address, case.coinbase))
                data = bytes(case.calldata)
                dst, src, length = (int.from_bytes(data[i:i + 32], "big")
                                    for i in (0, 32, 64))
                self.assertLessEqual(max(dst, src), 33)
                self.assertLessEqual(length, 51)
                self.assertLessEqual(max(dst, src) + length, len(initial_memory))
                # Snapshot the source before writing, including overlapping copies.
                memory = bytearray(initial_memory)
                memory[dst:dst + length] = initial_memory[src:src + length]
                expected = tuple((i, int.from_bytes(memory[32 * i:32 * (i + 1)], "big"))
                                 for i in range(3))
                self.assertEqual(case.expected_storage, expected)
                if length == 0:
                    coverage.add("empty")
                elif dst == src:
                    coverage.add("self")
                elif src < dst < src + length:
                    coverage.add("overlap_right")
                elif dst < src < dst + length:
                    coverage.add("overlap_left")
            self.assertEqual(coverage, {"empty", "self", "overlap_right", "overlap_left"})

    def test_ripemd160_cases_have_exact_halts_and_storage_oracles(self) -> None:
        self.assertEqual(len(fixture_test.RIPEMD160_FIXTURES), 12)
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.RIPEMD160_FIXTURES:
                cases = fixture_test.load_state_cases(path, fork)
                self.assertEqual(len(cases), 1)
                case = cases[0]
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                predicate = source.split("Definition run_fixture_exact_halt", 1)[1].split(
                    "Definition run_fixture_out_of_gas", 1)[0]
                self.assertIn("InstructionResult.Stop => true", predicate)
                self.assertIn("| _ => false", predicate)
                self.assertFalse(case.expected_accounts)
                self.assertIn("fixture_account_storage_matches host", source)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")

    def test_ripemd160_storage_selection_locks_entry_transfer_noninterference(self) -> None:
        # All calls have zero value and fixed gas well below the cap even after
        # intrinsic gas. Memory is at most 64 bytes; no balance/CALLVALUE/GAS read.
        # The gas719 case fails: one word costs 720 gas; output memory stays unchanged.
        patterns = {
            "_1": ("", "6000", "610258",
                   0x9c1185a5c5e9fc54612808977ee8f548b2258d31),
            "_2": ("64f34578907f600552", "6025", "611770",
                   0xdbc100f916bfbc53535573d98cf0cbb3a5b36124),
            "_3_postfixed0": ("65f34578907f00600052", "6025", "611770",
                   0x7730b4642169b0f16752696da8da830a4b429c9d),
            "_4_gas719": ("7f" + "ff" * 32 + "600052", "6020", "6102cf",
                   2**256 - 1),
        }
        expected = {}
        for prefix, opcode, value_arg in (("Call", "f1", "6000"),
                                          ("CALLCODE", "f2", "6000"),
                                          ("static_Call", "fa", "")):
            for suffix, (setup, size, gas, digest) in patterns.items():
                code = (setup + "60206000" + size + "6000" + value_arg
                        + "6003" + gas + opcode + "60025560005160005500")
                expected[f"{prefix}Ripemd160{suffix}.json"] = (code, digest)
        self.assertEqual(set(expected), {p.name for p in fixture_test.RIPEMD160_FIXTURES})
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.RIPEMD160_FIXTURES:
                case = fixture_test.load_state_case(path, fork)
                code, digest = expected[path.name]
                self.assertEqual(bytes(case.code), bytes.fromhex(code))
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.call_value, 100000)
                self.assertEqual(case.transaction_gas_limit, 365224)
                expected_storage = ((0, digest),) if "gas719" in path.name else ((0, digest), (2, 1))
                self.assertEqual(case.expected_storage, expected_storage)
                parent = next(a for a in case.accounts if a.address == case.target_address)
                self.assertEqual(parent.balance, 20000000)
                self.assertEqual(parent.storage, ())
                self.assertNotIn(case.target_address, (case.caller_address, case.coinbase, 3))
                self.assertNotIn(3, (case.caller_address, case.coinbase))
                self.assertEqual(dict(case.expected_account_storage)[case.caller_address], ())

    def test_sha256_cases_have_exact_halts_and_storage_oracles(self) -> None:
        self.assertEqual(len(fixture_test.SHA256_FIXTURES), 12)
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.SHA256_FIXTURES:
                cases = fixture_test.load_state_cases(path, fork)
                self.assertEqual(len(cases), 1)
                case = cases[0]
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                predicate = source.split("Definition run_fixture_exact_halt", 1)[1].split(
                    "Definition run_fixture_out_of_gas", 1)[0]
                self.assertIn("InstructionResult.Stop => true", predicate)
                self.assertIn("| _ => false", predicate)
                self.assertFalse(case.expected_accounts)
                self.assertIn("fixture_account_storage_matches host", source)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")

    def test_sha256_storage_selection_locks_entry_transfer_noninterference(self) -> None:
        # All calls have zero value and fixed gas well below the cap even after
        # intrinsic gas. Memory is at most 64 bytes; no balance/CALLVALUE/GAS read.
        # The legacy gas99 filename is a success case: one word costs 72 gas.
        patterns = {
            "_1": ("", "6000", "6101f4",
                   0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855),
            "_2": ("64f34578907f600552", "6025", "6101f4",
                   0xcb39b3bde22925b2f931111130c774761d8895e0e08437c9b396c1e97d10f34d),
            "_3_postfix0": ("65f34578907f00600052", "6025", "6101f4",
                   0x3b745a1c00d035c334f358d007a430e4cf0ae63aa0556fb05529706de546464d),
            "_4_gas99": ("7f" + "ff" * 32 + "600052", "6020", "6063",
                   0xaf9613760f72635fbdb44a5a0a63c39f12af30f950a6ee5c971be188e89c4051),
        }
        expected = {}
        for prefix, opcode, value_arg in (("Call", "f1", "6000"),
                                          ("CALLCODE", "f2", "6000"),
                                          ("static_Call", "fa", "")):
            for suffix, (setup, size, gas, digest) in patterns.items():
                code = (setup + "60206000" + size + "6000" + value_arg
                        + "6002" + gas + opcode + "60025560005160005500")
                expected[f"{prefix}Sha256{suffix}.json"] = (code, digest)
        self.assertEqual(set(expected), {p.name for p in fixture_test.SHA256_FIXTURES})
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.SHA256_FIXTURES:
                case = fixture_test.load_state_case(path, fork)
                code, digest = expected[path.name]
                self.assertEqual(bytes(case.code), bytes.fromhex(code))
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.call_value, 100000)
                self.assertEqual(case.transaction_gas_limit, 365224)
                self.assertEqual(case.expected_storage, ((0, digest), (2, 1)))
                parent = next(a for a in case.accounts if a.address == case.target_address)
                self.assertEqual(parent.balance, 20000000)
                self.assertEqual(parent.storage, ())
                self.assertNotIn(case.target_address, (case.caller_address, case.coinbase, 2))
                self.assertNotIn(2, (case.caller_address, case.coinbase))
                self.assertEqual(dict(case.expected_account_storage)[case.caller_address], ())

    def test_identity_cases_have_exact_halts_and_account_or_storage_oracles(self) -> None:
        self.assertEqual(len(fixture_test.IDENTITY_FIXTURES), 12)
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.IDENTITY_FIXTURES:
                cases = fixture_test.load_state_cases(path, fork)
                self.assertEqual(len(cases), 1)
                case = cases[0]
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                predicate = source.split("Definition run_fixture_exact_halt", 1)[1].split(
                    "Definition run_fixture_out_of_gas", 1)[0]
                self.assertIn("InstructionResult.Stop => true", predicate)
                self.assertIn("| _ => false", predicate)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")
                if path in fixture_test.IDENTITY_ACCOUNT_FIXTURES:
                    self.assertEqual(case.call_value, 0)
                    self.assertTrue(case.expected_accounts)
                    self.assertIn("fixture_account_state_matches host", source)
                    with self.assertRaises(fixture_test.FixtureError):
                        fixture_test.render_rocq(path, replace(case, expected_accounts=()))
                    original = json.loads(path.read_text())
                    next(iter(original.values()))["transaction"]["value"] = ["0x01"]
                    with patch.object(Path, "read_text", return_value=json.dumps(original)):
                        with self.assertRaises(fixture_test.FixtureError):
                            fixture_test.load_state_cases(path, fork)
                else:
                    self.assertFalse(case.expected_accounts)
                    self.assertIn("fixture_account_storage_matches host", source)

    def test_identity_storage_selection_locks_entry_transfer_noninterference(self) -> None:
        # Every call has fixed zero value and a fixed gas request far below the
        # cap with or without intrinsic gas. No BALANCE, CALLVALUE or GAS read.
        # The 64-byte output case observes its untouched second memory word.
        full_word = "7f" + "ff" * 32 + "600052"
        expected = {
            "CallIdentitiy_1.json": ("6020600060006000600060046101f4f160025560005160005500",
                                    ((2, 1),), 365224),
            "CallIdentity_2.json": ("64f34578907f6000526020600060256000600060046101f4f160025560005160005500",
                                    ((0, 0xf34578907f), (2, 1)), 365224),
            "CallIdentity_6_inputShorterThanOutput.json":
                (full_word + "611234602052604060006020600060006004610258f15060205160005500",
                 ((0, 0x1234),), 10000000),
        }
        for prefix, opcode, value_arg in (("Call", "f1", "6000"),
                                          ("CALLCODE", "f2", "6000"),
                                          ("static_Call", "fa", "")):
            for gas in (17, 18):
                code = (full_word + "6020600060206000" + value_arg + "600460"
                        + f"{gas:02x}" + opcode + "60025560005160005500")
                storage = ((0, 2 ** 256 - 1),) + (((2, 1),) if gas == 18 else ())
                expected[f"{prefix}Identity_4_gas{gas}.json"] = (code, storage, 365224)
        self.assertEqual(set(expected), {p.name for p in fixture_test.IDENTITY_STORAGE_FIXTURES})
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.IDENTITY_STORAGE_FIXTURES:
                case = fixture_test.load_state_case(path, fork)
                code, storage, gas = expected[path.name]
                self.assertEqual(bytes(case.code), bytes.fromhex(code))
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.call_value, 100000)
                self.assertEqual(case.transaction_gas_limit, gas)
                self.assertEqual(case.expected_storage, storage)
                parent = next(a for a in case.accounts if a.address == case.target_address)
                self.assertEqual(parent.balance, 20000000)
                self.assertEqual(parent.storage, ())
                self.assertNotIn(case.target_address, (case.caller_address, case.coinbase, 4))
                self.assertNotIn(4, (case.caller_address, case.coinbase))
                self.assertEqual(dict(case.expected_account_storage)[case.caller_address], ())

    def test_identity_account_selection_locks_return_buffer_and_constructor_observations(self) -> None:
        word = "7f112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00600052"
        expected = {
            "identity_to_bigger.json": (word + "602060106010600060006004620186a0f1503d60005500", 16, 200000),
            "identity_to_smaller.json": (word + "601060106020600060006004620186a0f1503d60005500", 32, 200000),
            "create_callprecompile_returndatasize.json":
                ("602380601560003960006000f0503d6000550000fe62112233600052602060006020600060006004619000f1503d60005560206000f30000",
                 None, 0x0a00000000),
        }
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.IDENTITY_ACCOUNT_FIXTURES:
                case = fixture_test.load_state_case(path, fork)
                code, size, gas = expected[path.name]
                self.assertEqual(bytes(case.code), bytes.fromhex(code))
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.transaction_gas_limit, gas)
                before = {a.address: a for a in case.accounts}
                after = {a.address: a for a in case.expected_accounts}
                self.assertEqual(before[case.target_address].balance, 0)
                self.assertNotIn(4, (case.caller_address, case.coinbase, case.target_address))
                self.assertEqual(case.expected_storage, ((0, size),) if size else ())
                if size is None:
                    created = int("945304eb96065b2a98b57a48a06ae28d285a71b5", 16)
                    self.assertNotIn(created, before)
                    self.assertNotIn(created, (case.caller_address, case.coinbase))
                    self.assertEqual(after[created].code, (0,) * 29 + (0x11, 0x22, 0x33))
                    self.assertEqual(after[created].storage, ((0, 32),))
                    self.assertEqual(after[created].nonce, 1)
                    self.assertEqual(after[created].balance, 0)
                    self.assertEqual(after[case.target_address].nonce, 1)

    def test_selfdestruct_cases_have_exact_halts_and_full_account_oracles(self) -> None:
        self.assertEqual(len(fixture_test.SELFDESTRUCT_FIXTURES), 5)
        for fork in ("Cancun", "Prague"):
            cases = [(path, case) for path in fixture_test.SELFDESTRUCT_FIXTURES
                     for case in fixture_test.load_state_cases(path, fork)]
            self.assertEqual(len(cases), 7)
            for path, case in cases:
                self.assertEqual(case.call_value, 0)
                self.assertTrue(case.expected_accounts)
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertIn("fixture_account_state_matches host", source)
                self.assertRegex(source, r"run_fixture_exact_halt\s*=\s*Some")
                result = ("SelfDestruct" if path in fixture_test.SELFDESTRUCT_DIRECT_FIXTURES
                          else "Stop")
                predicate = source.split("Definition run_fixture_exact_halt", 1)[1].split(
                    "Definition run_fixture_out_of_gas", 1)[0]
                self.assertIn(f"InstructionResult.{result} => true", predicate)
                self.assertIn("| _ => false", predicate)
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, replace(case, expected_accounts=()))
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.render_rocq(path, case, "OutOfGas")
                original = json.loads(path.read_text())
                next(iter(original.values()))["transaction"]["value"] = ["0x01"]
                with patch.object(Path, "read_text", return_value=json.dumps(original)):
                    with self.assertRaises(fixture_test.FixtureError):
                        fixture_test.load_state_cases(path, fork)

    def test_selfdestruct_selection_locks_execution_and_balance_assumptions(self) -> None:
        beneficiary = int("c94f5374fce5edbc8e2a8697c15331677e6ebf0b", 16)
        parent_address = int("cc" * 20, 16)
        for fork in ("Cancun", "Prague"):
            for index, path in enumerate(fixture_test.SELFDESTRUCT_DIRECT_FIXTURES):
                case = fixture_test.load_state_case(path, fork)
                self.assertEqual(bytes(case.code), bytes.fromhex(f"73{beneficiary:040x}ff00"))
                self.assertEqual(case.calldata, ())
                self.assertEqual(case.transaction_gas_limit, 600000)
                before = {a.address: a for a in case.accounts}
                after = {a.address: a for a in case.expected_accounts}
                self.assertNotIn(case.target_address, (case.caller_address, case.coinbase))
                self.assertEqual(before[case.target_address].balance, 0)
                self.assertEqual(before[case.target_address], after[case.target_address])
                self.assertNotIn(beneficiary, (case.caller_address, case.coinbase))
                if index == 0:
                    self.assertNotIn(beneficiary, before)
                    self.assertNotIn(beneficiary, after)
                else:
                    self.assertEqual(before[beneficiary], after[beneficiary])
                    self.assertEqual(after[beneficiary].balance, (10, 100, 10)[index - 1])
                storage = ((0, 1),) if index == 3 else ()
                self.assertEqual(after[case.target_address].storage, storage)
            cases = fixture_test.load_state_cases(fixture_test.SELFDESTRUCT_CALL_FIXTURE, fork)
            for index, case in enumerate(cases):
                self.assertEqual(case.target_address, parent_address)
                self.assertNotIn(parent_address, (case.caller_address, case.coinbase))
                self.assertEqual(bytes(case.code), bytes.fromhex("600060006000600060006004355af100"))
                self.assertEqual(bytes(case.calldata), bytes.fromhex("693c6139")
                                 + (0x1000 + index).to_bytes(32, "big"))
                self.assertEqual(case.transaction_gas_limit, 80000000)
                before = {a.address: a for a in case.accounts}
                after = {a.address: a for a in case.expected_accounts}
                for child, code in ((0x1000, "33ff00"), (0x1001, "61deadff00"),
                                    (0x1002, "30ff00")):
                    self.assertEqual(before[child].balance,
                                     0xff000000000000 if child == 0x1000 else 0x100000000000)
                    self.assertEqual(bytes(before[child].code), bytes.fromhex(code))
                    self.assertEqual(after[child].code, before[child].code)
                    self.assertEqual(after[child].nonce, before[child].nonce)
                    self.assertEqual(after[child].storage, before[child].storage)
                    self.assertNotIn(child, (case.caller_address, case.coinbase))
                    balance = 0 if child == 0x1000 + index and index < 2 else before[child].balance
                    self.assertEqual(after[child].balance, balance)
                self.assertEqual(before[parent_address].balance, 0x100000000000)
                self.assertEqual(after[parent_address].balance,
                                 0xff100000000000 if index == 0 else 0x100000000000)
                if index == 1:
                    self.assertNotIn(0xdead, before)
                    self.assertEqual(after[0xdead].balance, 0x100000000000)
                    self.assertEqual(after[0xdead].code, ())
                    self.assertEqual(after[0xdead].nonce, 0)
                    self.assertEqual(after[0xdead].storage, ())
                    self.assertNotIn(0xdead, (case.caller_address, case.coinbase))

    def test_log_cases_compare_expected_hash_on_both_forks(self) -> None:
        self.assertEqual(len(fixture_test.LOG_FIXTURES), 46)
        for fork in ("Cancun", "Prague"):
            for path in fixture_test.LOG_FIXTURES:
                case = fixture_test.load_state_case(path, fork)
                test = next(iter(json.loads(path.read_text()).values()))
                self.assertEqual(case.expected_logs_hash,
                                 int(test["post"][fork][0]["logs"], 16))
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertIn("LogObservation.hash host.(StatefulHost.logs)", source)
                self.assertIn(str(case.expected_logs_hash), source)
                self.assertTrue(case.expected_account_storage)

    def test_log_hash_cannot_be_missing_or_malformed(self) -> None:
        path = fixture_test.LOG_FIXTURES[0]
        original = json.loads(path.read_text())
        for value in (None, "0x", "0x00", "0x" + "ff" * 33, "0xzz"):
            document = json.loads(json.dumps(original))
            next(iter(document.values()))["post"]["Cancun"][0]["logs"] = value
            with patch.object(Path, "read_text", return_value=json.dumps(document)):
                with self.assertRaises(fixture_test.FixtureError):
                    fixture_test.load_state_case(path, "Cancun")
        case = fixture_test.load_state_case(path, "Cancun")
        with self.assertRaises(fixture_test.FixtureError):
            fixture_test.render_rocq(path, replace(case, expected_logs_hash=None))

    def test_log_selection_does_not_observe_entry_balance_transfer(self) -> None:
        child_address = int("0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6", 16)
        prefix = "6000600060006000601773" + f"{child_address:040x}"
        parents = {bytes.fromhex(prefix + gas + "f160005500")
                   for gas in ("6103e8", "620186a0")}
        for path in fixture_test.LOG_FIXTURES:
            case = fixture_test.load_state_case(path, "Cancun")
            self.assertIn(bytes(case.code), parents)
            self.assertEqual(case.calldata, ())
            self.assertGreaterEqual(case.transaction_gas_limit, 200000)
            parent = next(a for a in case.accounts if a.address == case.target_address)
            self.assertGreaterEqual(parent.balance, 23)
            self.assertNotIn(case.target_address, (case.caller_address, case.coinbase))
            self.assertNotIn(child_address, (case.caller_address, case.coinbase))
            child = next(a for a in case.accounts if a.address == child_address)
            index = 0
            while index < len(child.code):
                opcode = child.code[index]
                # No account-balance, call-value, gas-budget or nested-call observations.
                self.assertIn(opcode, (0, 51, 81, 82, 83, 88, 160, 161, 162, 163, 164)
                              + tuple(range(96, 128)))
                index += 1 + (opcode - 95 if 96 <= opcode <= 127 else 0)

    def test_dynamic_effective_gas_price(self) -> None:
        env = {"currentBaseFee": "0x0a"}
        tx = {"maxFeePerGas": "0x14", "maxPriorityFeePerGas": "0x03"}
        self.assertEqual(fixture_test.effective_gas_price(tx, env), 13)
        self.assertEqual(fixture_test.effective_gas_price(
            dict(tx, maxFeePerGas="0x0b"), env), 11)
        self.assertEqual(fixture_test.effective_gas_price({"gasPrice": "0x07"}, env), 7)

    def test_invalid_fee_fields_rejected(self) -> None:
        env = {"currentBaseFee": "0x0a"}
        for tx in ({}, {"maxFeePerGas": "0x14"},
                   {"maxFeePerGas": "0x09", "maxPriorityFeePerGas": "0x00"},
                   {"maxFeePerGas": "0x14", "maxPriorityFeePerGas": "0x15"},
                   {"gasPrice": "0x0a", "maxFeePerGas": "0x14"}):
            with self.subTest(tx=tx), self.assertRaises(fixture_test.FixtureError):
                fixture_test.effective_gas_price(tx, env)

    def test_transient_cases_have_code_and_zero_entry_value(self) -> None:
        self.assertEqual(len(fixture_test.TRANSIENT_STORAGE_FIXTURES), 4)
        for path in fixture_test.TRANSIENT_STORAGE_FIXTURES:
            case = fixture_test.load_state_case(path, "Cancun")
            self.assertTrue(case.code)
            self.assertEqual(case.call_value, 0)
            self.assertEqual(case.gas_price, 10)

    def test_call_cases_use_frame_runner_and_check_all_account_storage(self) -> None:
        for path, case in ((path, case) for path in fixture_test.CALL_EXECUTION_FIXTURES
                           for case in fixture_test.load_state_cases(path, "Cancun")):
            source = fixture_test.render_rocq(path, case)
            self.assertIn("CallRunner.run", source)
            self.assertNotIn("InterpreterDispatch.run_plain_stateful_fuel", source)
            self.assertGreater(len(case.expected_account_storage), 1)
            self.assertIn("accept_action action && fixture_account_storage_matches host", source)
            for address, storage in case.expected_account_storage:
                self.assertIn(f"({address}, {fixture_test.render_pairs(storage)})", source)

    def test_direct_case_keeps_existing_runner(self) -> None:
        path = fixture_test.ADD11_FIXTURE
        case = fixture_test.load_state_case(path, "Cancun")
        self.assertEqual(case.expected_account_storage, ())
        self.assertIn("InterpreterDispatch.run_plain_stateful_fuel", fixture_test.render_rocq(path, case))

    def test_creation_cases_execute_with_zero_entry_value(self) -> None:
        self.assertEqual(len(fixture_test.CREATE_FIXTURES), 20)
        for path, case in ((path, case) for path in fixture_test.CREATE_FIXTURES
                           for case in fixture_test.load_state_cases(path, "Cancun")):
            self.assertTrue(case.code)
            self.assertEqual(case.call_value, 0)
            self.assertIn(path, fixture_test.CALL_EXECUTION_FIXTURES)
        identity_constructor = fixture_test.RETURN_DATA_FIXTURE_ROOT / "create_callprecompile_returndatasize.json"
        self.assertIn(identity_constructor, fixture_test.IDENTITY_ACCOUNT_FIXTURES)

    def test_creation_constructor_storage_has_an_independent_post_state(self) -> None:
        for root in (fixture_test.RETURN_DATA_FIXTURE_ROOT, fixture_test.CREATE2_FIXTURE_ROOT):
            path = root / "returndatacopy_0_0_following_successful_create.json"
            case = fixture_test.load_state_case(path, "Cancun")
            initial_addresses = {account.address for account in case.accounts}
            created = [(address, storage) for address, storage in case.expected_account_storage
                       if address not in initial_addresses]
            self.assertEqual(len(created), 1)
            self.assertEqual(created[0][1], ((0, 1),))

    def test_constructor_context_cases_keep_account_checks(self) -> None:
        self.assertEqual(len(fixture_test.CONSTRUCTOR_CONTEXT_FIXTURES), 5)
        for fork in ("Cancun", "Prague"):
            cases = [(path, case) for path in fixture_test.CONSTRUCTOR_CONTEXT_FIXTURES
                     for case in fixture_test.load_state_cases(path, fork)]
            self.assertEqual(len(cases), 7)
            for path, case in cases:
                self.assertTrue(case.expected_accounts)
                self.assertTrue(case.code)
                self.assertEqual(case.call_value, 0)
                source = fixture_test.render_rocq(path, case)
                self.assertIn("CallRunner.run", source)
                self.assertIn("fixture_account_state_matches host", source)

    def test_creation_oracle_retains_deployed_code_and_nonce(self) -> None:
        for root in (fixture_test.RETURN_DATA_FIXTURE_ROOT, fixture_test.CREATE2_FIXTURE_ROOT):
            path = root / "returndatasize_following_successful_create.json"
            case = fixture_test.load_state_case(path, "Cancun")
            initial_addresses = {account.address for account in case.accounts}
            created = [account for account in case.expected_accounts
                       if account.address not in initial_addresses]
            self.assertEqual(len(created), 1)
            self.assertEqual(len(created[0].code), 32)
            self.assertEqual(created[0].code[-3:], (0x11, 0x22, 0x33))
            self.assertEqual(created[0].nonce, 1)
            self.assertEqual(case.call_value, 0)
            self.assertNotEqual(case.caller_address, case.coinbase)

    def test_creation_account_oracle_uses_fixture_post_state(self) -> None:
        for path in fixture_test.CREATE_FIXTURES:
            document = next(iter(json.loads(path.read_text()).values()))
            for index, case in enumerate(fixture_test.load_state_cases(path, "Cancun")):
                post = document["post"]["Cancun"][index]["state"]
                expected = {int(address, 16): account for address, account in post.items()}
                self.assertEqual(len(case.expected_accounts), len(expected))
                for account in case.expected_accounts:
                    source = expected[account.address]
                    self.assertEqual(account.nonce, int(source["nonce"], 16))
                    self.assertEqual(account.balance, int(source["balance"], 16))
                    self.assertEqual(account.code, tuple(bytes.fromhex(source["code"][2:])))

    def test_direct_cases_do_not_claim_transaction_account_checks(self) -> None:
        case = fixture_test.load_state_case(fixture_test.ADD11_FIXTURE, "Cancun")
        self.assertEqual(case.expected_accounts, ())

    def test_creation_oracle_cannot_be_silently_disabled(self) -> None:
        path = fixture_test.CREATE_FIXTURES[0]
        case = fixture_test.load_state_case(path, "Cancun")
        with self.assertRaises(fixture_test.FixtureError):
            fixture_test.render_rocq(path, replace(case, expected_accounts=()))
        source = fixture_test.render_rocq(path, case)
        self.assertIn("fixture_account_state_matches host", source)
        for name in ("missing_contract_rejected", "wrong_code_rejected",
                     "wrong_nonce_rejected", "wrong_balance_rejected",
                     "unexpected_created_account_rejected",
                     "unexpected_balance_only_account_rejected",
                     "unexpected_storage_only_account_rejected",
                     "fee_only_coinbase_may_be_absent", "empty_cleanup_not_required"):
            self.assertIn(f"Example {name}", source)

    def test_creation_account_checks_reject_transaction_effects(self) -> None:
        path = fixture_test.CREATE_FIXTURES[0]
        original = json.loads(path.read_text())
        for change in ("value", "sender_target", "sender_coinbase", "coded_sender"):
            document = json.loads(json.dumps(original))
            test = next(iter(document.values()))
            tx = test["transaction"]
            if change == "value":
                tx["value"] = ["0x01"] * len(tx["value"])
            elif change == "sender_target":
                tx["sender"] = tx["to"]
            elif change == "sender_coinbase":
                test["env"]["currentCoinbase"] = tx["sender"]
            else:
                sender = next(key for key in test["pre"]
                              if int(key, 16) == int(tx["sender"], 16))
                test["pre"][sender]["code"] = "0x00"
            with self.subTest(change=change), \
                 patch.object(Path, "read_text", return_value=json.dumps(document)), \
                 self.assertRaises(fixture_test.FixtureError):
                fixture_test.load_state_case(path, "Cancun")

    def test_creation_copy_failures_require_exact_bounds_error(self) -> None:
        failures = set(fixture_test.CREATE_FIXTURES) & fixture_test.RETURN_DATA_FAILURE_FIXTURES
        self.assertEqual(len(failures), 3)
        for path in failures:
            with self.subTest(path=path), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "CreateFailure.v"
                args = Namespace(fixture=[path], emit=output, fork="Cancun")
                with patch.object(fixture_test, "parse_args", return_value=args), \
                     patch("builtins.print"), \
                     patch.object(fixture_test, "run_coqc") as coqc:
                    coqc.return_value.returncode = 0
                    self.assertEqual(fixture_test.main(), 0)
                source = output.read_text()
            self.assertIn("CallRunner.run", source)
            self.assertIn("InstructionResult.OutOfOffset => true", source)
            self.assertIn("run_fixture_out_of_offset =", source)
            self.assertNotIn("\n  run_fixture =", source)

    def test_call_context_cases_have_executable_targets_and_zero_entry_value(self) -> None:
        cases = [fixture_test.load_state_case(path, "Cancun")
                 for path in fixture_test.CALL_CONTEXT_FIXTURES]
        self.assertEqual(len(cases), 10)
        for case in cases:
            self.assertTrue(case.code)
            self.assertEqual(case.call_value, 0)
        excluded = fixture_test.RETURN_DATA_FIXTURE_ROOT / "returndatacopy_after_failing_delegatecall.json"
        self.assertNotIn(excluded, fixture_test.DEFAULT_FIXTURES)

    def test_static_calls_execute_code_without_entry_transfer(self) -> None:
        self.assertEqual(len(fixture_test.STATIC_CALL_FIXTURES), 6)
        for path in fixture_test.STATIC_CALL_FIXTURES:
            case = fixture_test.load_state_case(path, "Cancun")
            self.assertTrue(case.code)
            self.assertEqual(case.call_value, 0)
            self.assertIn(path, fixture_test.CALL_EXECUTION_FIXTURES)
            self.assertIn("CallRunner.run", fixture_test.render_rocq(path, case))

    def test_static_copy_failure_requires_exact_bounds_error(self) -> None:
        path = fixture_test.RETURN_DATA_FIXTURE_ROOT / "returndatacopy_after_failing_staticcall.json"
        self.assertIn(path, fixture_test.RETURN_DATA_FAILURE_FIXTURES)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "StaticFailure.v"
            args = Namespace(fixture=[path], emit=output, fork="Cancun")
            with patch.object(fixture_test, "parse_args", return_value=args), \
                 patch("builtins.print"), \
                 patch.object(fixture_test, "run_coqc") as coqc:
                coqc.return_value.returncode = 0
                self.assertEqual(fixture_test.main(), 0)
            source = output.read_text()
        self.assertIn("InstructionResult.OutOfOffset => true", source)
        self.assertIn("run_fixture_out_of_offset =", source)
        self.assertNotIn("\n  run_fixture =", source)

    def test_static_return_checks_exact_output(self) -> None:
        path = fixture_test.STATIC_RETURN_FIXTURE
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "StaticReturn.v"
            args = Namespace(fixture=[path], emit=output, fork="Cancun")
            with patch.object(fixture_test, "parse_args", return_value=args), \
                 patch("builtins.print"), \
                 patch.object(fixture_test, "run_coqc") as coqc:
                coqc.return_value.returncode = 0
                self.assertEqual(fixture_test.main(), 0)
            source = output.read_text()
        self.assertIn("fixture_return_output_matches [0; 21]", source)
        self.assertIn("fixture_return_output_matches [0; 21; 0]) = None", source)
        self.assertIn("fixture_return_output_matches [0]) = None", source)
        self.assertIn("fixture_return_output_matches [1; 21]) = None", source)
        self.assertNotIn("\n  run_fixture =", source)

    def test_delegatecall_oracle_checks_parent_storage_and_sender(self) -> None:
        path = next(path for path in fixture_test.CALL_CONTEXT_FIXTURES
                    if path.name == "delegatecallSenderCheck.json")
        case = fixture_test.load_state_case(path, "Cancun")
        self.assertEqual(case.expected_storage, ((0, 1), (1, case.caller_address)))
        self.assertEqual(dict(case.expected_account_storage)[case.target_address],
                         case.expected_storage)
        for account in case.accounts:
            if account.address != case.target_address and account.code:
                self.assertEqual(dict(case.expected_account_storage)[account.address], ())

    def test_target_storage_oracle_normalizes_order_without_dropping_keys(self) -> None:
        path = next(path for path in fixture_test.CALL_CONTEXT_FIXTURES
                    if path.name == "delegatecallBasic.json")
        case = fixture_test.load_state_case(path, "Cancun")
        self.assertEqual(case.expected_storage, ((0, 1), (1, 1)))
        source = fixture_test.render_rocq(path, case)
        self.assertIn("fixture_normalize_storage account.(StatefulHost.Account.storage)", source)
        self.assertIn("List.fold_right fixture_storage_insert []", source)
        self.assertIn("Some [(0, 1); (1, 1)]", source)
        for name in ("reordered_storage_matches", "wrong_value_rejected",
                     "extra_key_rejected", "missing_key_rejected", "duplicate_key_rejected"):
            self.assertIn(f"Example {name}", source)

    def test_failing_callcode_copy_selects_exact_exception_in_main(self) -> None:
        path = fixture_test.RETURN_DATA_FIXTURE_ROOT / "returndatacopy_after_failing_callcode.json"
        self.assertIn(path, fixture_test.CALL_EXECUTION_FIXTURES)
        self.assertIn(path, fixture_test.RETURN_DATA_FAILURE_FIXTURES)
        case = fixture_test.load_state_case(path, "Cancun")
        self.assertEqual(case.expected_storage, ((0, 0xffffffffffff),))
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "CallcodeFailure.v"
            args = Namespace(fixture=[path], emit=output, fork="Cancun")
            with patch.object(fixture_test, "parse_args", return_value=args), \
                 patch("builtins.print"), \
                 patch.object(fixture_test, "run_coqc") as coqc:
                coqc.return_value.returncode = 0
                self.assertEqual(fixture_test.main(), 0)
            source = output.read_text()
        self.assertIn("CallRunner.run", source)
        self.assertIn("InstructionResult.OutOfOffset => true", source)
        self.assertIn("run_fixture_out_of_offset =", source)
        self.assertNotIn("\n  run_fixture =", source)

    def test_call_post_storage_is_not_taken_from_pre_state(self) -> None:
        path = fixture_test.CALL_EXECUTION_FIXTURES[0]
        case = fixture_test.load_state_case(path, "Cancun")
        expected = dict(case.expected_account_storage)[case.target_address]
        self.assertEqual(expected, case.expected_storage)
        initial = next(a.storage for a in case.accounts if a.address == case.target_address)
        self.assertNotEqual(initial, expected)

    def test_emit_without_fixture_uses_original_smoke_test(self) -> None:
        args = Namespace(fixture=None, emit=Path("StateFixtureTest.v"), fork="Cancun")

        self.assertEqual(
            fixture_test.select_fixtures(args),
            (fixture_test.ADD11_FIXTURE,),
        )

    def test_default_fixture_batch_covers_supported_state_programs(self) -> None:
        args = Namespace(fixture=None, emit=None, fork="Cancun")
        fixtures = fixture_test.select_fixtures(args)
        names = [path.name for path in fixtures]

        self.assertEqual(fixtures, fixture_test.DEFAULT_FIXTURES)
        self.assertEqual(len(names), 218)
        self.assertEqual(sum(len(fixture_test.load_state_cases(path, "Cancun"))
                             for path in fixtures), 270)
        self.assertIn("RevertOpcode.json", names)
        self.assertIn("RevertOnEmptyStack.json", names)
        self.assertIn("returndatacopy_following_call.json", names)
        self.assertIn("returndatacopy_following_revert.json", names)
        self.assertIn("call_then_call_value_fail_then_returndatasize.json", names)
        self.assertEqual(names[0], "add11.json")
        self.assertIn("accessListExample.json", names)
        self.assertIn("extCodeCopyBounds.json", names)
        self.assertIn("RawExtCodeCopyMemoryGas.json", names)
        self.assertIn("RawExtCodeSizeGas.json", names)
        self.assertIn("extcodecopy_dejavu.json", names)
        self.assertIn("extCodeHashSelf.json", names)
        self.assertIn("extCodeHashDynamicArgument.json", names)
        self.assertIn("extCodeHashPrecompiles.json", names)
        self.assertIn("shl11.json", names)
        self.assertIn("shr_2^255_257.json", names)
        self.assertIn("sar_2^255_256.json", names)
        self.assertIn("shiftCombinations.json", names)
        self.assertIn("shiftSignedCombinations.json", names)
        self.assertIn("chainId.json", names)
        self.assertIn("chainIdGasCost.json", names)
        self.assertIn("sloadGasCost.json", names)
        self.assertIn("selfBalance.json", names)
        self.assertIn("selfBalanceGasCost.json", names)
        self.assertIn("selfBalanceEqualsBalance.json", names)
        self.assertIn("sstoreGas.json", names)
        self.assertIn("RawBalanceGas.json", names)
        self.assertIn("mload8bitBound.json", names)
        self.assertIn("mload16bitBound.json", names)
        self.assertIn("mem0b_singleByte.json", names)
        self.assertIn("mem31b_singleByte.json", names)
        self.assertIn("mem32b_singleByte.json", names)
        self.assertIn("mem33b_singleByte.json", names)
        self.assertIn("calldatacopy_dejavu.json", names)
        self.assertIn("calldatacopy_dejavu2.json", names)
        self.assertIn("codecopy_dejavu.json", names)
        self.assertIn("codecopy_dejavu2.json", names)
        self.assertIn("randomStatetest217.json", names)
        self.assertIn("randomStatetest301.json", names)
        self.assertIn("randomStatetest586.json", names)
        self.assertIn("callValue.json", names)
        self.assertIn("TestNameRegistrator.json", names)

    def test_memory_copy_failure_requires_out_of_gas(self) -> None:
        for path in fixture_test.MEMORY_COPY_FAILURE_FIXTURES:
            case = fixture_test.load_state_case(path, "Cancun")
            source = fixture_test.render_rocq(path, case, "MemoryOOG")
            self.assertIn("run_fixture_memory_out_of_gas =", source)
            self.assertIn("InstructionResult.MemoryOOG => true", source)
            self.assertEqual(case.expected_storage, ())

    def test_external_code_cases_and_gas_expectations(self) -> None:
        cases = [case for path in fixture_test.EXTERNAL_CODE_FIXTURES
                 for case in fixture_test.load_state_cases(path, "Cancun")]
        self.assertEqual(len(cases), 7)
        self.assertEqual([case.expected_storage for case in cases[:3]],
                         [((1, 2616),), ((1, 2629),), ((1, 4948),)])
        self.assertEqual(len(cases[5].expected_storage), 1)
        self.assertNotEqual(cases[5].expected_storage[0][1], 0)
        self.assertIn(fixture_test.EXTERNAL_CODE_FIXTURES[-1],
                      fixture_test.MEMORY_COPY_FAILURE_FIXTURES)

    def test_code_hash_fixture_cases(self) -> None:
        groups = [fixture_test.load_state_cases(path, "Cancun")
                  for path in fixture_test.CODE_HASH_FIXTURES]
        self.assertEqual([len(cases) for cases in groups], [1, 5, 9])
        case = groups[0][0]
        target = next(account for account in case.accounts
                      if account.address == case.target_address)
        expected_hash = dict(case.expected_storage)[0]
        self.assertNotEqual(expected_hash, 0)
        self.assertIn(f"StatefulHost.Account.code_hash := {expected_hash};",
                      fixture_test.render_account(0, target))

    def test_code_hash_gas_and_cross_instruction_cases(self) -> None:
        cases = fixture_test.make_code_hash_gas_cases("Cancun")
        self.assertEqual(len(cases), 5)
        self.assertEqual([case.expected_storage for case in cases],
                         [((1, 2616),)] + [((1, 116),)] * 4)
        self.assertEqual(cases[0].code[6], 0x3F)
        self.assertEqual(cases[0].code, cases[1].code)
        self.assertEqual(cases[3].code[:4], (0x60, 42, 0x3B, 0x50))
        self.assertEqual(cases[4].code[8], 0x3C)
        self.assertEqual(cases[3].access_list, ())
        self.assertEqual(cases[4].access_list, ())

    def test_account_hash_uses_keccak_not_sha3(self) -> None:
        for code, digest in (
            (b"", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
            (b"abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
        ):
            with self.subTest(code=code):
                account = fixture_test.Account(42, 0, 0, tuple(code), ())
                source = fixture_test.render_account(0, account)
                self.assertIn(f"StatefulHost.Account.code_hash := {int(digest, 16)};",
                              source)

    def test_initial_warm_accounts_follow_fork(self) -> None:
        case = replace(
            fixture_test.load_state_case(fixture_test.ADD11_FIXTURE, "Cancun"),
            caller_address=100, target_address=200, coinbase=300,
        )
        self.assertEqual(
            fixture_test.initial_warm_accounts(case),
            (100, 200, 300, *range(1, 11)),
        )
        prague = replace(case, fork="Prague", spec_id="PRAGUE")
        self.assertEqual(
            fixture_test.initial_warm_accounts(prague),
            (100, 200, 300, *range(1, 18)),
        )
        duplicates = replace(case, caller_address=1, target_address=1, coinbase=1)
        self.assertEqual(fixture_test.initial_warm_accounts(duplicates), tuple(range(1, 11)))
        source = fixture_test.render_rocq(fixture_test.ADD11_FIXTURE, case)
        self.assertIn("List.fold_left StatefulHost.warm_account [100; 200; 300; 1;", source)

    def test_access_list_matches_selected_data_index(self) -> None:
        path = fixture_test.ACCESS_LIST_FIXTURE
        first = fixture_test.load_state_case(path, "Cancun", 0)
        second = fixture_test.load_state_case(path, "Cancun", 1)
        self.assertEqual(first.calldata, second.calldata)
        self.assertEqual(first.access_list[0], (first.target_address, (0, 1)))
        self.assertEqual(first.access_list[1:], second.access_list)
        self.assertNotIn(first.target_address, dict(second.access_list))
        source = fixture_test.render_rocq(path, first)
        self.assertIn("StatefulHost.warm_access_list", source)
        self.assertIn(f"[({first.target_address}, [0; 1]);", source)

    def test_access_list_gas_cases_only_change_warming(self) -> None:
        cold, warm, duplicate = fixture_test.make_access_list_gas_cases("Cancun")
        self.assertEqual(cold.code, warm.code)
        self.assertEqual(warm.code, duplicate.code)
        self.assertEqual(cold.access_list, ())
        self.assertEqual(warm.access_list, ((42, ()),))
        self.assertEqual(duplicate.access_list, warm.access_list * 2)
        self.assertNotIn(42, fixture_test.initial_warm_accounts(cold))
        self.assertEqual(cold.expected_storage, ((1, 2616),))
        self.assertEqual(warm.expected_storage, ((1, 116),))
        self.assertEqual(duplicate.expected_storage, warm.expected_storage)

    def test_access_list_empty_null_and_duplicates(self) -> None:
        self.assertEqual(fixture_test.parse_access_list(None), ())
        self.assertEqual(fixture_test.parse_access_list([]), ())
        entry = {"address": "0x" + "00" * 19 + "2a",
                 "storageKeys": ["0x" + "00" * 31 + "07"] * 2}
        self.assertEqual(fixture_test.parse_access_list([entry, entry]),
                         ((42, (7, 7)), (42, (7, 7))))

    def test_malformed_access_lists_are_rejected(self) -> None:
        address = "0x" + "00" * 20
        key = "0x" + "00" * 32
        invalid = [False, {}, [None], [{}],
                   [{"address": address, "storageKeys": None}],
                   [{"address": address, "storageKeys": key}]]
        for bad_address in (None, 42, "0x1", "0x" + "00" * 21,
                            "0x" + "gg" * 20, "-" + address):
            invalid.append([{"address": bad_address, "storageKeys": []}])
        for bad_key in (None, 7, "0x7", "0x" + "00" * 33,
                        "0x" + "gg" * 32, "-" + key):
            invalid.append([{"address": address, "storageKeys": [bad_key]}])
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(fixture_test.FixtureError):
                fixture_test.parse_access_list(value)

    def test_access_list_array_length_must_match_data(self) -> None:
        document = json.loads(fixture_test.ADD11_FIXTURE.read_text())
        test = next(iter(document.values()))
        test["transaction"]["accessLists"] = []
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "access_list.json"
            path.write_text(json.dumps(document))
            with self.assertRaisesRegex(fixture_test.FixtureError, "must match transaction.data length"):
                fixture_test.load_state_case(path, "Cancun")
            test["transaction"]["accessLists"] = [[]]
            path.write_text(json.dumps(document))
            fixture_test.load_state_case(path, "Cancun")

    def test_memory_return_requires_exact_output(self) -> None:
        path = fixture_test.MEMORY_RETURN_FIXTURE
        case = fixture_test.load_state_case(path, "Cancun")
        self.assertEqual(case.code, (54, 96, 0, 96, 0, 55, 89, 96, 0, 243, 0))
        self.assertEqual(len(case.calldata), 80)
        output = case.calldata + (0,) * 16
        source = fixture_test.render_rocq(path, case, "Return", output)
        self.assertIn("run_fixture_return =", source)
        self.assertIn("List.list_eq_dec Z.eq_dec", source)
        for incorrect in (output + (0,), output[:-1], (output[0] ^ 1,) + output[1:]):
            values = "[" + "; ".join(str(value) for value in incorrect) + "]"
            self.assertIn(
                f"Goal run_fixture_with_action (fixture_return_output_matches {values}) = None.",
                source,
            )
        with self.assertRaises(ValueError):
            fixture_test.render_rocq(path, case, "Return")
        with self.assertRaises(ValueError):
            fixture_test.render_rocq(path, case, expected_output=output)

    def test_empty_output_has_a_rejection_check(self) -> None:
        path = fixture_test.MEMORY_RETURN_FIXTURE
        case = fixture_test.load_state_case(path, "Cancun")
        source = fixture_test.render_rocq(path, case, "Return", ())
        self.assertIn(
            "Goal run_fixture_with_action (fixture_return_output_matches [0]) = None.",
            source,
        )
        self.assertEqual(source.count("Goal run_fixture_with_action"), 1)
        ordinary_source = fixture_test.render_rocq(path, case)
        self.assertNotIn("Goal run_fixture_with_action", ordinary_source)

    def test_nonempty_calldata_copy_cases(self) -> None:
        cases = [
            fixture_test.load_state_case(path, "Cancun")
            for path in fixture_test.CALLDATA_COPY_FIXTURES
        ]
        self.assertEqual([len(case.calldata) for case in cases], [232, 278, 265])
        self.assertEqual(
            [case.expected_storage[0][1] for case in cases],
            [50000, 0x737AA092F1975664518A55, 50000],
        )

    def test_load_call_input_fixtures(self) -> None:
        call_value = fixture_test.load_state_case(
            fixture_test.CALL_INPUT_FIXTURES[0],
            "Cancun",
        )
        name_registrator = fixture_test.load_state_case(
            fixture_test.CALL_INPUT_FIXTURES[1],
            "Cancun",
        )
        self.assertEqual(call_value.code, (0x34, 0x60, 0x00, 0x55, 0x00))
        self.assertEqual(call_value.call_value, 100000)
        self.assertEqual(call_value.expected_storage, ((0, 100000),))
        self.assertEqual(len(name_registrator.calldata), 64)
        self.assertEqual(name_registrator.calldata[31], 0xFA)
        self.assertEqual(name_registrator.calldata[63], 0xFA)
        self.assertEqual(
            name_registrator.expected_storage,
            ((2**256 - 6, 2**256 - 6),),
        )

    def test_return_data_cases_cover_every_input(self) -> None:
        cases = [
            fixture_test.load_state_cases(path, "Cancun")
            for path in fixture_test.RETURN_DATA_FIXTURES
        ]
        self.assertEqual([len(group) for group in cases], [1, 2, 1, 3, 1])
        self.assertEqual(
            [case.calldata for case in cases[1]], [(), (0x99, 0x29, 0x19, 0xAA)]
        )
        self.assertEqual([case.calldata[-1] for case in cases[3]], [100, 99, 101])

    def test_return_data_failure_requires_out_of_offset(self) -> None:
        path = fixture_test.RETURN_DATA_FIXTURES[2]
        case = fixture_test.load_state_case(path, "Cancun")
        source = fixture_test.render_rocq(path, case, "OutOfOffset")
        self.assertIn("InstructionResult.OutOfOffset => true", source)
        self.assertIn("run_fixture_out_of_offset =", source)
        self.assertEqual(case.expected_storage, ((0, 1),))

    def test_return_data_post_index_is_checked(self) -> None:
        path = fixture_test.RETURN_DATA_FIXTURES[3]
        with self.assertRaises(fixture_test.FixtureError):
            fixture_test.load_state_case(path, "Cancun")
        for index in (-1, 3):
            with self.assertRaises(fixture_test.FixtureError):
                fixture_test.load_state_case(path, "Cancun", index)

    def test_load_add11_uses_fixture_execution_data(self) -> None:
        case = fixture_test.load_state_case(
            fixture_test.DEFAULT_FIXTURE,
            "Cancun",
        )

        self.assertEqual(case.name, "add11")
        self.assertEqual(case.spec_id, "CANCUN")
        self.assertEqual(
            case.code,
            (0x60, 0x01, 0x60, 0x01, 0x01, 0x60, 0x00, 0x55, 0x00),
        )
        self.assertEqual(case.expected_storage, ((0, 2),))
        self.assertEqual(case.chain_id, 1)
        self.assertEqual(case.gas_price, 10)
        self.assertEqual(case.transaction_gas_limit, 400000)
        self.assertEqual(case.transaction_nonce, 0)
        self.assertEqual(case.call_value, 100000)
        self.assertEqual(case.calldata, ())
        self.assertEqual(case.block_number, 1)
        self.assertEqual(case.timestamp, 1000)
        self.assertEqual(case.base_fee, 10)

    def test_load_add11_preserves_fixture_addresses(self) -> None:
        case = fixture_test.load_state_case(
            fixture_test.DEFAULT_FIXTURE,
            "Cancun",
        )

        addresses = [account.address for account in case.accounts]
        self.assertNotIn(0, addresses)
        self.assertIn(case.target_address, addresses)
        self.assertIn(case.caller_address, addresses)

    def test_exceptional_halt_case_rolls_back_storage_before_trailing_stop(self) -> None:
        case = fixture_test.make_exceptional_halt_case("Cancun")

        self.assertEqual(case.transaction_gas_limit, 2400)
        self.assertEqual(case.code, (0x60, 0x01, 0x60, 0x00, 0x55, 0x00))
        self.assertEqual(case.expected_storage, ())
        target = next(
            account
            for account in case.accounts
            if account.address == case.target_address
        )
        self.assertEqual(target.code, case.code)

    def test_revert_checks_output_and_restored_storage(self) -> None:
        cases = fixture_test.load_state_cases(fixture_test.REVERT_FIXTURE, "Cancun")
        self.assertEqual(len(cases), 4)
        for case in cases:
            source = fixture_test.render_rocq(fixture_test.REVERT_FIXTURE, case, "Revert", (0,))
            self.assertEqual(case.expected_storage, ())
            self.assertIn("InstructionResult.Revert =>", source)
            self.assertIn("StatefulFrame.finish", source)
            self.assertIn("fixture_return_output_matches [1]) = None", source)

    def test_render_rocq_registers_concrete_host(self) -> None:
        case = fixture_test.make_exceptional_halt_case("Cancun")
        source = fixture_test.render_rocq(fixture_test.DEFAULT_FIXTURE, case)

        for instance in ("IsLink", "HostTypesAreLinks", "HostForRevmHost"):
            self.assertIn(
                f"#[local] Existing Instance StatefulHost.{instance}.",
                source,
            )
        self.assertIn("(run_host := run_Host_for_StatefulHost)", source)

    def test_render_rocq_contains_fixture_state_and_bytecode(self) -> None:
        case = fixture_test.load_state_case(
            fixture_test.DEFAULT_FIXTURE,
            "Cancun",
        )
        source = fixture_test.render_rocq(fixture_test.DEFAULT_FIXTURE, case)

        self.assertIn("SpecId.CANCUN", source)
        self.assertIn("StatefulHost.Environment.Block.timestamp := 1000", source)
        self.assertIn(
            f"StatefulHost.Environment.Call.caller := {case.caller_address}",
            source,
        )
        self.assertIn(
            f"Address.value :=\n         {case.target_address}",
            source,
        )
        self.assertIn(
            f"Address.value :=\n         {case.caller_address}",
            source,
        )
        self.assertIn(
            f"Uint.value := {case.call_value}",
            source,
        )
        self.assertIn("(96 : u8); (1 : u8); (96 : u8); (1 : u8)", source)
        self.assertIn(
            "Some [(0, 2)]",
            source,
        )
        self.assertIn("run_plain_stateful_fuel\n      100000", source)
        self.assertIn(
            "InterpreterAction.NewFrame FrameInput.Empty => true",
            source,
        )
        self.assertIn("InstructionResult.Stop => true", source)
        self.assertIn(
            "run_fixture_with_action fixture_terminated_successfully",
            source,
        )
        self.assertIn(
            "match bytecode.(Bytecode.action) with\n"
            "  | None => bytecode_is_not_end bytecode\n"
            "  | Some _ => false",
            source,
        )
        self.assertIn(
            "InterpreterTypes.I\n      fixture_should_continue",
            source,
        )
        self.assertIn(
            f"Gas.remaining := {{| Integer.value := {case.transaction_gas_limit} |}}",
            source,
        )

    def test_render_rocq_can_observe_exceptional_termination(self) -> None:
        case = fixture_test.make_exceptional_halt_case("Cancun")
        source = fixture_test.render_rocq(
            fixture_test.ADD11_FIXTURE,
            case,
            expected_instruction_result="OutOfGas",
        )

        self.assertIn(
            "Goal\n"
            "  run_fixture_out_of_gas =\n"
            "  Some [].",
            source,
        )
        self.assertIn(
            "fun entry => negb (Z.eqb (snd entry) 0)",
            source,
        )

    def test_load_shift_fixture_uses_empty_post_storage_for_zero(self) -> None:
        fixture = fixture_test.SHIFT_FIXTURE_ROOT / "shl01.json"
        case = fixture_test.load_state_case(fixture, "Cancun")

        self.assertEqual(case.expected_storage, ())

    def test_load_chain_id_fixtures_uses_chain_id_and_expected_storage(self) -> None:
        expectations = {
            "chainId.json": (
                (0x46, 0x60, 0x01, 0x55, 0x00),
                ((1, 1),),
            ),
            "chainIdGasCost.json": (
                (
                    0x5A, 0x46, 0x5A, 0x90, 0x50, 0x90, 0x03,
                    0x60, 0x02, 0x90, 0x03, 0x60, 0x01, 0x55, 0x00,
                ),
                ((1, 2),),
            ),
        }

        for name, (code, expected_storage) in expectations.items():
            with self.subTest(name=name):
                case = fixture_test.load_state_case(
                    fixture_test.CHAIN_ID_FIXTURE_ROOT / name,
                    "Cancun",
                )
                self.assertEqual(case.chain_id, 1)
                self.assertEqual(case.code, code)
                self.assertEqual(case.expected_storage, expected_storage)

    def test_load_sload_gas_cost_fixture(self) -> None:
        case = fixture_test.load_state_case(
            fixture_test.SLOAD_FIXTURE_ROOT / "sloadGasCost.json",
            "Cancun",
        )

        self.assertEqual(
            case.code,
            (
                0x5A, 0x80, 0x54, 0x5A, 0x90, 0x50, 0x90, 0x03,
                0x60, 0x05, 0x90, 0x03, 0x60, 0x01, 0x55, 0x00,
            ),
        )
        self.assertEqual(case.expected_storage, ((1, 0x834),))

    def test_load_direct_self_balance_fixtures(self) -> None:
        expectations = {
            "selfBalance.json": (
                (0x47, 0x60, 0x01, 0x55, 0x00),
                ((1, 500),),
            ),
            "selfBalanceEqualsBalance.json": (
                (0x30, 0x31, 0x47, 0x14, 0x60, 0x01, 0x55, 0x00),
                ((1, 1),),
            ),
            "selfBalanceGasCost.json": (
                (
                    0x5A, 0x47, 0x5A, 0x90, 0x50, 0x90, 0x03,
                    0x60, 0x02, 0x90, 0x03, 0x60, 0x01, 0x55, 0x00,
                ),
                ((1, 5),),
            ),
        }

        for name, (code, expected_storage) in expectations.items():
            with self.subTest(name=name):
                case = fixture_test.load_state_case(
                    fixture_test.SELF_BALANCE_FIXTURE_ROOT / name,
                    "Cancun",
                )
                self.assertEqual(case.code, code)
                self.assertEqual(case.expected_storage, expected_storage)

    def test_balance_gas_fixture_reads_pre_warmed_sender(self) -> None:
        case = fixture_test.load_state_case(fixture_test.BALANCE_GAS_FIXTURE, "Cancun")
        self.assertEqual(case.code[4], 0x73)
        self.assertEqual(int.from_bytes(bytes(case.code[5:25]), "big"), case.caller_address)
        self.assertEqual(case.code[25], 0x31)
        self.assertEqual(case.call_value, 0)
        self.assertEqual(case.expected_storage, ((1, 116),))
        self.assertIn(case.caller_address, fixture_test.initial_warm_accounts(case))

    def test_load_sstore_gas_fixture(self) -> None:
        case = fixture_test.load_state_case(
            fixture_test.SSTORE_GAS_FIXTURE,
            "Cancun",
        )

        self.assertEqual(
            case.expected_storage,
            (
                (0x1000, 5000),
                (0x1001, 100),
                (0x1002, 100),
                (0x1003, 100),
                (0x1004, 100),
                (0x1005, 5000),
                (0x1006, 22100),
                (0x1007, 2200),
                (0x1008, 20000),
            ),
        )

    def test_load_memory_fixtures(self) -> None:
        expectations = {
            "mload8bitBound.json": (
                (0x61, 0x01, 0x00, 0x51, 0x60, 0x01, 0x55, 0x00),
                (),
            ),
            "mload16bitBound.json": (
                (0x62, 0x01, 0x00, 0x00, 0x51, 0x60, 0x01, 0x55, 0x00),
                (),
            ),
            "mem0b_singleByte.json": (
                (0x60, 0x2A, 0x60, 0x00, 0x53, 0x59, 0x60, 0x00, 0x55, 0x00),
                ((0, 0x20),),
            ),
            "mem31b_singleByte.json": (
                (0x60, 0x2A, 0x60, 0x1E, 0x53, 0x59, 0x60, 0x00, 0x55, 0x00),
                ((0, 0x20),),
            ),
            "mem32b_singleByte.json": (
                (0x60, 0x2A, 0x60, 0x1F, 0x53, 0x59, 0x60, 0x00, 0x55, 0x00),
                ((0, 0x20),),
            ),
            "mem33b_singleByte.json": (
                (0x60, 0x2A, 0x60, 0x20, 0x53, 0x59, 0x60, 0x00, 0x55, 0x00),
                ((0, 0x40),),
            ),
        }

        for name, (code, expected_storage) in expectations.items():
            with self.subTest(name=name):
                case = fixture_test.load_state_case(
                    fixture_test.MEMORY_FIXTURE_ROOT / name,
                    "Cancun",
                )
                self.assertEqual(case.code, code)
                self.assertEqual(case.expected_storage, expected_storage)

    def test_render_rocq_contains_nonempty_calldata(self) -> None:
        fixture = json.loads(fixture_test.DEFAULT_FIXTURE.read_text())
        fixture["add11"]["transaction"]["data"][0] = "0xdeadbeef"

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "add11.json"
            path.write_text(json.dumps(fixture))
            case = fixture_test.load_state_case(path, "Cancun")
            source = fixture_test.render_rocq(path, case)

        self.assertEqual(case.calldata, (0xDE, 0xAD, 0xBE, 0xEF))
        self.assertIn(
            "bytes.Bytes.value :=\n"
            "             [(222 : u8); (173 : u8); (190 : u8); (239 : u8)]",
            source,
        )

    def test_load_state_case_rejects_invalid_post_index(self) -> None:
        fixture = json.loads(fixture_test.DEFAULT_FIXTURE.read_text())
        fixture["add11"]["post"]["Cancun"][0]["indexes"]["gas"] = 3

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "add11.json"
            path.write_text(json.dumps(fixture))
            with self.assertRaisesRegex(
                fixture_test.FixtureError,
                "invalid gasLimit index",
            ):
                fixture_test.load_state_case(path, "Cancun")


if __name__ == "__main__":
    unittest.main()
