#!/usr/bin/env python3

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import patch


SCRIPT_PATH = Path(__file__).with_name("revm_fixture_test.py")
SPEC = importlib.util.spec_from_file_location("revm_fixture_test", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
fixture_test = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = fixture_test
SPEC.loader.exec_module(fixture_test)


class RevmFixtureTestTest(unittest.TestCase):
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

    def test_decode_program(self) -> None:
        self.assertEqual(
            fixture_test.decode_program(
                "0x600460070160005500",
                fixture_test.INSTRUCTIONS["add"],
            ),
            (4, 7),
        )

    def test_decode_program_rejects_another_opcode(self) -> None:
        with self.assertRaisesRegex(fixture_test.FixtureError, "expected ADD"):
            fixture_test.decode_program(
                "0x600460070260005500",
                fixture_test.INSTRUCTIONS["add"],
            )

    def test_decode_program_disambiguates_sub_opcode(self) -> None:
        self.assertEqual(
            fixture_test.decode_program(
                "0x600160000360005500",
                fixture_test.INSTRUCTIONS["sub"],
            ),
            (1, 0),
        )

    def test_load_add_cases_uses_fixture_inputs_and_post_storage(self) -> None:
        fixture = {
            "add": {
                "_info": {"labels": {"0": "four_plus_seven"}},
                "pre": {
                    "0x1000": {
                        "code": "0x600460070160005500",
                        "storage": {},
                    },
                    "0xcccc": {"code": "0x00", "storage": {}},
                },
                "transaction": {"data": ["0x693c6139" + "00" * 32]},
                "post": {
                    "Cancun": [
                        {
                            "indexes": {"data": 0},
                            "state": {
                                "0x1000": {"storage": {"0x00": "0x0b"}}
                            },
                        }
                    ]
                },
            }
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "add.json"
            path.write_text(json.dumps(fixture))
            cases = fixture_test.load_instruction_cases(path, "Cancun")

        self.assertEqual(
            cases,
            [
                fixture_test.InstructionCase(
                    instruction=fixture_test.INSTRUCTIONS["add"],
                    name="four_plus_seven",
                    operands=(4, 7),
                    expected=11,
                )
            ],
        )

    def test_render_rocq_uses_revm_add_simulation(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.REPO_ROOT / "tests/testdata/add.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["add"],
                    "example",
                    (4, 7),
                    11,
                )
            ],
        )

        self.assertIn("arithmetic.add", source)
        self.assertIn("let result := add interpreter", source)
        self.assertIn("Uint.value := 11", source)
        self.assertIn("vm_compute", source)

    def test_render_rocq_keeps_sub_operand_order(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.REPO_ROOT / "tests/testdata/sub.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["sub"],
                    "twenty_three_minus_one",
                    (1, 23),
                    22,
                )
            ],
        )

        self.assertLess(
            source.index("Uint.value := 23"),
            source.index("Uint.value := 1"),
        )
        self.assertIn("let result := sub interpreter", source)

    def test_load_div_cases_includes_division_by_zero(self) -> None:
        cases = fixture_test.load_instruction_cases(
            fixture_test.ARITHMETIC_FIXTURE_ROOT / "div.json",
            "Cancun",
        )

        self.assertIn("div_2_0", [case.name for case in cases])
        self.assertTrue(
            any(case.operands == (0, 2) for case in cases)
        )

    def test_render_rocq_maps_mod_fixture_to_revm_rem(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.ARITHMETIC_FIXTURE_ROOT / "mod.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["mod"],
                    "two_mod_three",
                    (3, 2),
                    2,
                )
            ],
        )

        self.assertIn("arithmetic.rem", source)
        self.assertIn("let result := rem interpreter", source)

    def test_official_fixture_case_counts(self) -> None:
        expected_counts = {
            "add": 5,
            "mul": 7,
            "sub": 5,
            "div": 7,
            "sdiv": 14,
            "mod": 5,
            "smod": 5,
            "addmod": 12,
            "mulmod": 10,
            "exp": 11,
            "signextend": 15,
            "lt": 4,
            "gt": 4,
            "slt": 4,
            "sgt": 4,
            "eq": 3,
            "iszero": 3,
            "and": 5,
            "or": 6,
            "xor": 6,
            "not": 6,
        }

        for name, expected_count in expected_counts.items():
            instruction = fixture_test.INSTRUCTIONS[name]
            cases = fixture_test.load_instruction_cases(
                instruction.fixture_root / f"{name}.json",
                "Cancun",
            )
            self.assertEqual(len(cases), expected_count, name)

    def test_decode_addmod_program(self) -> None:
        self.assertEqual(
            fixture_test.decode_program(
                "0x6002600260010860005500",
                fixture_test.INSTRUCTIONS["addmod"],
            ),
            (2, 2, 1),
        )

    def test_decode_sdiv_program_constructs_negative_operands(self) -> None:
        self.assertEqual(
            fixture_test.decode_program(
                "0x600460000360026000030560005500",
                fixture_test.INSTRUCTIONS["sdiv"],
            ),
            (
                fixture_test.U256_MODULUS - 4,
                fixture_test.U256_MODULUS - 2,
            ),
        )

    def test_sdiv_fixture_ignores_stray_lower_program_address(self) -> None:
        cases = fixture_test.load_instruction_cases(
            fixture_test.ARITHMETIC_FIXTURE_ROOT / "sdiv.json",
            "Cancun",
        )

        first_case = next(case for case in cases if case.name == "sdiv_1_neg1")
        self.assertEqual(
            first_case.operands,
            (fixture_test.U256_MODULUS - 1, 1),
        )
        self.assertEqual(first_case.expected, fixture_test.U256_MODULUS - 1)

    def test_render_rocq_reverses_ternary_operands(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.ARITHMETIC_FIXTURE_ROOT / "addmod.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["addmod"],
                    "four_plus_one_mod_zero",
                    (0, 1, 4),
                    0,
                )
            ],
        )

        self.assertLess(
            source.index("Uint.value := 4"),
            source.index("Uint.value := 1"),
        )
        self.assertLess(
            source.index("Uint.value := 1"),
            source.index("Uint.value := 0"),
        )
        self.assertIn("let result := addmod interpreter", source)

    def test_render_rocq_passes_interpreter_types_to_exp(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.ARITHMETIC_FIXTURE_ROOT / "exp.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["exp"],
                    "two_squared",
                    (2, 2),
                    4,
                )
            ],
        )

        self.assertIn(
            "let result := exp InterpreterTypes.I interpreter",
            source,
        )

    def test_exp_fixture_includes_full_width_exponents(self) -> None:
        cases = fixture_test.load_instruction_cases(
            fixture_test.ARITHMETIC_FIXTURE_ROOT / "exp.json",
            "Cancun",
        )
        case_names = [case.name for case in cases]

        self.assertIn("exp_2_257", case_names)
        self.assertIn("exp_0_big", case_names)
        self.assertIn("exp_neg1_neg2", case_names)

    def test_render_rocq_uses_revm_bitand_simulation(self) -> None:
        source = fixture_test.render_rocq(
            [fixture_test.BITWISE_FIXTURE_ROOT / "and.json"],
            "Cancun",
            [
                fixture_test.InstructionCase(
                    fixture_test.INSTRUCTIONS["and"],
                    "example",
                    (3, 5),
                    1,
                )
            ],
        )

        self.assertIn("bitwise.bitand", source)
        self.assertIn("let result := op_bitand interpreter", source)


if __name__ == "__main__":
    unittest.main()
