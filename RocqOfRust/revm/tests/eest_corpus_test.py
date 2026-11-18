"""Synthetic index, strict accounting and persistent signed-protocol regressions.

The mock process checks the transport, not Rocq semantics or pinned EEST coverage.
"""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import eest_corpus as corpus
import run_eest_corpus as runner
import transaction_compare as compare
import transaction_fixture as fixture
import verify_eest_corpus as verify


TXBYTES = "0xdf800182520894" + "11" * 20 + "80801b0101"


def raw_test():
    account = {"balance": "0x100000", "nonce": "0x00", "code": "0x", "storage": {}}
    return {
        "env": {"currentCoinbase": "0x" + "22" * 20, "currentGasLimit": "0x100000",
                "currentNumber": "0x01", "currentTimestamp": "0x01", "currentBaseFee": "0x00",
                "currentRandom": "0x00", "currentExcessBlobGas": "0x00"},
        "pre": {"0x" + "33" * 20: account},
        "transaction": {"data": ["0x"], "gasLimit": ["0x5208"], "gasPrice": "0x01",
                        "nonce": "0x00", "sender": "0x" + "33" * 20,
                        "to": "0x" + "11" * 20, "value": ["0x00"]},
        "post": {"Cancun": [{"indexes": {"data": 0, "gas": 0, "value": 0},
                             "hash": "0x" + "00" * 32, "logs": "0x" + "01" * 32,
                             "txbytes": TXBYTES}]},
    }


def create_index(root: Path, *, extra_formats: bool = False) -> dict:
    (root / ".meta").mkdir()
    (root / "state_tests").mkdir()
    test = raw_test()
    test["_info"] = {"hash": corpus.canonical_hash(test)}
    cases = [{"id": "synthetic[state-test]", "fixture_hash": test["_info"]["hash"],
              "fork": "Cancun", "json_path": "state_tests/case.json", "format": "state_test"}]
    (root / cases[0]["json_path"]).write_text(json.dumps({cases[0]["id"]: test}))
    if extra_formats:
        for fixture_format in sorted(set(corpus.FORMAT_DIRECTORIES) - {"state_test"}):
            directory = corpus.FORMAT_DIRECTORIES[fixture_format]
            (root / directory).mkdir()
            raw = ({"txbytes": TXBYTES, "result": {"Cancun": {
                       "exception": "TransactionException.NONCE_OVERFLOW", "intrinsicGas": "0x00"}}}
                   if fixture_format == "transaction_test" else {"network": "Cancun"})
            digest = corpus.canonical_hash(raw)
            raw["_info"] = {"hash": digest}
            case = {"id": "synthetic[" + fixture_format + "]", "fixture_hash": digest,
                    "fork": "Cancun", "json_path": directory + "/case.json", "format": fixture_format}
            cases.append(case)
            (root / case["json_path"]).write_text(json.dumps({case["id"]: raw}))
    (root / ".meta/index.json").write_text(json.dumps({"test_cases": cases}))
    return corpus.load_index(root, require_pin=False)


def native_result(index: dict, case: dict, *, verified: bool = True) -> dict:
    source = corpus.normalize(index, case)
    return {"protocol": 1, "engine": "rocq_revm", "kind": "Completed", "status": "Stop",
            "authentication": {"verified": verified,
                               "transaction": source["transaction"] if verified else None},
            "gas": {key: 0 for key in compare.SETTLEMENT_FIELDS}, "data": [], "accounts": [], "logs": [],
            "commitments": {"source": "rocq", "state_root": source["expectation"]["state_root"],
                            "logs_hash": source["expectation"]["logs_hash"]}}


def make_record(index: dict, case: dict, *, verified: bool = True) -> dict:
    output = native_result(index, case, verified=verified)
    request = compare.serialize_input(corpus.normalize(index, case), 1000, signed=True)
    status, comparison = runner.classification(index, case, output)
    return {"protocol": 1, "engine": "rocq_revm", "fixture": dict(case), "pin": dict(index["pin"]),
            "fuel": 1000, "timeout_seconds": 5, "duration_seconds": 0,
            "bridge_sha256": "0" * 64, "request_sha256": hashlib.sha256(request.encode()).hexdigest(),
            "status": status, "comparison": comparison, "native_output": output,
            "reasons": comparison.get("reasons", [])}


def expect_error(function, text=""):
    try:
        function()
    except (fixture.FixtureError, TimeoutError) as error:
        assert text in str(error), str(error)
    else:
        raise AssertionError("expected error containing " + repr(text))


def test_canonical_hash_uses_sorted_compact_payload_without_info():
    expected = "0x43258cff783fe7036d8a43033f830adfc60ec037382473548ac742b888292777"
    assert corpus.canonical_hash({"b": 2, "_info": {"hash": "irrelevant"}, "a": 1}) == expected


def test_pin_census_and_unpinned_scope():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        assert index["pin"]["verified"] is False and index["pin"]["commit"] is None
        expect_error(lambda: corpus.load_index(root), "digest")
        with patch.object(corpus, "PINNED_INDEX_SHA256", index["pin"]["index_sha256"]):
            expect_error(lambda: corpus.load_index(root), "census")
        case = corpus.select_cases(index)[0]
        record = make_record(index, case)
        summary = verify.verify_records(index, [case], [record])
        assert record["status"] == "authenticated_state_pass"
        assert not any(summary[field] for field in ("all_selected_pass", "full_state_corpus_pass", "full_eest_corpus_pass"))


def test_all_formats_in_selection_and_explicit_unsupported_results():
    with tempfile.TemporaryDirectory() as directory:
        index = create_index(Path(directory), extra_formats=True)
        selected = corpus.select_cases(index, fixture_format="all")
        assert len(selected) == 6
        records = []
        for case in selected:
            if case["format"] == "state_test":
                records.append(make_record(index, case))
            else:
                if case["format"] == "transaction_test":
                    output = {"protocol": 1, "engine": "rocq_revm", "scope": "raw_transaction",
                              "kind": "Unsupported", "reason": "RawValidationUnavailable", "details": []}
                    with patch.object(runner, "bridge_exchange", return_value=output):
                        records.append(runner.run_case(index, case, {}, Path("/missing"), 1000, 5, "0" * 64))
                    assert records[-1]["reasons"] == ["RawValidationUnavailable"]
                else:
                    records.append(runner.run_case(index, case, {}, Path("/missing"), 1000, 5, "0" * 64))
                    assert records[-1]["reasons"] == ["format:" + case["format"]]
                assert records[-1]["status"] == "unsupported"
        summary = verify.verify_records(index, selected, records)
        assert summary["statuses"] == {"authenticated_state_pass": 1, "unsupported": 5}
        assert summary["full_eest_corpus_pass"] is False
        partitions = [corpus.shard_for_id(case["id"], 3) for case in selected]
        assert all(0 <= partition < 3 for partition in partitions)


def test_exact_selection_rejects_ambiguous_or_invalid_inputs():
    with tempfile.TemporaryDirectory() as directory:
        index = create_index(Path(directory))
        case = corpus.select_cases(index)[0]
        assert corpus.select_cases(index, exact_ids=[case["id"]]) == [case]
        expect_error(lambda: corpus.select_cases(index, exact_ids=[case["id"]] * 2), "duplicate")
        expect_error(lambda: corpus.select_cases(index, exact_ids=["missing"]), "unknown")
        expect_error(lambda: corpus.select_cases(index, fork="Osaka"), "unknown")
        expect_error(lambda: corpus.select_cases(index, shard_count=2), "together")
        expect_error(lambda: corpus.select_cases(index, shard_count=True, shard_index=0), "coordinates")
        expect_error(lambda: corpus.select_cases(index, shard_count=2, shard_index=2), "coordinates")
        expect_error(lambda: corpus.select_cases(index, fixture_format="transaction_test", exact_ids=[case["id"]]), "conflict")


def test_metadata_duplicate_keys_paths_and_hashes_fail_closed():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        path = root / ".meta/index.json"
        for field, value in (("id", ""), ("fixture_hash", "0x1234"), ("json_path", "state_tests/../case.json"),
                             ("json_path", "/state_tests/case.json"), ("format", "unknown")):
            changed = dict(case, **{field: value})
            path.write_text(json.dumps({"test_cases": [changed]}))
            expect_error(lambda: corpus.load_index(root, require_pin=False))
        path.write_text(json.dumps({"test_cases": [case, case]}))
        expect_error(lambda: corpus.load_index(root, require_pin=False), "duplicate")
        expect_error(lambda: corpus.read_json('{"test_cases":[],"test_cases":[]}'), "duplicate")
        expect_error(lambda: corpus.read_json('{"value":NaN}'), "non-finite")


def test_payload_mutation_retaining_info_hash_and_symlink_escape_are_rejected():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        document = json.loads((root / case["json_path"]).read_text())
        document[case["id"]]["transaction"]["nonce"] = "0x01"
        (root / case["json_path"]).write_text(json.dumps(document))
        corpus.fixture_document.cache_clear()
        expect_error(lambda: corpus.load_test(index, case), "payload hash")
        path = root / "state_tests/escape.json"
        path.symlink_to(root.parent / "outside.json")
        expect_error(lambda: corpus.fixture_document(root, "state_tests/escape.json"), "escapes")


def test_exact_post_id_and_fork_shape_are_required():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        changed = dict(case, id="other")
        expect_error(lambda: corpus.load_test(index, changed), "exact metadata ID")
        test = raw_test()
        test["post"]["Prague"] = copy.deepcopy(test["post"]["Cancun"])
        case["fixture_hash"] = corpus.canonical_hash(test)
        test["_info"] = {"hash": case["fixture_hash"]}
        (root / case["json_path"]).write_text(json.dumps({case["id"]: test}))
        corpus.fixture_document.cache_clear()
        expect_error(lambda: corpus.load_test(index, case), "exactly one post")


def test_verifier_rejects_missing_duplicate_extra_and_cross_identity_records():
    with tempfile.TemporaryDirectory() as directory:
        index = create_index(Path(directory))
        case = corpus.select_cases(index)[0]
        record = make_record(index, case)
        expect_error(lambda: verify.verify_records(index, [case], []), "missing")
        expect_error(lambda: verify.verify_records(index, [case], [record, record]), "duplicate")
        for field, value in (("engine", "geth"), ("protocol", True), ("fuel", True),
                             ("timeout_seconds", float("nan")), ("duration_seconds", -1),
                             ("request_sha256", "0" * 64), ("status", "pass")):
            changed = copy.deepcopy(record)
            changed[field] = value
            expect_error(lambda: verify.verify_records(index, [case], [changed]))
        changed = copy.deepcopy(record)
        changed["fixture"]["id"] = "unknown"
        expect_error(lambda: verify.verify_records(index, [case], [changed]), "unselected")
        changed = copy.deepcopy(record)
        changed["fixture"]["fixture_hash"] = "0x" + "11" * 32
        expect_error(lambda: verify.verify_records(index, [case], [changed]), "identity")
        changed = copy.deepcopy(record)
        changed["pin"]["verified"] = 0
        expect_error(lambda: verify.verify_records(index, [case], [changed]), "pin")
        changed = copy.deepcopy(record)
        changed["extra"] = 1
        expect_error(lambda: verify.verify_records(index, [case], [changed]), "fields")


def test_execution_only_or_forged_commitments_can_never_be_promoted_to_pass():
    with tempfile.TemporaryDirectory() as directory:
        index = create_index(Path(directory))
        # In-memory pin simulation exercises the promotion guard, not actual pin acceptance.
        index["pin"].update(verified=True, ref=corpus.PINNED_REF, commit=corpus.PINNED_COMMIT)
        case = corpus.select_cases(index)[0]
        record = make_record(index, case)
        assert verify.verify_records(index, [case], [record])["all_selected_pass"] is True
        assert verify.verify_records(index, [case], [record])["full_state_corpus_pass"] is False
        unsigned = make_record(index, case, verified=False)
        assert unsigned["status"] == "execution_only"
        assert verify.verify_records(index, [case], [unsigned])["all_selected_pass"] is False
        unsigned["status"] = "pass"
        expect_error(lambda: verify.verify_records(index, [case], [unsigned]), "comparison")
        for mutate in (lambda r: r["native_output"]["commitments"].update(source="python"),
                       lambda r: r["native_output"]["commitments"]["state_root"].__setitem__(0, 99),
                       lambda r: r["native_output"]["authentication"]["transaction"].update(nonce=99),
                       lambda r: r.update(bridge_sha256=None),
                       lambda r: r.update(comparison=None, native_output=None)):
            changed = copy.deepcopy(record)
            mutate(changed)
            expect_error(lambda: verify.verify_records(index, [case], [changed]))


def mock_bridge(root: Path, source: str) -> Path:
    path = root / "mock_bridge"
    path.write_text("#!/usr/bin/env python3\n" + source)
    path.chmod(0o700)
    return path


def test_persistent_transport_requires_signed_requests_and_reuses_successful_process():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        output = native_result(index, case)
        executable = mock_bridge(root,
            "import json, sys\n"
            "for line in sys.stdin:\n"
            "    request = json.loads(line)\n"
            "    assert request['request'] == 'execute_signed_transaction'\n"
            "    assert 'transaction' not in request\n"
            "    assert request['fuel'] == 1000\n"
            "    print(" + repr(json.dumps(output)) + ", flush=True)\n")
        bridge = {}
        try:
            first = runner.run_case(index, case, bridge, executable, 1000, 2)
            process = bridge["process"]
            second = runner.run_case(index, case, bridge, executable, 1000, 2)
            assert bridge["process"] is process
            assert first["status"] == second["status"] == "authenticated_state_pass"
            verify.validate_record(index, case, first)
        finally:
            runner.stop_bridge(bridge)


def test_timeout_exit_wire_errors_and_incomplete_reset_the_bridge():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        programs = (("import time\ntime.sleep(1)\n", "timeout"),
                    ("import sys\nsys.exit(3)\n", "runner_error"),
                    ("print('{}', flush=True)\n", "runner_error"),
                    ("print('{}\\n{}', flush=True)\n", "runner_error"))
        for source, status in programs:
            bridge = {}
            result = runner.run_case(index, case, bridge, mock_bridge(root, source), 1000, 0.1)
            assert result["status"] == status, result
            assert not bridge
            assert result["fuel"] == 1000 and result["request_sha256"] is not None
        incomplete = {"protocol": 1, "engine": "rocq_revm", "kind": "Incomplete",
                      "authentication": {"verified": False, "transaction": None}}
        source = "import sys\nfor line in sys.stdin:\n    print(" + repr(json.dumps(incomplete)) + ", flush=True)\n"
        bridge = {}
        record = runner.run_case(index, case, bridge, mock_bridge(root, source), 1000, 1)
        assert record["status"] == "incomplete" and not bridge
        verify.validate_record(index, case, record)
        with patch.object(runner, "bridge_exchange", side_effect=RuntimeError("transport bug")):
            record = runner.run_case(index, case, {}, Path("/missing"), 1000, 1)
        assert record["status"] == "internal_error" and "transport bug" in record["reasons"][0]
        verify.validate_record(index, case, record)


def test_verifier_validates_native_schema_before_any_classification():
    with tempfile.TemporaryDirectory() as directory:
        index = create_index(Path(directory))
        case = corpus.select_cases(index)[0]
        original = make_record(index, case)
        mutations = (lambda r: r["native_output"]["authentication"].update(verified=1),
                     lambda r: r["native_output"].update(authentication={"verified": True, "transaction": None}),
                     lambda r: r["native_output"].update(authentication={"verified": False, "transaction": {}}),
                     lambda r: r["native_output"].update(engine="geth"),
                     lambda r: r["native_output"].update(protocol=True),
                     lambda r: r["native_output"].update(extra=1),
                     lambda r: r["native_output"]["gas"].update(gas_used=True),
                     lambda r: r["native_output"]["commitments"].update(state_root=[0] * 31))
        for mutate in mutations:
            record = copy.deepcopy(original)
            mutate(record)
            with patch.object(runner, "classification", side_effect=AssertionError("validator bypassed")):
                expect_error(lambda: verify.validate_record(index, case, record))
            record.update(comparison=None, status="runner_error")
            expect_error(lambda: verify.validate_record(index, case, record))


def test_child_observes_memory_core_and_stderr_file_limits():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        executable = mock_bridge(root,
            "import json, resource, sys\n"
            "for line in sys.stdin:\n"
            "    limits = [value for key in (resource.RLIMIT_AS, resource.RLIMIT_CORE, resource.RLIMIT_FSIZE) "
            "for value in resource.getrlimit(key)]\n"
            "    print(json.dumps({'protocol': 1, 'engine': 'rocq_revm', 'kind': 'Unsupported', "
            "'authentication': {'verified': False, 'transaction': None}, 'reason': 'ResourceLimits', "
            "'details': limits}), flush=True)\n")
        record = runner.run_case(index, case, {}, executable, 1000, 2)
        assert record["status"] == "unsupported", record
        limits = record["native_output"]["details"]
        assert limits == [runner.MAX_ADDRESS_SPACE] * 2 + [0, 0] + [runner.MAX_STDERR_BYTES] * 2
        executable = mock_bridge(root,
            "import os\n"
            "data = b'x' * (9 * 1024 * 1024)\n"
            "while data:\n"
            "    written = os.write(2, data)\n"
            "    data = data[written:]\n")
        sizes = []
        stop = runner.stop_bridge
        def collect_stderr_size(bridge):
            if bridge:
                sizes.append(bridge['stderr'].seek(0, 2))
            return stop(bridge)
        with patch.object(runner, "stop_bridge", side_effect=collect_stderr_size):
            record = runner.run_case(index, case, {}, executable, 1000, 2)
        assert record["status"] == "runner_error", record
        assert sizes and max(sizes) <= runner.MAX_STDERR_BYTES
        assert "bridge stderr:" in record["reasons"][0]
        assert len(record["reasons"][0]) <= runner.MAX_ERROR_CHARS + len(" [truncated]")
        with patch.object(corpus, "load_test", side_effect=fixture.FixtureError("x" * 10000)):
            record = runner.run_case(index, case, {}, executable, 1000, 2)
        assert record["status"] == "fixture_error"
        assert len(record["reasons"][0]) <= runner.MAX_ERROR_CHARS + len(" [truncated]")


def test_result_reader_bounds_each_line_before_json_parsing():
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "results.jsonl"
        path.write_text("x" * 100 + "\n")
        with patch.object(compare, "MAX_WIRE_BYTES", 16):
            expect_error(lambda: list(verify.read_records([path])), "size limit")
        path.write_text('{"duplicate":1,"duplicate":2}\n')
        expect_error(lambda: list(verify.read_records([path])), "duplicate")


def test_missing_bytes_unknown_fork_and_exception_never_use_execution_only_fallback():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index = create_index(root)
        case = corpus.select_cases(index)[0]
        test = raw_test()
        del test["post"]["Cancun"][0]["txbytes"]
        case["fixture_hash"] = corpus.canonical_hash(test)
        test["_info"] = {"hash": case["fixture_hash"]}
        (root / case["json_path"]).write_text(json.dumps({case["id"]: test}))
        corpus.fixture_document.cache_clear()
        record = runner.run_case(index, case, {}, Path("/missing"), 1000, 1)
        assert record["status"] == "unsupported" and record["request_sha256"] is None
        assert "missing_signed_transaction" in record["reasons"]
        test["post"]["UnknownFutureFork"] = test["post"].pop("Cancun")
        case.update(fork="UnknownFutureFork", fixture_hash=corpus.canonical_hash(test))
        test["_info"]["hash"] = case["fixture_hash"]
        (root / case["json_path"]).write_text(json.dumps({case["id"]: test}))
        corpus.fixture_document.cache_clear()
        record = runner.run_case(index, case, {}, Path("/missing"), 1000, 1)
        assert record["status"] == "unsupported" and record["reasons"] == ["fork:UnknownFutureFork"]
        test["post"]["Cancun"] = test["post"].pop("UnknownFutureFork")
        test["post"]["Cancun"][0]["txbytes"] = TXBYTES
        test["post"]["Cancun"][0]["expectException"] = "TR_InvalidS"
        case.update(fork="Cancun", fixture_hash=corpus.canonical_hash(test))
        test["_info"]["hash"] = case["fixture_hash"]
        (root / case["json_path"]).write_text(json.dumps({case["id"]: test}))
        corpus.fixture_document.cache_clear()
        output = {"protocol": 1, "engine": "rocq_revm", "kind": "AuthenticationRejected",
                  "reason": "InvalidSignature", "details": [],
                  "accounts": [], "logs": [],
                  "commitments": {"source": "rocq", "state_root": [0] * 32, "logs_hash": [1] * 32},
                  "authentication": {"verified": False, "transaction": None}}
        status, comparison = runner.classification(index, case, output)
        assert status == "unsupported" and comparison["full_eest_pass"] is False
        assert comparison["reasons"] == ["transaction_exception_mapping_required"]



def test_prefork_type_rejection_without_claiming_signature_recovery():
    # Synthetic fixture and wire response exercise validation, not execution.
    raw = raw_test()
    payload = bytes.fromhex("01800182520894" + "11" * 20 + "8080c0800101")
    encoded = bytes([1, 0xc0 + len(payload)]) + payload
    post = raw["post"].pop("Cancun")
    post[0].update(txbytes="0x" + encoded.hex(),
                   expectException="TransactionException.TYPE_1_TX_PRE_FORK")
    raw["post"]["Frontier"] = post
    raw["transaction"]["accessLists"] = [[]]
    source = fixture.normalize_case({"synthetic": raw}, "Frontier", 0, test_name="synthetic")
    output = {"protocol": 1, "engine": "rocq_revm", "kind": "AuthenticationRejected",
              "authentication": {"verified": False, "transaction": None},
              "reason": "TransactionTypeNotSupported", "details": [1],
              "accounts": copy.deepcopy(source["input"]["accounts"]), "logs": [],
              "commitments": {"source": "rocq", "state_root": source["expectation"]["state_root"],
                              "logs_hash": source["expectation"]["logs_hash"]}}
    result = compare.compare_execution(source, output)
    assert result["classification"] == "validated_state_rejection", result
    assert result["authentication_verified"] is False
    assert result["full_eest_pass"] is False
    mutations = [("fork", "Berlin"), ("fork", "Osaka")]
    for key, value in mutations:
        bad = copy.deepcopy(source); bad[key] = value
        assert compare.compare_execution(bad, output)["classification"] != "validated_state_rejection"
    for key, value in [("exception", "TransactionException.INTRINSIC_GAS_TOO_LOW"),
                       ("txbytes", None), ("txbytes", [1]), ("state_root", None)]:
        bad = copy.deepcopy(source); bad["expectation"][key] = value
        assert compare.compare_execution(bad, output)["classification"] != "validated_state_rejection"
    for key, value in [("reason", "InvalidSignature"), ("details", [2]), ("details", [])]:
        bad = copy.deepcopy(output); bad[key] = value
        assert compare.compare_execution(source, bad)["classification"] != "validated_state_rejection"
    for key in ("nonce", "gas_limit", "value"):
        bad = copy.deepcopy(source); bad["transaction"][key] += 1
        assert compare.compare_execution(bad, output)["classification"] != "validated_state_rejection"
    for key in ("state_root", "logs_hash"):
        bad = copy.deepcopy(output); bad["commitments"][key][0] ^= 1
        assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    bad = copy.deepcopy(output); bad["accounts"][0]["balance"] += 1
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    for key in ("accounts", "commitments"):
        bad = copy.deepcopy(output); del bad[key]
        try:
            compare.parse_output(json.dumps(bad))
        except fixture.FixtureError:
            pass
        else:
            raise AssertionError("missing rejection evidence accepted")
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / ".meta").mkdir(); (root / "state_tests").mkdir()
        raw["_info"] = {"hash": corpus.canonical_hash(raw)}
        meta = {"id": "synthetic", "fork": "Frontier", "format": "state_test",
                "json_path": "state_tests/case.json", "fixture_hash": raw["_info"]["hash"]}
        (root / "state_tests/case.json").write_text(json.dumps({"synthetic": raw}))
        (root / ".meta/index.json").write_text(json.dumps({"test_cases": [meta]}))
        index = corpus.load_index(root, require_pin=False)
        status, comparison = runner.classification(index, meta, output)
        assert status == "validated_state_rejection"
        assert comparison["full_eest_pass"] is False
        record = {"protocol": corpus.RECORD_VERSION, "engine": "rocq_revm", "fixture": meta,
                  "pin": index["pin"], "fuel": 1000, "timeout_seconds": 60, "duration_seconds": 0,
                  "bridge_sha256": "0" * 64,
                  "request_sha256": hashlib.sha256(compare.serialize_input(source, 1000, signed=True).encode()).hexdigest(),
                  "status": status, "comparison": comparison, "native_output": output, "reasons": []}
        assert verify.verify_records(index, [meta], [record])["all_selected_pass"] is False
        for field, value in (("authentication_verified", True), ("full_eest_pass", True)):
            bad = copy.deepcopy(record); bad["comparison"][field] = value
            try:
                verify.verify_records(index, [meta], [bad])
            except fixture.FixtureError:
                pass
            else:
                raise AssertionError("tampered rejection evidence accepted")
        bad = copy.deepcopy(record); bad["pin"]["verified"] = True; bad["status"] = "pass"
        try:
            verify.verify_records(index, [meta], [bad])
        except fixture.FixtureError:
            pass
        else:
            raise AssertionError("forged pin accepted")


TESTS = tuple(value for name, value in tuple(globals().items()) if name.startswith("test_"))

if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} synthetic EEST corpus runner/verifier tests passed; no pinned corpus execution claimed")
