"""Synthetic raw-format schema, comparison and corpus-accounting regressions.

Mock responses verify protocol/accounting guards, not Rocq validation semantics.
"""

import copy
import hashlib
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import eest_corpus as corpus
import run_eest_corpus as runner
import transaction_compare as wire
import transaction_fixture as fixture
import transaction_format as raw
import verify_eest_corpus as verifier


def test_document(negative=True):
    expected = ({"exception": "TransactionException.NONCE_OVERFLOW", "intrinsicGas": "0x00"}
                if negative else {"sender": "0x" + "11" * 20, "hash": "0x" + "22" * 32,
                                  "intrinsicGas": "0x5208"})
    return {"_info": {}, "txbytes": "0x01c0", "result": {"Cancun": expected}}


def output(kind, **fields):
    return {"protocol": 1, "engine": "rocq_revm", "scope": "raw_transaction", "kind": kind, **fields}


def valid_output():
    return output("Valid", sender=int("11" * 20, 16), hash=[34] * 32, intrinsic_gas=21000)


def expect_error(action):
    try:
        action()
    except fixture.FixtureError:
        pass
    else:
        raise AssertionError("expected strict schema/accounting rejection")


def index_case(root):
    (root / ".meta").mkdir()
    (root / "transaction_tests").mkdir()
    test = test_document()
    digest = corpus.canonical_hash(test)
    test["_info"] = {"hash": digest}
    case = {"id": "synthetic[raw-transaction]", "format": "transaction_test", "fork": "Cancun",
            "json_path": "transaction_tests/case.json", "fixture_hash": digest}
    (root / case["json_path"]).write_text(json.dumps({case["id"]: test}))
    (root / ".meta/index.json").write_text(json.dumps({"test_cases": [case]}))
    index = corpus.load_index(root, require_pin=False)
    return index, case


def record_for(index, case, native):
    status, comparison = runner.classification(index, case, native)
    request = runner.serialize_case_request(index, case, 1000)
    return {"protocol": 1, "engine": "rocq_revm", "fixture": dict(case), "pin": dict(index["pin"]),
            "fuel": 1000, "timeout_seconds": 1, "duration_seconds": 0,
            "bridge_sha256": "0" * 64, "request_sha256": hashlib.sha256(request.encode()).hexdigest(),
            "status": status, "comparison": comparison, "native_output": native,
            "reasons": comparison.get("reasons", [])}


def test_raw_request_contains_only_semantic_inputs():
    case = raw.normalize_case(test_document(), "Cancun", "raw-case")
    request = json.loads(raw.serialize_input(case))
    assert set(request) == {"protocol", "request", "fork", "chain_id", "signed_transaction"}
    assert request["request"] == "validate_signed_transaction" and request["chain_id"] == 1
    assert request["signed_transaction"] == [1, 192]
    case["expectation"].update(exception="other diagnostic", intrinsic_gas=123)
    assert json.loads(raw.serialize_input(case)) == request


def test_fixture_positive_and_negative_shapes_are_disjoint():
    for negative in (False, True):
        case = raw.normalize_case(test_document(negative), "Cancun", "case")
        assert (case["expectation"]["exception"] is not None) == negative
    mutations = (lambda d: d.update(unknown=True), lambda d: d.pop("txbytes"),
                 lambda d: d["result"].update(Prague={}), lambda d: d["result"]["Cancun"].update(sender="0x" + "00" * 20),
                 lambda d: d["result"]["Cancun"].update(exception=""),
                 lambda d: d["result"]["Cancun"].update(exception=None),
                 lambda d: d["result"]["Cancun"].update(intrinsicGas=True),
                 lambda d: d["result"]["Cancun"].update(intrinsicGas=2 ** 64),
                 lambda d: d.update(txbytes="0x0"))
    for mutate in mutations:
        document = test_document()
        mutate(document)
        expect_error(lambda: raw.normalize_case(document, "Cancun", "case"))
    assert raw.fixture_gas("21000") == raw.fixture_gas("0x5208") == raw.fixture_gas(21000)


def test_positive_comparison_checks_every_observation():
    case = raw.normalize_case(test_document(False), "Cancun", "case")
    assert raw.compare_result(case, valid_output())["classification"] == "validated_transaction_pass"
    for field, value in (("sender", 0), ("hash", [0] * 32), ("intrinsic_gas", 21001)):
        native = valid_output()
        native[field] = value
        comparison = raw.compare_result(case, native)
        assert comparison["classification"] == "transaction_mismatch"
        assert comparison["differences"][0]["field"] == field
    assert raw.compare_result(case, output("Rejected", reason="MalformedRlp", details=[]))["classification"] == "transaction_mismatch"


def test_definite_rejection_and_unfinished_results_are_distinct():
    case = raw.normalize_case(test_document(), "Cancun", "case")
    rejected = raw.compare_result(case, output("Rejected", reason="MalformedFields", details=[]))
    assert rejected["classification"] == "validated_transaction_rejection"
    assert rejected["validation_verified"] is True and rejected["authentication_verified"] is False
    for native in (output("Unsupported", reason="TransactionType", details=[4]), output("Incomplete")):
        comparison = raw.compare_result(case, native)
        assert comparison["classification"] not in raw.PASS_CLASSIFICATIONS
        assert comparison["validation_verified"] is False and comparison["full_eest_pass"] is False
    assert raw.compare_result(case, valid_output())["classification"] == "transaction_mismatch"


def test_native_wire_rejects_wrong_scope_engine_kinds_and_widths():
    mutations = (lambda d: d.update(protocol=True), lambda d: d.update(engine="geth"),
                 lambda d: d.update(scope="execution_only"), lambda d: d.update(kind=[]),
                 lambda d: d.update(kind="Completed"), lambda d: d.update(sender=True),
                 lambda d: d.update(sender=2 ** 160), lambda d: d.update(intrinsic_gas=2 ** 64),
                 lambda d: d.update(hash=[0] * 31), lambda d: d.update(hash=[True] * 32),
                 lambda d: d.update(hash=[256] * 32), lambda d: d.update(extra=1))
    for mutate in mutations:
        native = valid_output()
        mutate(native)
        expect_error(lambda: raw.parse_output(json.dumps(native)))
    for kind in ("Rejected", "Unsupported"):
        for fields in ({"reason": "", "details": []}, {"reason": "x", "details": [True]},
                       {"reason": "x", "details": [], "sender": 0}):
            expect_error(lambda: raw.parse_output(json.dumps(output(kind, **fields))))
    expect_error(lambda: raw.parse_output('{"protocol":1,"protocol":1}'))
    expect_error(lambda: raw.parse_output('{"protocol":NaN}'))
    expect_error(lambda: raw.parse_output(json.dumps(output("Incomplete", reason="x"))))


def test_raw_record_verifier_recomputes_request_and_result():
    with tempfile.TemporaryDirectory() as directory:
        index, case = index_case(Path(directory))
        native = output("Rejected", reason="MalformedFields", details=[])
        record = record_for(index, case, native)
        assert record["status"] == "validated_transaction_rejection"
        assert verifier.verify_records(index, [case], [record])["all_selected_pass"] is False
        index["pin"].update(verified=True, ref=corpus.PINNED_REF, commit=corpus.PINNED_COMMIT)
        record = record_for(index, case, native)
        assert verifier.verify_records(index, [case], [record])["all_selected_pass"] is True
        assert verifier.verify_records(index, [case], [record])["full_transaction_corpus_pass"] is False
        for field, value in (("request_sha256", "1" * 64), ("comparison", None), ("bridge_sha256", None)):
            forged = copy.deepcopy(record)
            forged[field] = value
            expect_error(lambda: verifier.verify_records(index, [case], [forged]))
        for native in (output("Unsupported", reason="TransactionType", details=[4]), output("Incomplete")):
            unfinished = record_for(index, case, native)
            assert verifier.verify_records(index, [case], [unfinished])["all_selected_pass"] is False
            unfinished["status"] = "pass"
            expect_error(lambda: verifier.verify_records(index, [case], [unfinished]))
        forged = copy.deepcopy(record)
        forged["native_output"]["scope"] = "state"
        with patch.object(runner, "classification", side_effect=AssertionError("wire validator bypassed")):
            expect_error(lambda: verifier.validate_record(index, case, forged))


def test_raw_corpus_transport_uses_the_raw_response_parser():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        index, case = index_case(root)
        executable = root / "mock_raw_bridge"
        response = json.dumps(output("Rejected", reason="MalformedFields", details=[]))
        executable.write_text("#!/usr/bin/env python3\nimport json,sys\nfor line in sys.stdin:\n"
                              "    request=json.loads(line)\n"
                              "    assert set(request)=={'protocol','request','fork','chain_id','signed_transaction'}\n"
                              "    assert request['request']=='validate_signed_transaction'\n"
                              "    print(" + repr(response) + ",flush=True)\n")
        executable.chmod(0o700)
        bridge = {}
        try:
            record = runner.run_case(index, case, bridge, executable, 1000, 2, "0" * 64)
            assert record["status"] == "validated_transaction_rejection", record
            verifier.validate_record(index, case, record)
        finally:
            runner.stop_bridge(bridge)
        unfinished = output("Unsupported", reason="TransactionType", details=[4])
        with patch.object(runner, "bridge_exchange", return_value=unfinished):
            record = runner.run_case(index, case, {}, Path("/missing"), 1000, 1)
        assert record["status"] == "unsupported"
        verifier.validate_record(index, case, record)


TESTS = tuple(value for name, value in tuple(globals().items()) if name.startswith("test_") and name != "test_document")

if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} synthetic raw transaction adapter/accounting tests passed; no Rocq validation execution claimed")
