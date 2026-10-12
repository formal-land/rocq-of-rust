"""Focused state rejection guards; synthetic responses do not execute Rocq."""

import copy
import hashlib
import json
from pathlib import Path
import tempfile

import eest_corpus as corpus
import eest_corpus_test as examples
import run_eest_corpus as runner
import transaction_compare as compare
import transaction_fixture as fixture
import transaction_fixture_test as fixture_examples
import verify_eest_corpus as verify


ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def source(fork="Berlin", tx_type=0, v=27, r=1, s=1, chain_id=1, nonce=0, sender_nonce=0,
           exception="TransactionException.INVALID_SIGNATURE_VRS"):
    raw = examples.raw_test()
    post = raw["post"].pop("Cancun")
    raw["post"][fork] = post
    if exception is not None:
        post[0]["expectException"] = exception
    tx = raw["transaction"]
    tx["chainId"] = hex(chain_id)
    tx["nonce"] = hex(nonce)
    raw["pre"][tx["sender"]]["nonce"] = hex(sender_nonce)
    target = bytes.fromhex(tx["to"][2:])
    if tx_type == 0:
        fields = [nonce, 1, 21000, target, 0, b"", v, r, s]
    elif tx_type == 1:
        tx["accessLists"] = [[]]
        fields = [chain_id, nonce, 1, 21000, target, 0, b"", [], v, r, s]
    elif tx_type in (2, 3):
        del tx["gasPrice"]
        tx.update(maxFeePerGas="0x01", maxPriorityFeePerGas="0x00", accessLists=[[]])
        fields = [chain_id, nonce, 0, 1, 21000, target, 0, b"", []]
        if tx_type == 3:
            tx.update(maxFeePerBlobGas="0x00", blobVersionedHashes=["0x01" + "00" * 31])
            raw["env"]["currentBlobGasPrice"] = "0x01"
            fields += [0, [bytes.fromhex("01" + "00" * 31)]]
        fields += [v, r, s]
    else:
        raise AssertionError("unsupported synthetic transaction type")
    encoded = fixture_examples.rlp(fields)
    post[0]["txbytes"] = "0x" + ((bytes([tx_type]) if tx_type else b"") + encoded).hex()
    return fixture.normalize_case({"synthetic": raw}, fork), raw


def rejected(case, reason="InvalidSignature", details=None):
    return {"protocol": 1, "engine": "rocq_revm", "kind": "AuthenticationRejected",
            "authentication": {"verified": False, "transaction": None},
            "reason": reason, "details": [] if details is None else details,
            "accounts": copy.deepcopy(case["input"]["accounts"]), "logs": [],
            "commitments": {"source": "rocq", "state_root": case["expectation"]["state_root"],
                            "logs_hash": case["expectation"]["logs_hash"]}}


def expect_error(function, message):
    try:
        function()
    except fixture.FixtureError as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError("expected " + message)


def test_legacy_chain_id_derivation_preserves_signed_v_and_construction_metadata():
    for v, expected in ((0, None), (1, None), (27, None), (28, None),
                        (29, ((29 - 35) % (1 << 64)) // 2),
                        (34, (1 << 63) - 1), (35, 0), (36, 0), (37, 1), (39, 2),
                        (1 << 64, ((1 << 64) - 35) // 2)):
        case, raw = source(v=v, chain_id=1 if v < 35 else expected)
        assert case["transaction"]["chain_id"] == expected
        assert case["source"]["transaction"]["chainId"] == raw["transaction"]["chainId"]
        assert case["authentication"]["signature_recovery_verified"] is False
        assert json.loads(compare.serialize_input(case, signed=True))["signed_transaction"] == case["expectation"]["txbytes"]
    for tx_type in (0, 1, 2):
        case, raw = source(tx_type=tx_type, v=39 if tx_type == 0 else 0, chain_id=2)
        raw["transaction"]["chainId"] = "0x01"
        expect_error(lambda: fixture.normalize_case({"synthetic": raw}, "Berlin"), "chainId disagrees")


def test_invalid_signature_guards_match_only_exact_pre_recovery_validation():
    for tx_type, v, r, s in ((0, 27, ORDER, 1), (0, 27, 1, ORDER),
                            (0, 27, 1, ORDER // 2 + 1), (1, 27, 1, 1), (1, 0, 0, 1)):
        case, raw = source(tx_type=tx_type, v=v, r=r, s=s)
        output = rejected(case)
        result = compare.compare_execution(case, output)
        assert result["classification"] == "validated_state_rejection", result
        assert result["authentication_verified"] is False and result["full_eest_pass"] is False
        assert result["matched_exception"] == "TransactionException.INVALID_SIGNATURE_VRS"
        for mutate in (lambda out: out.update(reason="RecoveryFailed"),
                       lambda out: out.update(reason="SenderMismatch", details=[1, 2]),
                       lambda out: out.update(details=[1]),
                       lambda out: out["accounts"][0].update(balance=123),
                       lambda out: out["commitments"]["state_root"].__setitem__(0, 1),
                       lambda out: out["commitments"]["logs_hash"].__setitem__(0, 2)):
            bad = copy.deepcopy(output)
            mutate(bad)
            assert compare.compare_execution(case, bad)["classification"] != "validated_state_rejection"
    case, raw = source(r=1, s=1)
    assert compare.compare_execution(case, rejected(case))["classification"] != "validated_state_rejection"
    case, raw = source(fork="Frontier", s=ORDER // 2 + 1)
    assert compare.compare_execution(case, rejected(case))["classification"] != "validated_state_rejection"
    case, raw = source(fork="Homestead", v=37)
    assert compare.compare_execution(case, rejected(case))["classification"] == "validated_state_rejection"
    case["expectation"]["exception"] = "TR_InvalidS"
    assert compare.compare_execution(case, rejected(case))["reasons"] == ["transaction_exception_mapping_required"]


def test_chain_id_rejection_checks_exact_details_and_validation_order():
    for tx_type, v in ((0, 39), (1, 0)):
        case, raw = source(tx_type=tx_type, v=v, chain_id=2, exception="TransactionException.INVALID_CHAINID")
        output = rejected(case, "ChainIdMismatch", [2, 1])
        assert compare.compare_execution(case, output)["classification"] == "validated_state_rejection"
        for details in ([], [1, 2], [2, 2], [3, 1]):
            bad = copy.deepcopy(output)
            bad["details"] = details
            assert compare.compare_execution(case, bad)["classification"] != "validated_state_rejection"
        case["input"]["chain_id"] = 2
        assert compare.compare_execution(case, output)["classification"] != "validated_state_rejection"
    case, raw = source(v=34, exception="TransactionException.INVALID_SIGNATURE_VRS|TransactionException.INVALID_CHAINID")
    result = compare.compare_execution(case, rejected(case, "ChainIdMismatch", [(1 << 63) - 1, 1]))
    assert result["matched_exception"] == "TransactionException.INVALID_CHAINID"
    assert result["classification"] == "validated_state_rejection"
    assert compare.compare_execution(case, rejected(case))["classification"] != "validated_state_rejection"
    case, raw = source(fork="Homestead", v=39, chain_id=2, exception="TransactionException.INVALID_CHAINID")
    assert compare.compare_execution(case, rejected(case, "ChainIdMismatch", [2, 1]))["classification"] != "validated_state_rejection"


def test_prefork_type_rejections_cover_all_enabled_boundaries_without_recovery():
    for tx_type, invalid_fork, valid_fork in ((1, "Istanbul", "Berlin"), (2, "Berlin", "London"), (3, "Shanghai", "Cancun")):
        exception = f"TransactionException.TYPE_{tx_type}_TX_PRE_FORK"
        case, raw = source(fork=invalid_fork, tx_type=tx_type, v=0, exception=exception)
        output = rejected(case, "TransactionTypeNotSupported", [tx_type])
        assert compare.compare_execution(case, output)["classification"] == "validated_state_rejection"
        output["details"] = [tx_type + 1]
        assert compare.compare_execution(case, output)["classification"] != "validated_state_rejection"
        output["details"] = [tx_type]
        case["fork"] = valid_fork
        assert compare.compare_execution(case, output)["classification"] != "validated_state_rejection"
        case["fork"] = invalid_fork
        case["transaction"]["nonce"] += 1
        assert compare.compare_execution(case, output)["classification"] != "validated_state_rejection"


def test_mapped_handler_rejections_require_authentication_and_nonce_overflow_never_completes():
    for exception, reason in (("NONCE_MISMATCH_TOO_HIGH", "NonceTooHigh"),
                              ("NONCE_MISMATCH_TOO_LOW", "NonceTooLow"),
                              ("NONCE_IS_MAX", "NonceOverflow"),
                              ("INSUFFICIENT_MAX_FEE_PER_BLOB_GAS", "BlobGasPriceGreaterThanMax")):
        kwargs = {"nonce": 1} if reason == "NonceTooHigh" else {"sender_nonce": 1} if reason == "NonceTooLow" else {
            "nonce": (1 << 64) - 1, "sender_nonce": (1 << 64) - 1} if reason == "NonceOverflow" else {"fork": "Cancun", "tx_type": 3, "v": 0}
        case, raw = source(exception="TransactionException." + exception, **kwargs)
        output = rejected(case, reason, [1, 0] if reason == "BlobGasPriceGreaterThanMax" else [])
        output.update(kind="Rejected", authentication={"verified": True, "transaction": copy.deepcopy(case["transaction"])})
        assert compare.compare_execution(case, output)["classification"] == "authenticated_state_pass"
        output["reason"] = "DifferentReason"
        assert compare.compare_execution(case, output)["classification"] == "execution_mismatch"
        output["reason"] = reason
        bad = copy.deepcopy(output)
        bad["details"] = [9, 9]
        assert compare.compare_execution(case, bad)["classification"] == "execution_mismatch"
        bad = copy.deepcopy(case)
        if reason == "BlobGasPriceGreaterThanMax":
            bad["input"]["block"]["blob_base_fee"] = 0
        else:
            bad["transaction"]["nonce"] = 0 if reason != "NonceTooLow" else 1
        assert compare.compare_execution(bad, output)["classification"] == "execution_mismatch"
        output["authentication"] = {"verified": False, "transaction": None}
        assert compare.compare_execution(case, output)["reasons"] == ["rejection_authentication_required"]
        if exception == "NONCE_IS_MAX":
            output = {"protocol": 1, "engine": "rocq_revm", "kind": "Completed", "status": "Stop",
                      "authentication": {"verified": True, "transaction": case["transaction"]},
                      "gas": {name: 0 for name in compare.SETTLEMENT_FIELDS}, "data": [],
                      "accounts": case["input"]["accounts"], "logs": [], "commitments": output["commitments"]}
            result = compare.compare_execution(case, output)
            assert result["classification"] == "execution_mismatch"
            assert result["differences"] == [{"field": "result_kind", "expected": "Rejected", "actual": "Completed"}]


def test_independent_verifier_requires_pin_wire_and_unchanged_state_for_validated_rejection():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        case, raw = source(tx_type=1, v=27)
        raw["_info"] = {"hash": corpus.canonical_hash(raw)}
        metadata = {"id": "synthetic", "fork": "Berlin", "format": "state_test",
                    "json_path": "state_tests/case.json", "fixture_hash": raw["_info"]["hash"]}
        (root / "state_tests").mkdir()
        (root / metadata["json_path"]).write_text(json.dumps({"synthetic": raw}))
        pin = {"verified": False, "ref": None, "commit": None, "index_sha256": "0" * 64}
        index = {"root": root.resolve(), "cases": {"synthetic": metadata}, "pin": pin}
        output = rejected(case)
        status, comparison = runner.classification(index, metadata, output)
        request = compare.serialize_input(corpus.normalize(index, metadata), 1000, signed=True)
        record = {"protocol": 1, "engine": "rocq_revm", "fixture": metadata, "pin": dict(pin),
                  "fuel": 1000, "timeout_seconds": 2, "duration_seconds": 0,
                  "bridge_sha256": "0" * 64, "request_sha256": hashlib.sha256(request.encode()).hexdigest(),
                  "status": status, "comparison": comparison, "native_output": output, "reasons": []}
        verify.validate_record(index, metadata, record)
        assert record["status"] == "validated_state_rejection" and not comparison["full_eest_pass"]
        record["status"] = "pass"
        expect_error(lambda: verify.validate_record(index, metadata, record), "independent fixture comparison")
        pin.update(verified=True, ref=corpus.PINNED_REF, commit=corpus.PINNED_COMMIT)
        status, comparison = runner.classification(index, metadata, output)
        record.update(status=status, comparison=comparison, pin=dict(pin))
        assert status == "pass"
        verify.validate_record(index, metadata, record)
        malformed = copy.deepcopy(record)
        malformed["native_output"]["authentication"]["verified"] = 1
        expect_error(lambda: verify.validate_record(index, metadata, malformed), "authentication")
        changed = copy.deepcopy(record)
        changed["native_output"]["accounts"][0]["balance"] += 1
        expect_error(lambda: verify.validate_record(index, metadata, changed), "independent fixture comparison")


TESTS = tuple(value for name, value in tuple(globals().items()) if name.startswith("test_"))

if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} focused state rejection adapter tests passed; no native execution claimed")
