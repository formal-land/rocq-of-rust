"""Authenticated transaction requests and Rocq commitment comparisons."""

import copy
import json
import os
from pathlib import Path

import transaction_compare as compare
import transaction_fixture as fixture


FIXTURE_ROOT = Path(os.environ.get("REVM_FIXTURE_ROOT", Path.cwd() / "tests/revm-testdata/GeneralStateTests"))


def case():
    return fixture.load_case(FIXTURE_ROOT / "stExample/add11.json", "Cancun")


def completed(verified=False):
    source = case()
    return {"protocol": 1, "engine": "rocq_revm", "kind": "Completed", "status": "Stop",
            "authentication": {"verified": verified,
                               "transaction": copy.deepcopy(source["transaction"]) if verified else None},
            "gas": dict(zip(compare.SETTLEMENT_FIELDS, [356888, 0, 43112, 3568880, 0, 431120, 0])),
            "data": [], "accounts": copy.deepcopy(source["expectation"]["accounts"]), "logs": [],
            "commitments": {"source": "rocq", "state_root": source["expectation"]["state_root"],
                            "logs_hash": source["expectation"]["logs_hash"]}}


def other_result(kind, **fields):
    if kind in ("Rejected", "AuthenticationRejected"):
        source = completed()
        fields.update(accounts=source["accounts"], logs=[], commitments=source["commitments"])
    return {"protocol": 1, "engine": "rocq_revm", "kind": kind,
            "authentication": {"verified": False, "transaction": None}, **fields}


def expect_error(function, message):
    try:
        function()
    except fixture.FixtureError as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError(message)


def test_execution_serialization_preserves_full_width_integers_and_optional_chain_id():
    source = case()
    message = json.loads(compare.serialize_input(source, 1000, signed=False))
    assert message["protocol"] == 1 and message["request"] == "execute_transaction"
    assert message["fuel"] == 1000
    assert message["transaction"] == source["transaction"]
    assert message["input"] == source["input"]
    assert message["transaction"]["chain_id"] is None
    assert len(message["input"]["accounts"]) == 3
    source["transaction"].update(target=None, chain_id=2 ** 64 - 1, value=2 ** 256 - 1)
    message = json.loads(compare.serialize_input(source, signed=False))
    assert message["transaction"]["target"] is None
    assert message["transaction"]["chain_id"] == 2 ** 64 - 1
    assert message["transaction"]["value"] == 2 ** 256 - 1


def test_signed_serialization_sends_no_normalized_transaction():
    source = case()
    message = json.loads(compare.serialize_input(source))
    assert message["request"] == "execute_signed_transaction"
    assert message["signed_transaction"] == source["expectation"]["txbytes"]
    assert message["declared_sender"] == source["transaction"]["caller"]
    assert "transaction" not in message
    source["transaction"].update(caller=None, nonce=99, value=123, gas_price=456)
    source["unsupported"].append("sender_recovery_required")
    message = json.loads(compare.serialize_input(source))
    assert message["declared_sender"] is None
    assert "transaction" not in message
    assert message["signed_transaction"] == source["expectation"]["txbytes"]


def test_missing_signed_bytes_preserves_execution_only_request():
    source = case()
    source["expectation"]["txbytes"] = None
    assert json.loads(compare.serialize_input(source))["request"] == "execute_transaction"
    expect_error(lambda: compare.serialize_input(source, signed=True), "requires transaction bytes")


def test_authentication_handled_gaps_only_leave_signed_path_open():
    source = case()
    source["unsupported"].extend(["sender_recovery_required", "invalid_signed_envelope",
                                   "canonical_blob_creation_validation_required"])
    assert json.loads(compare.serialize_input(source))["request"] == "execute_signed_transaction"
    expect_error(lambda: compare.serialize_input(source, signed=False), "unsupported execution inputs")
    source["unsupported"].append("environment_field:unknown")
    expect_error(lambda: compare.serialize_input(source), "environment_field:unknown")


def test_complete_state_and_hashes_match_only_execution_scope():
    result = compare.compare_execution(case(), completed())
    assert result["classification"] == "execution_pass"
    assert result["scope"] == "execution_only"
    assert result["engine"] == "rocq_revm"
    assert result["fixture"] == {"name": "add11", "fork": "Cancun", "post_index": 0}
    assert result["full_eest_pass"] is False
    assert result["fixture_identity_verified"] is False
    assert result["authentication_verified"] is False
    assert result["differences"] == []


def test_authenticated_state_pass_still_requires_fixture_identity():
    result = compare.compare_execution(case(), completed(True))
    assert result["classification"] == "authenticated_state_pass"
    assert result["scope"] == "authenticated_state"
    assert result["authentication_verified"] is True
    assert result["fixture_identity_verified"] is False
    assert result["full_eest_pass"] is False


def test_authenticated_decoded_fields_are_checked_against_fixture():
    for field, value in (("caller", 123), ("nonce", 999), ("target", None), ("gas_price", 12),
                         ("value", 1), ("data", [1]), ("access_list", [[1, [2]]])):
        output = completed(True)
        output["authentication"]["transaction"][field] = value
        result = compare.compare_execution(case(), output)
        assert result["classification"] == "execution_mismatch"
        assert result["differences"][0]["field"] == "authenticated_transaction." + field
    source = case()
    source["transaction"]["caller"] = None
    source["unsupported"].append("sender_recovery_required")
    assert compare.compare_execution(source, completed(True))["classification"] == "authenticated_state_pass"


def test_sender_coinbase_and_target_balances_each_detect_mismatches():
    for index in range(3):
        output = completed()
        output["accounts"][index]["balance"] += 1
        result = compare.compare_execution(case(), output)
        assert result["classification"] == "execution_mismatch"
        assert result["differences"][0]["field"] == "balance"
        assert result["differences"][0]["address"] == output["accounts"][index]["address"]
        assert result["full_eest_pass"] is False


def test_all_account_fields_and_account_presence_are_checked():
    for field, value in (("nonce", 999), ("code", [0]), ("code_hash", 0),
                         ("storage", [[0, 3]]), ("transient_storage", [[1, 2]])):
        output = completed()
        output["accounts"][0][field] = value
        result = compare.compare_execution(case(), output)
        assert result["classification"] == "execution_mismatch"
        assert result["differences"][0]["field"] == field
    output = completed()
    output["accounts"].pop()
    assert compare.compare_execution(case(), output)["differences"][0]["field"] == "account_presence"
    output = completed()
    extra = copy.deepcopy(output["accounts"][0])
    extra["address"] = 1
    output["accounts"].append(extra)
    assert compare.compare_execution(case(), output)["differences"][0]["field"] == "account_presence"


def test_account_order_is_irrelevant_but_duplicates_are_invalid():
    output = completed()
    output["accounts"].reverse()
    assert compare.compare_execution(case(), output)["classification"] == "execution_pass"
    output["accounts"].append(copy.deepcopy(output["accounts"][0]))
    expect_error(lambda: compare.compare_execution(case(), output), "duplicate native account")
    output = completed()
    output["accounts"][0]["storage"] = [[0, 2], [0, 2]]
    expect_error(lambda: compare.compare_execution(case(), output), "duplicate native storage")


def test_supplied_roots_are_checked_even_with_explicit_post_accounts():
    for field in ("state_root", "logs_hash"):
        output = completed()
        output["commitments"][field][0] ^= 1
        result = compare.compare_execution(case(), output)
        assert result["classification"] == "execution_mismatch"
        assert result["differences"][0]["field"] == field


def test_hash_only_oracles_use_rocq_commitments():
    source = case()
    source["expectation"]["accounts"] = None
    assert compare.compare_execution(source, completed())["classification"] == "execution_pass"
    assert compare.compare_execution(source, completed(True))["classification"] == "authenticated_state_pass"
    output = completed(True)
    output["commitments"]["state_root"][0] ^= 1
    result = compare.compare_execution(source, output)
    assert result["classification"] == "execution_mismatch"
    assert result["differences"][0]["field"] == "state_root"
    source["expectation"]["state_root"] = None
    assert compare.compare_execution(source, completed())["reasons"] == ["state_oracle_missing"]


def test_non_rocq_and_malformed_commitment_hashes_are_rejected():
    for source in ("python", "geth", None):
        output = completed()
        output["commitments"]["source"] = source
        expect_error(lambda: compare.compare_execution(case(), output), "must come from Rocq")
    for value in ([], [0] * 31, [0] * 33, [256] * 32, [True] * 32, None):
        output = completed()
        output["commitments"]["state_root"] = value
        expect_error(lambda: compare.compare_execution(case(), output), "")


def rejected_case():
    source = fixture.load_case(FIXTURE_ROOT / "stEIP1559/tipTooHigh.json", "Cancun")
    output = other_result("Rejected", reason="PriorityFeeGreaterThanMaxFee", details=[])
    output["authentication"] = {"verified": True, "transaction": copy.deepcopy(source["transaction"])}
    output["accounts"] = copy.deepcopy(source["input"]["accounts"])
    output["commitments"] = {"source": "rocq", "state_root": source["expectation"]["state_root"],
                             "logs_hash": source["expectation"]["logs_hash"]}
    return source, output


def test_expected_handler_rejection_checks_authentication_and_state_oracles():
    source, output = rejected_case()
    result = compare.compare_execution(source, output)
    assert result["classification"] == "authenticated_state_pass", result
    assert result["full_eest_pass"] is False
    for field in ("state_root", "logs_hash"):
        bad = copy.deepcopy(output)
        bad["commitments"][field][0] ^= 1
        assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    output["authentication"] = {"verified": False, "transaction": None}
    assert compare.compare_execution(source, output)["classification"] == "unsupported"


def test_expected_rejection_rejects_wrong_reason_changed_accounts_and_missing_evidence():
    source, output = rejected_case()
    for kind in ("Malformed", "Incomplete", "Unsupported", "AuthenticationRejected"):
        fields = {"reason": "PriorityFeeGreaterThanMaxFee", "details": []} if kind in ("Unsupported", "AuthenticationRejected") else {}
        assert compare.compare_execution(source, other_result(kind, **fields))["classification"] != "authenticated_state_pass"
    bad = copy.deepcopy(output)
    bad["reason"] = "LackOfFunds"
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    bad = copy.deepcopy(output)
    bad["accounts"][0]["balance"] += 1
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    bad = copy.deepcopy(output)
    del bad["commitments"]
    expect_error(lambda: compare.compare_execution(source, bad), "exact fields")
    source["expectation"]["logs_hash"] = None
    assert compare.compare_execution(source, output)["reasons"] == ["logs_oracle_missing"]


def test_exception_alternatives_require_a_precisely_mapped_match():
    source, output = rejected_case()
    source["expectation"]["exception"] = "TransactionException.UNKNOWN|TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS"
    assert compare.compare_execution(source, output)["classification"] == "authenticated_state_pass"
    source["expectation"]["exception"] = "TransactionException.UNKNOWN_NONCE_RULE"
    assert compare.compare_execution(source, output)["reasons"] == ["transaction_exception_mapping_required"]


def test_incomplete_and_unknown_exception_mappings_remain_explicit():
    source = case()
    assert compare.compare_execution(source, other_result("Incomplete"))["classification"] == "incomplete"
    assert compare.compare_execution(source, other_result("Unsupported", reason="Delegation", details=[]))["classification"] == "unsupported"
    assert compare.compare_execution(source, other_result("Rejected", reason="NonceTooHigh", details=[]))["classification"] == "execution_mismatch"
    for exception in ("TR_InvalidV", "TR_InvalidR", "TR_InvalidS"):
        source["expectation"]["exception"] = exception
        output = other_result("AuthenticationRejected", reason="InvalidSignature", details=[])
        result = compare.compare_execution(source, output)
        assert result["reasons"] == ["transaction_exception_mapping_required"]
        assert result["full_eest_pass"] is False
    source = case()
    source["expectation"]["logs_hash"] = None
    assert compare.compare_execution(source, completed())["reasons"] == ["logs_oracle_missing"]


def test_authentication_failure_never_becomes_an_execution_pass():
    for reason, details in (("InvalidSignature", []), ("RecoveryFailed", []),
                            ("SenderMismatch", [1, 2]), ("ChainIdMismatch", [1, 2]),
                            ("MalformedRlp", []), ("MalformedFields", [])):
        output = other_result("AuthenticationRejected", reason=reason, details=details)
        result = compare.compare_execution(case(), output)
        assert result["classification"] == "authentication_mismatch"
        assert result["authentication_verified"] is False
        assert result["rejection"] == {"reason": reason, "details": details}
        assert result["full_eest_pass"] is False


def test_native_result_protocol_preserves_all_fields_and_rejections():
    output = completed(True)
    output["accounts"][0]["balance"] = 2 ** 256 - 1
    output["logs"] = [{"address": 6, "topics": [7, 8], "data": [9, 10]}]
    assert compare.parse_output(json.dumps(output)) == output
    for kind in ("Rejected", "AuthenticationRejected", "Unsupported"):
        rejection = other_result(kind, reason="Example", details=[53006, 53005])
        assert compare.parse_output(json.dumps(rejection)) == rejection


def test_malformed_authentication_records_are_rejected():
    for value in ({"verified": 1, "transaction": None}, {"verified": True, "transaction": None},
                  {"verified": False, "transaction": case()["transaction"]}, {}, None):
        output = completed()
        output["authentication"] = value
        expect_error(lambda: compare.parse_output(json.dumps(output)), "")
    output = other_result("AuthenticationRejected", reason="InvalidSignature", details=[])
    output["authentication"] = {"verified": True, "transaction": case()["transaction"]}
    expect_error(lambda: compare.parse_output(json.dumps(output)), "cannot be verified")


def test_malformed_wire_unresolved_execution_sender_and_fuel_fail_explicitly():
    for wire in ("", '{}', '{"protocol":1,"kind":"Incomplete"} {}',
                 '{"protocol":1,"kind":"Incomplete","kind":"Incomplete"}',
                 '{"protocol":true,"kind":"Incomplete"}', '{"protocol":1,"kind":"WrongKind"}'):
        expect_error(lambda: compare.parse_output(wire), "")
    output = completed()
    for value in (-1, True):
        output["gas"]["gas_used"] = value
        expect_error(lambda: compare.parse_output(json.dumps(output)), "nonnegative")
    source = case()
    source["transaction"]["caller"] = None
    expect_error(lambda: compare.serialize_input(source, signed=False), "nonnegative")
    source = case()
    source["fork"] = "UnsupportedFork"
    expect_error(lambda: compare.serialize_input(source), "outside")
    expect_error(lambda: compare.serialize_input(case(), compare.MAX_FUEL + 1), "fuel exceeds limit")


def test_other_engine_results_cannot_count_as_revm_execution():
    for engine in ("go_rocq", "geth", "other", None):
        output = completed()
        output["engine"] = engine
        expect_error(lambda: compare.parse_output(json.dumps(output)), "engine must be rocq_revm")
        expect_error(lambda: compare.compare_execution(case(), output), "engine must be rocq_revm")


def test_authorization_echo_requires_correct_shape_and_rust_widths():
    transaction = case()["transaction"]
    transaction.update(tx_type=4, authorization_list=[{
        "chain_id": (1 << 256) - 1, "address": (1 << 160) - 1, "nonce": (1 << 64) - 1,
        "y_parity": 255, "r": (1 << 256) - 1, "s": (1 << 256) - 1}])
    compare.validate_transaction(transaction)
    for field in transaction["authorization_list"][0]:
        changed = copy.deepcopy(transaction)
        changed["authorization_list"][0][field] += 1
        expect_error(lambda: compare.validate_transaction(changed), "Rust width")
    transaction["authorization_list"] = None
    expect_error(lambda: compare.validate_transaction(transaction), "requires authorization list")
    transaction.update(tx_type=2, authorization_list=[])
    expect_error(lambda: compare.validate_transaction(transaction), "requires type 4")


def test_empty_authorization_rejection_requires_type_fork_and_empty_list():
    source, output = rejected_case()
    source["fork"] = "Osaka"
    source["transaction"].update(tx_type=4, authorization_list=[])
    output.update(reason="EmptyAuthorizationList", details=[])
    assert compare.mapped_rejection_prerequisites(source, output)
    for key, value in (("tx_type", 2), ("target", None), ("authorization_list", [{}])):
        bad = copy.deepcopy(source)
        bad["transaction"][key] = value
        assert not compare.mapped_rejection_prerequisites(bad, output)
    source["fork"] = "Cancun"
    assert not compare.mapped_rejection_prerequisites(source, output)
    source["fork"] = "Osaka"
    output["details"] = [0]
    assert not compare.mapped_rejection_prerequisites(source, output)


def test_type4_creation_rejection_requires_exact_decoded_envelope():
    from transaction_fixture_test import rlp
    source = case()
    source["fork"] = "Osaka"
    fields = [1, 0, 1, 10, 50000, b"", 0, b"", [], [], 0, 1, 1]
    raw = b"\x04" + rlp(fields)
    envelope = fixture.signed_envelope(raw)
    source["transaction"].update({key: value for key, value in envelope.items()
                                  if key not in {"supported", "signature"}})
    name = "TransactionException.TYPE_4_TX_CONTRACT_CREATION"
    source["expectation"].update(txbytes=list(raw), exception=name)
    output = other_result("AuthenticationRejected", reason="MalformedFields", details=[])
    assert compare.validated_authentication_rejection(source, output) == name
    for reason in ("InvalidRlp", "InvalidSignature", "EmptyAuthorizationList"):
        bad = copy.deepcopy(output)
        bad["reason"] = reason
        assert compare.validated_authentication_rejection(source, bad) is None
    bad = copy.deepcopy(source)
    bad["transaction"]["nonce"] += 1
    assert compare.validated_authentication_rejection(bad, output) is None
    for target in (b"\x00" * 20, b"\x00"):
        fields[5] = target
        bad = copy.deepcopy(source)
        bad["expectation"]["txbytes"] = list(b"\x04" + rlp(fields))
        assert compare.validated_authentication_rejection(bad, output) is None
    fields[5] = b""
    fields[4] = 1 << 64
    bad = copy.deepcopy(source)
    bad["expectation"]["txbytes"] = list(b"\x04" + rlp(fields))
    assert compare.validated_authentication_rejection(bad, output) is None


def test_type3_creation_rejection_requires_exact_decoded_envelope():
    from transaction_fixture_test import rlp
    source = case()
    source["fork"] = "Osaka"
    fields = [1, 0, 1, 10, 50000, b"", 0, b"", [], 1, [b"\x01" + b"\x00" * 31], 0, 1, 1]
    raw = b"\x03" + rlp(fields)
    envelope = fixture.signed_envelope(raw)
    source["transaction"].update({key: value for key, value in envelope.items()
                                  if key not in {"supported", "signature"}})
    name = "TransactionException.TYPE_3_TX_CONTRACT_CREATION"
    source["expectation"].update(txbytes=list(raw), exception=name)
    output = other_result("AuthenticationRejected", reason="MalformedFields", details=[])
    assert compare.validated_authentication_rejection(source, output) == name
    for reason in ("MalformedRlp", "InvalidSignature", "TransactionTypeNotSupported"):
        bad = copy.deepcopy(output)
        bad["reason"] = reason
        assert compare.validated_authentication_rejection(source, bad) is None
    for key, value in (("nonce", 1), ("target", 0), ("gas_price", 11)):
        bad = copy.deepcopy(source)
        bad["transaction"][key] = value
        assert compare.validated_authentication_rejection(bad, output) is None
    for index, value in ((4, 1 << 64), (3, 1 << 256), (5, b"\x00"),
                         (5, b"\x00" * 20), (10, [b"\x01"])):
        changed = list(fields)
        changed[index] = value
        bad = copy.deepcopy(source)
        bad["expectation"]["txbytes"] = list(b"\x03" + rlp(changed))
        assert compare.validated_authentication_rejection(bad, output) is None
    bad = copy.deepcopy(output)
    bad["details"] = [0]
    assert compare.validated_authentication_rejection(source, bad) is None


def test_osaka_cap_rejection_requires_exact_limit_and_details():
    source, output = rejected_case()
    source["fork"] = "Osaka"
    source["expectation"]["exception"] = "TransactionException.GAS_LIMIT_EXCEEDS_MAXIMUM"
    source["transaction"]["gas_limit"] = (1 << 24) + 1
    output.update(reason="GasLimitAboveCap", details=[(1 << 24) + 1, 1 << 24])
    output["authentication"]["transaction"] = copy.deepcopy(source["transaction"])
    assert compare.compare_execution(source, output)["classification"] == "authenticated_state_pass"
    for fork in ("Cancun", "Prague"):
        bad = copy.deepcopy(source)
        bad["fork"] = fork
        assert not compare.mapped_rejection_prerequisites(bad, output)
    for limit in (1 << 24, 1 << 64):
        bad = copy.deepcopy(source)
        bad["transaction"]["gas_limit"] = limit
        rejection = dict(output, details=[limit, 1 << 24])
        assert not compare.mapped_rejection_prerequisites(bad, rejection)
    bad = copy.deepcopy(output)
    bad["details"][1] += 1
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    bad = dict(output, reason="GasLimitAboveBlock")
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"


def test_floor_rejections_require_exact_cost_fork_and_intrinsic_precedence():
    source, output = rejected_case()
    source["transaction"].update(tx_type=1, data=[1] * 134, gas_limit=26359,
                                 access_list=[], authorization_list=None, target=1)
    output.update(reason="FloorGasTooHigh", details=[26360, 26359])
    output["authentication"]["transaction"] = copy.deepcopy(source["transaction"])
    for fork in ("Prague", "Osaka"):
        source["fork"] = fork
        for exception in ("INTRINSIC_GAS_TOO_LOW", "INTRINSIC_GAS_BELOW_FLOOR_GAS_COST"):
            source["expectation"]["exception"] = "TransactionException." + exception
            assert compare.compare_execution(source, output)["classification"] == "authenticated_state_pass"
    bad = copy.deepcopy(source)
    bad["fork"] = "Cancun"
    assert not compare.mapped_rejection_prerequisites(bad, output)
    for details in ([26361, 26359], [26360, 26358], []):
        bad = dict(output, details=details)
        assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"
    for limit in (23143, 26360):
        bad = copy.deepcopy(source)
        bad["transaction"]["gas_limit"] = limit
        assert not compare.mapped_rejection_prerequisites(bad, dict(output, details=[26360, limit]))
    # Access lists, creation and authorizations can make intrinsic gas fail first.
    for fields in ({"access_list": [[1, [0]]]}, {"target": None},
                   {"tx_type": 4, "authorization_list": [{}]}):
        bad = copy.deepcopy(source)
        bad["transaction"].update(fields)
        assert not compare.mapped_rejection_prerequisites(bad, output)
    bad = dict(output, reason="IntrinsicGasTooHigh")
    assert compare.compare_execution(source, bad)["classification"] == "execution_mismatch"


def test_payment_overflow_requires_both_fixture_and_rust_product_overflow():
    source, output = rejected_case()
    source["transaction"].update(gas_limit=16777216,
        gas_price=5513909011300771210646237381366090850155713555506693525688456381329244268)
    source["expectation"]["exception"] = "TransactionException.GASLIMIT_PRICE_PRODUCT_OVERFLOW"
    output.update(reason="PaymentOverflow", details=[])
    output["authentication"]["transaction"] = copy.deepcopy(source["transaction"])
    assert compare.compare_execution(source, output)["classification"] == "authenticated_state_pass"
    for limit, price in ((1, 1), (50000, 1 << 128), (1 << 64, 1 << 255),
                         (16777216, 1 << 256), (-1, 1), (1, -1)):
        bad = copy.deepcopy(source)
        bad["transaction"].update(gas_limit=limit, gas_price=price)
        assert not compare.mapped_rejection_prerequisites(bad, output)
    assert not compare.mapped_rejection_prerequisites(source, dict(output, details=[1]))
    bad = copy.deepcopy(source)
    bad["transaction"].update(gas_limit=1, gas_price=1, value=(1 << 256) - 1)
    assert not compare.mapped_rejection_prerequisites(bad, output)


TESTS = tuple(value for name, value in tuple(globals().items()) if name.startswith("test_"))

if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} transaction bridge/comparison tests passed")
