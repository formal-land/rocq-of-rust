"""Parser regressions including the unmodified historical add11 fixture."""

import copy
import json
import os
from pathlib import Path

import transaction_fixture as adapter


FIXTURE_ROOT = Path(os.environ.get("REVM_FIXTURE_ROOT", Path.cwd() / "tests/revm-testdata/GeneralStateTests"))
ADD11 = FIXTURE_ROOT / "stExample/add11.json"
ACCESS_LIST = FIXTURE_ROOT / "stExample/accessListExample.json"
SENDER = "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"
TARGET = "0x095e7baea6a6c7c4c2dfeb977efac326af552d87"
COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"


def fixture():
    return json.loads(ADD11.read_text())


def unsigned_fixture():
    document = fixture()
    del document["add11"]["post"]["Cancun"][0]["txbytes"]
    return document


def normalize(document):
    return adapter.normalize_case(document, "Cancun")


def expect_error(function, message):
    try:
        function()
    except adapter.FixtureError as error:
        assert message in str(error), (message, str(error))
    else:
        raise AssertionError(f"expected FixtureError containing {message!r}")


def rlp(value):
    if isinstance(value, int):
        value = value.to_bytes((value.bit_length() + 7) // 8, "big")
    if isinstance(value, list):
        payload = b"".join(rlp(child) for child in value)
        short_base, long_base = 192, 247
    else:
        if len(value) == 1 and value[0] < 128:
            return value
        payload = value
        short_base, long_base = 128, 183
    if len(payload) < 56:
        return bytes([short_base + len(payload)]) + payload
    length = len(payload).to_bytes((len(payload).bit_length() + 7) // 8, "big")
    return bytes([long_base + len(length)]) + length + payload


def test_historical_add11_retains_every_account_and_exact_transaction():
    case = adapter.load_case(ADD11, "Cancun")
    assert case["schema_version"] == 1
    assert case["unsupported"] == ["authentication_verification_required"]
    tx = case["transaction"]
    assert tx["caller"] == int(SENDER, 16)
    assert tx["target"] == int(TARGET, 16)
    assert (tx["nonce"], tx["gas_limit"], tx["gas_price"], tx["value"], tx["data"]) == (0, 400000, 10, 100000, [])
    assert tx["chain_id"] is None  # The actual signed v is 27, despite config.chainid=1.
    assert case["input"]["chain_id"] == 1
    before = {account["address"]: account for account in case["input"]["accounts"]}
    after = {account["address"]: account for account in case["expectation"]["accounts"]}
    assert set(before) == set(after) == {int(SENDER, 16), int(TARGET, 16), int(COINBASE, 16)}
    assert before[int(SENDER, 16)]["balance"] == 1000000000000000000
    assert after[int(SENDER, 16)]["balance"] == 999999999999468880
    assert after[int(SENDER, 16)]["nonce"] == 1
    assert after[int(TARGET, 16)]["balance"] == 1000000000000100000
    assert after[int(TARGET, 16)]["storage"] == [[0, 2]]
    assert after[int(COINBASE, 16)]["nonce"] == 1
    assert after[int(COINBASE, 16)]["balance"] == 0
    assert case["authentication"]["signature_recovery_verified"] is False
    assert case["authentication"]["caller_source"] == "fixture_sender"
    assert case["authentication"]["envelope_signature"]["v"] == 27
    assert len(case["expectation"]["txbytes"]) == 101
    assert case["input"]["block"]["blob_base_fee"] == 1
    json.dumps(case)  # The boundary has no dataclasses, bytes, or opaque values.


def test_historical_access_lists_use_selected_data_index_and_signed_chain_id():
    first = adapter.load_case(ACCESS_LIST, "Cancun", 0)
    second = adapter.load_case(ACCESS_LIST, "Cancun", 1)
    assert first["transaction"]["tx_type"] == second["transaction"]["tx_type"] == 1
    assert first["transaction"]["chain_id"] == second["transaction"]["chain_id"] == 1
    assert first["transaction"]["access_list"] == [[int(TARGET, 16), [0, 1]], [int("19" + TARGET[4:], 16), [0]]]
    assert len(second["transaction"]["access_list"]) == 1
    assert second["indexes"] == {"data": 1, "gas": 0, "value": 0}
    assert len(second["input"]["accounts"]) == 2
    assert second["expectation"]["accounts"] is not None


def test_selected_indexes_are_independent_and_bool_is_not_an_index():
    document = unsigned_fixture()
    test = document["add11"]
    test["transaction"]["data"] = ["0x00", "0xabcd"]
    test["transaction"]["gasLimit"] = ["0x01", "0x010203"]
    test["transaction"]["value"] = ["0x05", "0x06"]
    test["post"]["Cancun"][0]["indexes"] = {"data": 1, "gas": 1, "value": 0}
    tx = normalize(document)["transaction"]
    assert (tx["data"], tx["gas_limit"], tx["value"]) == ([171, 205], 66051, 5)
    test["post"]["Cancun"][0]["indexes"]["data"] = True
    expect_error(lambda: normalize(document), "invalid selected index")


def test_null_access_list_is_legacy_empty_access_list_is_typed():
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    raw["data"] = ["0x", "0x"]
    raw["accessLists"] = [None, []]
    assert normalize(document)["transaction"]["tx_type"] == 0
    document["add11"]["post"]["Cancun"][0]["indexes"]["data"] = 1
    case = normalize(document)
    assert case["transaction"]["tx_type"] == 1
    assert case["transaction"]["access_list"] == []
    assert case["transaction"]["chain_id"] is None  # Preserve MissingChainId rejection.


def test_duplicate_access_list_entries_are_preserved_for_intrinsic_cost():
    document = unsigned_fixture()
    item = {"address": TARGET, "storageKeys": ["0x" + "00" * 32, "0x" + "00" * 32]}
    document["add11"]["transaction"]["accessLists"] = [[item, copy.deepcopy(item)]]
    assert normalize(document)["transaction"]["access_list"] == [[int(TARGET, 16), [0, 0]], [int(TARGET, 16), [0, 0]]]


def test_create_and_absent_call_target_account_remain_executable_shapes():
    document = unsigned_fixture()
    document["add11"]["transaction"]["to"] = ""
    assert normalize(document)["transaction"]["target"] is None
    document["add11"]["transaction"]["to"] = "0x"
    assert normalize(document)["transaction"]["target"] is None
    document["add11"]["transaction"]["to"] = "0x" + "11" * 20
    assert normalize(document)["transaction"]["target"] == int("11" * 20, 16)


def test_dynamic_fee_caps_and_invalid_priority_are_retained():
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    del raw["gasPrice"]
    raw.update(maxFeePerGas="0x02", maxPriorityFeePerGas="0x03")
    tx = normalize(document)["transaction"]
    assert (tx["tx_type"], tx["gas_price"], tx["max_priority_fee"]) == (2, 2, 3)
    assert tx["gas_price"] < normalize(document)["input"]["block"]["base_fee"]
    assert tx["chain_id"] is None


def test_signed_typed_fee_cap_chain_id_and_duplicate_list_crosschecks():
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    del raw["gasPrice"]
    raw.update(maxFeePerGas="0x14", maxPriorityFeePerGas="0x03", accessLists=[[]])
    fields = [7, 0, 3, 20, 400000, bytes.fromhex(TARGET[2:]), 100000, b"", [], 0, 1, 2]
    document["add11"]["post"]["Cancun"][0]["txbytes"] = "0x" + (b"\x02" + rlp(fields)).hex()
    tx = normalize(document)["transaction"]
    assert (tx["tx_type"], tx["chain_id"], tx["gas_price"], tx["max_priority_fee"]) == (2, 7, 20, 3)
    assert normalize(document)["input"]["chain_id"] == 1  # Preserve chain-id rejection.
    raw["chainId"] = "0x01"
    expect_error(lambda: normalize(document), "chainId disagrees")


def test_eip155_chain_id_is_derived_and_never_copied_from_configuration():
    fields = [0, 10, 400000, bytes.fromhex(TARGET[2:]), 100000, b"", 39, 1, 2]
    document = fixture()
    document["add11"]["post"]["Cancun"][0]["txbytes"] = "0x" + rlp(fields).hex()
    assert normalize(document)["transaction"]["chain_id"] == 2
    del document["add11"]["post"]["Cancun"][0]["txbytes"]
    assert normalize(document)["transaction"]["chain_id"] is None


def test_signed_envelope_mismatch_is_not_ignored():
    document = fixture()
    document["add11"]["transaction"]["nonce"] = "0x01"
    expect_error(lambda: normalize(document), "nonce disagrees")


def test_invalid_rlp_is_error_or_explicit_expected_exception_boundary():
    for invalid in (b"", b"\x81\x01", b"\xb8\x01\x80", b"\xf8\x00", b"\xc1", b"\xc0\x80"):
        expect_error(lambda: adapter.decode_rlp(invalid), "RLP")
    document = fixture()
    post = document["add11"]["post"]["Cancun"][0]
    post["txbytes"] = "0xc1"
    expect_error(lambda: normalize(document), "RLP")
    post["expectException"] = "TransactionException.INVALID_RLP"
    case = normalize(document)
    assert case["expectation"]["exception"] == "TransactionException.INVALID_RLP"
    assert "invalid_signed_envelope" in case["unsupported"]
    assert "authentication_verification_required" in case["unsupported"]
    assert case["expectation"]["txbytes"] == [193]
    assert case["authentication"]["envelope_error"]


def test_unsigned_source_also_cannot_claim_complete_authentication():
    case = normalize(unsigned_fixture())
    assert case["expectation"]["txbytes"] is None
    assert case["transaction"]["caller"] == int(SENDER, 16)
    assert case["authentication"]["requires_verification"] is True
    assert case["authentication"]["complete_pass_requires_authentication"] is True
    assert "authentication_verification_required" in case["unsupported"]


def test_signature_failure_is_not_a_passable_execution_case():
    document = fixture()
    document["add11"]["post"]["Cancun"][0]["expectException"] = "TransactionException.INVALID_SIGNATURE_VRS"
    case = normalize(document)
    assert case["authentication"]["requires_verification"] is True
    assert "authentication_verification_required" in case["unsupported"]


def test_missing_sender_needs_recovery_without_using_prestate_guess():
    document = fixture()
    del document["add11"]["transaction"]["sender"]
    case = normalize(document)
    assert case["transaction"]["caller"] is None
    assert "sender_recovery_required" in case["unsupported"]
    assert case["authentication"]["caller_source"] == "unresolved"
    assert len(case["input"]["accounts"]) == 3


def test_hash_only_expected_post_state_stays_hash_only():
    document = fixture()
    del document["add11"]["post"]["Cancun"][0]["state"]
    case = normalize(document)
    assert case["expectation"]["accounts"] is None
    assert len(case["expectation"]["state_root"]) == 32
    assert len(case["expectation"]["logs_hash"]) == 32


def test_blobs_authorizations_and_unknown_semantics_are_explicit():
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    del raw["gasPrice"]
    raw.update(maxFeePerGas="0x14", maxPriorityFeePerGas="0x03", maxFeePerBlobGas="0x02", blobVersionedHashes=[])
    case = normalize(document)
    assert "transaction_type:3" not in case["unsupported"]
    assert case["transaction"]["blob_hashes"] == []
    assert case["transaction"]["max_fee_per_blob_gas"] == 2
    raw["authorizationList"] = [{"chainId": "0x00", "nonce": "0x01", "address": TARGET,
                                 "v": "0x00", "r": "0x01", "s": "0x02"}]
    raw["novelSemantics"] = "0xdead"
    case = normalize(document)
    assert "transaction_type:4" not in case["unsupported"]
    assert "transaction_field:novelSemantics" in case["unsupported"]
    assert case["source"]["transaction"]["novelSemantics"] == "0xdead"
    assert case["transaction"]["authorization_list"] == [{"chain_id": 0, "nonce": 1,
        "address": int(TARGET, 16), "y_parity": 0, "r": 1, "s": 2}]


def test_wrong_width_lists_duplicate_account_keys_and_storage_keys_fail():
    document = unsigned_fixture()
    document["add11"]["transaction"]["accessLists"] = [[] , []]
    expect_error(lambda: normalize(document), "match data array length")
    document = unsigned_fixture()
    document["add11"]["transaction"]["accessLists"] = [[{"address": "0x01", "storageKeys": []}]]
    expect_error(lambda: normalize(document), "exactly 20 bytes")
    document = fixture()
    document["add11"]["pre"][TARGET.upper().replace("0X", "0x")] = copy.deepcopy(document["add11"]["pre"][TARGET])
    expect_error(lambda: normalize(document), "duplicate numeric account")
    document = fixture()
    document["add11"]["pre"][TARGET]["storage"] = {"0x00": "0x01", "0x0": "0x02"}
    expect_error(lambda: normalize(document), "duplicate numeric storage")


def test_semantic_invalid_values_and_transaction_exceptions_are_preserved():
    document = unsigned_fixture()
    document["add11"]["transaction"]["nonce"] = hex(1 << 64)
    document["add11"]["post"]["Cancun"][0]["expectException"] = "TransactionException.NONCE_OVERFLOW"
    case = normalize(document)
    assert case["transaction"]["nonce"] == 1 << 64
    assert case["expectation"]["exception"] == "TransactionException.NONCE_OVERFLOW"
    assert case["expectation"]["accounts"] is not None


def test_keccak_vectors_and_blob_price_integer_division():
    vectors = {
        b"": "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        b"\x00": "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a",
        b"abc": "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
    }
    for data, expected in vectors.items():
        assert adapter.keccak256(data).hex() == expected
    assert adapter.fake_exponential(0, 3338477) == 1
    assert adapter.fake_exponential(3338477, 3338477) == 2
    assert adapter.fake_exponential(6676954, 3338477) == 7
    expect_error(lambda: adapter.fake_exponential(1, 0), "positive")


def test_case_selection_never_silently_chooses_a_post_or_test():
    document = fixture()
    document["other"] = copy.deepcopy(document["add11"])
    expect_error(lambda: normalize(document), "choose test_name")
    assert adapter.normalize_case(document, "Cancun", test_name="other")["name"] == "other"
    expect_error(lambda: adapter.normalize_case(document, "Cancun", test_name="missing"), "no test")
    expect_error(lambda: adapter.load_case(ACCESS_LIST, "Cancun"), "choose post_index")
    expect_error(lambda: adapter.load_case(ACCESS_LIST, "Cancun", -1), "invalid selected index")
    expect_error(lambda: adapter.load_case(ACCESS_LIST, "Cancun", True), "invalid selected index")


def test_source_retained_without_aliasing_or_mutation():
    document = fixture()
    original = copy.deepcopy(document)
    case = normalize(document)
    assert document == original
    case["source"]["transaction"]["value"][0] = "0xdead"
    assert document == original


def test_custom_blob_schedule_and_previous_block_hash_are_preserved():
    document = unsigned_fixture()
    test = document["add11"]
    test["config"]["blobSchedule"]["Cancun"] = {
        "baseFeeUpdateFraction": "0x01", "max": "0x02", "target": "0x01",
    }
    test["env"]["currentExcessBlobGas"] = "0x02"
    test["env"]["previousHash"] = "0x" + "ab" * 32
    case = normalize(document)
    assert case["input"]["max_blobs_per_tx"] == 2
    assert case["input"]["block"]["blob_base_fee"] == 6
    assert case["input"]["block"]["hashes"] == [[0, int("ab" * 32, 16)]]
    assert case["input"]["block"]["use_state_test_hashes"] is True


def test_missing_randao_or_excess_is_not_fabricated():
    document = unsigned_fixture()
    test = document["add11"]
    del test["env"]["currentRandom"]
    del test["env"]["currentExcessBlobGas"]
    case = normalize(document)
    assert case["input"]["block"]["previous_randao"] is None
    assert case["input"]["excess_blob_gas"] is None


def test_non_string_expected_exception_is_malformed():
    for value in (False, 0, [], {}):
        document = unsigned_fixture()
        document["add11"]["post"]["Cancun"][0]["expectException"] = value
        expect_error(lambda: normalize(document), "must be a string")


def test_semantic_environment_extras_are_reported_but_metadata_is_harmless():
    document = unsigned_fixture()
    test = document["add11"]
    test["env"]["novelSemantics"] = "0x01"
    test["transaction"]["_info"] = {"comment": "harmless"}
    case = normalize(document)
    assert "environment_field:novelSemantics" in case["unsupported"]
    assert "transaction_field:_info" not in case["unsupported"]
    assert case["source"]["env"]["novelSemantics"] == "0x01"

def test_every_signed_envelope_requires_authentication_without_exception_matching():
    document = fixture()
    for exception in (None, "TR_InvalidV", "TR_InvalidR", "TR_InvalidS", "arbitrary_future_error"):
        post = document["add11"]["post"]["Cancun"][0]
        if exception is None:
            post.pop("expectException", None)
        else:
            post["expectException"] = exception
        case = normalize(document)
        assert case["authentication"]["requires_verification"] is True
        assert case["authentication"]["complete_pass_requires_authentication"] is True
        assert case["authentication"]["signature_recovery_verified"] is False
        assert "authentication_verification_required" in case["unsupported"]


def test_invalid_v_r_s_remain_authentication_boundaries_with_raw_values():
    for exception, v, r, s in (("TR_InvalidV", 29, 1, 2), ("TR_InvalidR", 27, 0, 2),
                               ("TR_InvalidS", 27, 1, 0)):
        document = fixture()
        fields = [0, 10, 400000, bytes.fromhex(TARGET[2:]), 100000, b"", v, r, s]
        post = document["add11"]["post"]["Cancun"][0]
        post["txbytes"] = "0x" + rlp(fields).hex()
        post["expectException"] = exception
        case = normalize(document)
        assert case["expectation"]["exception"] == exception
        assert case["authentication"]["envelope_signature"] == {"v": v, "r": r, "s": s}
        assert case["authentication"]["requires_verification"] is True
        assert "authentication_verification_required" in case["unsupported"]


def blob_fixture(target=bytes.fromhex(TARGET[2:])):
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    del raw["gasPrice"]
    hashes = [b"\x01" + b"\x00" * 31, b"\x01" + b"\x11" * 31]
    raw.update(maxFeePerGas="0x14", maxPriorityFeePerGas="0x03", accessLists=[[]],
               maxFeePerBlobGas="0x05", blobVersionedHashes=["0x" + value.hex() for value in hashes],
               to="0x" + target.hex())
    fields = [7, 0, 3, 20, 400000, target, 100000, b"", [], 5, hashes, 0, 1, 2]
    document["add11"]["post"]["Cancun"][0]["txbytes"] = "0x" + (b"\x03" + rlp(fields)).hex()
    return document, fields


def test_type3_signed_envelope_preserves_chain_id_fee_cap_and_blob_order():
    document, fields = blob_fixture()
    case = normalize(document)
    tx = case["transaction"]
    assert tx["tx_type"] == 3
    assert tx["chain_id"] == 7
    assert case["input"]["chain_id"] == 1
    assert (tx["gas_price"], tx["max_priority_fee"], tx["max_fee_per_blob_gas"]) == (20, 3, 5)
    assert tx["blob_hashes"] == [int.from_bytes(value, "big") for value in fields[10]]
    assert tx["blob_hashes"][0] != tx["blob_hashes"][1]
    assert case["canonical_envelope"]["blob_creation_forbidden"] is False
    assert case["unsupported"] == ["authentication_verification_required"]


def test_type3_signed_fee_and_blob_hash_mismatches_fail():
    document, _ = blob_fixture()
    document["add11"]["transaction"]["maxFeePerBlobGas"] = "0x06"
    expect_error(lambda: normalize(document), "max_fee_per_blob_gas disagrees")
    document, _ = blob_fixture()
    document["add11"]["transaction"]["blobVersionedHashes"].reverse()
    expect_error(lambda: normalize(document), "blob_hashes disagrees")
    document, _ = blob_fixture()
    document["add11"]["transaction"]["blobVersionedHashes"] = []
    expect_error(lambda: normalize(document), "blob_hashes disagrees")


def test_type3_malformed_envelope_blob_field_shapes_fail():
    _, fields = blob_fixture()
    expect_error(lambda: adapter.signed_envelope(b"\x03" + rlp(fields[:-1])), "14 fields")
    fields[10] = b"\x00" * 32
    expect_error(lambda: adapter.signed_envelope(b"\x03" + rlp(fields)), "must be a list")
    fields[10] = [b"\x00" * 31]
    expect_error(lambda: adapter.signed_envelope(b"\x03" + rlp(fields)), "32 bytes")
    fields[10] = [b"\x00" * 33]
    expect_error(lambda: adapter.signed_envelope(b"\x03" + rlp(fields)), "32 bytes")
    fields[10] = [[b"\x00" * 32]]
    expect_error(lambda: adapter.signed_envelope(b"\x03" + rlp(fields)), "32 bytes")


def test_type3_semantic_invalid_empty_or_wrong_version_hashes_are_preserved():
    for hashes in ([], [b"\x02" + b"\x00" * 31]):
        document, fields = blob_fixture()
        fields[10] = hashes
        raw = document["add11"]["transaction"]
        raw["blobVersionedHashes"] = ["0x" + value.hex() for value in hashes]
        document["add11"]["post"]["Cancun"][0]["txbytes"] = "0x" + (b"\x03" + rlp(fields)).hex()
        tx = normalize(document)["transaction"]
        assert tx["blob_hashes"] == [int.from_bytes(value, "big") for value in hashes]
        assert tx["tx_type"] == 3


def test_blob_creation_preserves_native_execution_shape_and_canonical_rejection_boundary():
    document, fields = blob_fixture(b"")
    document["add11"]["post"]["Cancun"][0]["expectException"] = "TR_BlobTxContractCreation"
    case = normalize(document)
    assert case["transaction"]["target"] is None
    assert case["transaction"]["tx_type"] == 3
    assert case["transaction"]["blob_hashes"] == [int.from_bytes(value, "big") for value in fields[10]]
    assert case["canonical_envelope"]["blob_creation_forbidden"] is True
    assert "canonical_blob_creation_validation_required" in case["unsupported"]
    assert "authentication_verification_required" in case["unsupported"]
    assert case["expectation"]["exception"] == "TR_BlobTxContractCreation"



def historical_case(fork):
    document = unsigned_fixture()
    document["add11"]["post"][fork] = document["add11"]["post"]["Cancun"]
    return document


def test_all_pinned_forks_reach_native_semantic_gate():
    for fork in adapter.SUPPORTED_FORKS:
        case = adapter.normalize_case(historical_case(fork), fork)
        assert f"fork:{fork}" not in case["unsupported"]


def test_pre_london_does_not_charge_supplied_base_fee():
    case = adapter.normalize_case(historical_case("Berlin"), "Berlin")
    assert case["input"]["block"]["base_fee"] == 0


def test_pre_london_missing_base_fee_is_accepted():
    document = historical_case("Berlin")
    del document["add11"]["env"]["currentBaseFee"]
    assert "base_fee_not_supplied" not in adapter.normalize_case(document, "Berlin")["unsupported"]


def test_london_requires_base_fee():
    document = historical_case("London")
    del document["add11"]["env"]["currentBaseFee"]
    assert "base_fee_not_supplied" in adapter.normalize_case(document, "London")["unsupported"]


def test_randao_activates_at_paris():
    for fork in ("Berlin", "London", "Paris", "Shanghai"):
        case = adapter.normalize_case(historical_case(fork), fork)
        assert (case["input"]["block"]["previous_randao"] is None) == (fork in ("Berlin", "London"))


def test_blob_environment_activates_at_cancun():
    for fork in ("Berlin", "London", "Paris", "Shanghai"):
        case = adapter.normalize_case(historical_case(fork), fork)
        assert case["input"]["block"]["blob_base_fee"] == 0
        assert case["input"]["excess_blob_gas"] is None
        assert case["input"]["max_blobs_per_tx"] is None

def test_type4_signed_authorizations_are_crosschecked():
    document = unsigned_fixture()
    raw = document["add11"]["transaction"]
    del raw["gasPrice"]
    raw.update(maxFeePerGas="0x14", maxPriorityFeePerGas="0x03", chainId="0x01",
               authorizationList=[{"chainId": "0x01", "address": TARGET, "nonce": "0x00",
                                   "v": "0x01", "r": "0x02", "s": "0x03", "signer": SENDER}])
    auth = [1, bytes.fromhex(TARGET[2:]), 0, 1, 2, 3]
    fields = [1, 0, 3, 20, 400000, bytes.fromhex(TARGET[2:]), 100000, b"", [], [auth], 0, 1, 2]
    document["add11"]["post"]["Cancun"][0]["txbytes"] = "0x" + (b"\x04" + rlp(fields)).hex()
    parsed = normalize(document)
    assert parsed["transaction"]["authorization_list"] == [dict(zip(
        ("chain_id", "address", "nonce", "y_parity", "r", "s"), (1, int(TARGET, 16), 0, 1, 2, 3)))]
    raw["authorizationList"][0]["nonce"] = "0x01"
    expect_error(lambda: normalize(document), "authorization_list disagrees")


def test_type4_malformed_authorizations_fail_and_invalid_signatures_are_preserved():
    fields = [1, 0, 3, 20, 400000, bytes.fromhex(TARGET[2:]), 0, b"", [], [], 0, 1, 2]
    assert adapter.signed_envelope(b"\x04" + rlp(fields))["authorization_list"] == []
    fields[9] = [[1, bytes.fromhex(TARGET[2:]), (1 << 64) - 1, 2, 0, 0]]
    assert adapter.signed_envelope(b"\x04" + rlp(fields))["authorization_list"][0]["y_parity"] == 2
    fields[9][0][1] = b"\x00" * 19
    expect_error(lambda: adapter.signed_envelope(b"\x04" + rlp(fields)), "20 bytes")
    fields[9] = [[]]
    expect_error(lambda: adapter.signed_envelope(b"\x04" + rlp(fields)), "six fields")
    fields[9] = b""
    expect_error(lambda: adapter.signed_envelope(b"\x04" + rlp(fields)), "must be a list")
    expect_error(lambda: adapter.normalize_authorizations([{"chainId": "0x01", "v": "0x00", "yParity": "0x01"}]), "disagree")


TESTS = (
    test_type4_signed_authorizations_are_crosschecked,
    test_type4_malformed_authorizations_fail_and_invalid_signatures_are_preserved,
    test_all_pinned_forks_reach_native_semantic_gate,
    test_pre_london_does_not_charge_supplied_base_fee,
    test_pre_london_missing_base_fee_is_accepted,
    test_london_requires_base_fee,
    test_randao_activates_at_paris,
    test_blob_environment_activates_at_cancun,

    test_historical_add11_retains_every_account_and_exact_transaction,
    test_historical_access_lists_use_selected_data_index_and_signed_chain_id,
    test_selected_indexes_are_independent_and_bool_is_not_an_index,
    test_null_access_list_is_legacy_empty_access_list_is_typed,
    test_duplicate_access_list_entries_are_preserved_for_intrinsic_cost,
    test_create_and_absent_call_target_account_remain_executable_shapes,
    test_dynamic_fee_caps_and_invalid_priority_are_retained,
    test_signed_typed_fee_cap_chain_id_and_duplicate_list_crosschecks,
    test_eip155_chain_id_is_derived_and_never_copied_from_configuration,
    test_signed_envelope_mismatch_is_not_ignored,
    test_invalid_rlp_is_error_or_explicit_expected_exception_boundary,
    test_signature_failure_is_not_a_passable_execution_case,
    test_unsigned_source_also_cannot_claim_complete_authentication,
    test_missing_sender_needs_recovery_without_using_prestate_guess,
    test_hash_only_expected_post_state_stays_hash_only,
    test_blobs_authorizations_and_unknown_semantics_are_explicit,
    test_wrong_width_lists_duplicate_account_keys_and_storage_keys_fail,
    test_semantic_invalid_values_and_transaction_exceptions_are_preserved,
    test_keccak_vectors_and_blob_price_integer_division,
    test_case_selection_never_silently_chooses_a_post_or_test,
    test_source_retained_without_aliasing_or_mutation,
    test_custom_blob_schedule_and_previous_block_hash_are_preserved,
    test_missing_randao_or_excess_is_not_fabricated,
    test_non_string_expected_exception_is_malformed,
    test_semantic_environment_extras_are_reported_but_metadata_is_harmless,
    test_every_signed_envelope_requires_authentication_without_exception_matching,
    test_invalid_v_r_s_remain_authentication_boundaries_with_raw_values,
    test_type3_signed_envelope_preserves_chain_id_fee_cap_and_blob_order,
    test_type3_signed_fee_and_blob_hash_mismatches_fail,
    test_type3_malformed_envelope_blob_field_shapes_fail,
    test_type3_semantic_invalid_empty_or_wrong_version_hashes_are_preserved,
    test_blob_creation_preserves_native_execution_shape_and_canonical_rejection_boundary,
)


if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} transaction fixture parser tests passed")
