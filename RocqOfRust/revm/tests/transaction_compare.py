"""Signed/execution requests and state comparisons for extracted REVM.

Only Rocq produces execution transactions, authentication evidence and hashes
for signed requests. Fixture identity verification is a separate requirement
before any result can count as a complete EEST pass.
"""

from __future__ import annotations

import copy
import json

import transaction_fixture as fixture


PROTOCOL = 1
ENGINE = "rocq_revm"
MAX_FUEL = 10000000
MAX_WIRE_BYTES = 16 * 1024 * 1024
ACCOUNT_FIELDS = ("address", "balance", "nonce", "code_hash")
SETTLEMENT_FIELDS = ("gas_remaining", "gas_refunded", "gas_used", "caller_reimbursement",
                     "beneficiary_reward", "base_fee_burn", "blob_fee_burn")


# Exact handler errors observed in the historical GeneralStateTests corpus.
# Authentication rejection is checked separately against its validation stage.
EXPECTED_REJECTIONS = {
    "TransactionException.INTRINSIC_GAS_TOO_LOW": {"IntrinsicGasTooHigh"},
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS": {"LackOfFunds"},
    "TransactionException.SENDER_NOT_EOA": {"RejectCallerWithCode"},
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS": {"GasPriceBelowBaseFee"},
    "TransactionException.GAS_ALLOWANCE_EXCEEDED": {"GasLimitAboveBlock"},
    "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS": {"PriorityFeeGreaterThanMaxFee"},
    "TransactionException.TYPE_4_EMPTY_AUTHORIZATION_LIST": {"EmptyAuthorizationList"},
    "TransactionException.TYPE_3_TX_ZERO_BLOBS": {"EmptyBlobs"},
    "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED": {"TooManyBlobs"},
    "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH": {"BlobVersionNotSupported"},
    "TransactionException.INITCODE_SIZE_EXCEEDED": {"CreateInitCodeSizeLimit"},
    "TransactionException.NONCE_MISMATCH_TOO_HIGH": {"NonceTooHigh"},
    "TransactionException.NONCE_MISMATCH_TOO_LOW": {"NonceTooLow"},
    "TransactionException.NONCE_IS_MAX": {"NonceOverflow"},
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_BLOB_GAS": {"BlobGasPriceGreaterThanMax"},
}


def unsigned(value: object) -> int:
    if type(value) is not int or value < 0:
        raise fixture.FixtureError("wire integer must be nonnegative")
    return value


def execution_gaps(case: dict, signed: bool) -> list[str]:
    addressed = {"authentication_verification_required"}
    if signed:
        addressed |= {"sender_recovery_required", "invalid_signed_envelope",
                      "canonical_blob_creation_validation_required"}
    return [reason for reason in case["unsupported"] if reason not in addressed]


def serialize_input(case: dict, fuel: int = 1000000, *, signed: bool | None = None) -> str:
    if case["fork"] not in fixture.SUPPORTED_FORKS:
        raise fixture.FixtureError("wire fork is outside the extracted handler")
    raw = case["expectation"]["txbytes"]
    if signed is None:
        signed = raw is not None
    if type(signed) is not bool:
        raise fixture.FixtureError("signed execution flag must be boolean")
    if signed and raw is None:
        raise fixture.FixtureError("signed execution requires transaction bytes")
    gaps = execution_gaps(case, signed)
    if gaps:
        raise fixture.FixtureError(f"unsupported execution inputs: {gaps}")
    if unsigned(fuel) > MAX_FUEL:
        raise fixture.FixtureError("native request fuel exceeds limit")
    message = {"protocol": PROTOCOL, "fuel": unsigned(fuel), "fork": case["fork"],
               "input": copy.deepcopy(case["input"])}
    if signed:
        if not isinstance(raw, list) or any(unsigned(byte) > 255 for byte in raw):
            raise fixture.FixtureError("signed transaction must be bytes")
        caller = case["transaction"]["caller"]
        if caller is not None:
            unsigned(caller)
        message.update(request="execute_signed_transaction", signed_transaction=copy.deepcopy(raw),
                       declared_sender=caller)
    else:
        unsigned(case["transaction"]["caller"])
        message.update(request="execute_transaction", transaction=copy.deepcopy(case["transaction"]))
    encoded = json.dumps(message, separators=(",", ":"), allow_nan=False) + "\n"
    if len(encoded.encode()) > MAX_WIRE_BYTES:
        raise fixture.FixtureError("native request exceeds input size limit")
    return encoded


def unique_object(pairs):
    value = {}
    for key, entry in pairs:
        if key in value:
            raise fixture.FixtureError(f"duplicate native JSON key {key!r}")
        value[key] = entry
    return value


def exact_fields(value: object, fields: set[str]):
    if not isinstance(value, dict) or set(value) != fields:
        raise fixture.FixtureError(f"native result must have exact fields {sorted(fields)}")


def validate_account(account: dict):
    exact_fields(account, set(ACCOUNT_FIELDS) | {"code", "storage", "transient_storage"})
    for key in ACCOUNT_FIELDS:
        unsigned(account[key])
    if not isinstance(account["code"], list):
        raise fixture.FixtureError("native code must be an array")
    for byte in account["code"]:
        if unsigned(byte) > 255:
            raise fixture.FixtureError("native code byte is out of range")
    for field in ("storage", "transient_storage"):
        if not isinstance(account[field], list):
            raise fixture.FixtureError("native storage must be an array")
        for pair in account[field]:
            if not isinstance(pair, list) or len(pair) != 2:
                raise fixture.FixtureError("native storage entry must be a pair")
            unsigned(pair[0])
            unsigned(pair[1])


def validate_transaction(transaction: dict):
    exact_fields(transaction, {"tx_type", "caller", "target", "nonce", "chain_id", "gas_limit",
                 "gas_price", "max_priority_fee", "access_list", "max_fee_per_blob_gas", "blob_hashes",
                 "value", "data", "authorization_list"})
    for field in ("tx_type", "caller", "nonce", "gas_limit", "gas_price", "max_fee_per_blob_gas", "value"):
        unsigned(transaction[field])
    for field in ("target", "chain_id", "max_priority_fee"):
        if transaction[field] is not None:
            unsigned(transaction[field])
    for field in ("blob_hashes", "data"):
        if not isinstance(transaction[field], list):
            raise fixture.FixtureError("native transaction fields must be arrays")
        for value in transaction[field]:
            if unsigned(value) > 255 and field == "data":
                raise fixture.FixtureError("native transaction data byte is out of range")
    if not isinstance(transaction["access_list"], list):
        raise fixture.FixtureError("native access list must be an array")
    for entry in transaction["access_list"]:
        if not isinstance(entry, list) or len(entry) != 2 or not isinstance(entry[1], list):
            raise fixture.FixtureError("native access-list entry must be a pair with key array")
        unsigned(entry[0])
        for key in entry[1]:
            unsigned(key)
    if transaction["authorization_list"] is not None:
        if transaction["tx_type"] != 4 or not isinstance(transaction["authorization_list"], list):
            raise fixture.FixtureError("native authorization list requires type 4")
        for entry in transaction["authorization_list"]:
            exact_fields(entry, {"chain_id", "address", "nonce", "y_parity", "r", "s"})
            for key, bits in (("chain_id", 256), ("address", 160), ("nonce", 64), ("y_parity", 8), ("r", 256), ("s", 256)):
                if unsigned(entry[key]) >= 1 << bits:
                    raise fixture.FixtureError("native authorization integer exceeds Rust width")
    elif transaction["tx_type"] == 4:
        raise fixture.FixtureError("native type 4 requires authorization list")


def validate_authentication(authentication: dict):
    exact_fields(authentication, {"verified", "transaction"})
    if type(authentication["verified"]) is not bool:
        raise fixture.FixtureError("native authentication flag must be boolean")
    if authentication["verified"]:
        validate_transaction(authentication["transaction"])
    elif authentication["transaction"] is not None:
        raise fixture.FixtureError("unverified authentication cannot supply a transaction")


def validate_commitments(commitments: dict):
    exact_fields(commitments, {"source", "state_root", "logs_hash"})
    if commitments["source"] != "rocq":
        raise fixture.FixtureError("native commitments must come from Rocq")
    for field in ("state_root", "logs_hash"):
        value = commitments[field]
        if not isinstance(value, list) or len(value) != 32:
            raise fixture.FixtureError("native commitment must have 32 bytes")
        for byte in value:
            if unsigned(byte) > 255:
                raise fixture.FixtureError("native commitment byte is out of range")


def parse_output(encoded: str) -> dict:
    if len(encoded.encode()) > MAX_WIRE_BYTES:
        raise fixture.FixtureError("native result exceeds input size limit")
    try:
        result = json.loads(encoded, object_pairs_hook=unique_object)
    except (ValueError, TypeError) as error:
        raise fixture.FixtureError(f"invalid native JSON result: {error}") from error
    if not isinstance(result, dict) or type(result.get("protocol")) is not int or result["protocol"] != PROTOCOL:
        raise fixture.FixtureError("invalid native result version")
    if result.get("engine") != ENGINE:
        raise fixture.FixtureError("native result engine must be rocq_revm")
    validate_authentication(result.get("authentication"))
    common = {"protocol", "engine", "kind", "authentication"}
    kind = result.get("kind")
    if kind == "Completed":
        exact_fields(result, common | {"status", "gas", "data", "accounts", "logs", "commitments"})
        validate_commitments(result["commitments"])
        if not isinstance(result["status"], str):
            raise fixture.FixtureError("native status must be a string")
        exact_fields(result["gas"], set(SETTLEMENT_FIELDS))
        for value in result["gas"].values():
            unsigned(value)
        for field in ("data", "accounts", "logs"):
            if not isinstance(result[field], list):
                raise fixture.FixtureError("native result arrays must be arrays")
        for byte in result["data"]:
            if unsigned(byte) > 255:
                raise fixture.FixtureError("native output byte is out of range")
        for account in result["accounts"]:
            validate_account(account)
        account_map(result["accounts"])
        for log in result["logs"]:
            exact_fields(log, {"address", "topics", "data"})
            unsigned(log["address"])
            if not isinstance(log["topics"], list) or not isinstance(log["data"], list):
                raise fixture.FixtureError("native log fields must be arrays")
            for topic in log["topics"]:
                unsigned(topic)
            for byte in log["data"]:
                if unsigned(byte) > 255:
                    raise fixture.FixtureError("native log byte is out of range")
    elif kind in ("Rejected", "Unsupported", "AuthenticationRejected"):
        extra = {"accounts", "logs", "commitments"} if kind in ("Rejected", "AuthenticationRejected") else set()
        exact_fields(result, common | {"reason", "details"} | extra)
        if kind in ("Rejected", "AuthenticationRejected"):
            validate_commitments(result["commitments"])
            if not isinstance(result["accounts"], list) or result["logs"] != []:
                raise fixture.FixtureError("rejection must return accounts and no logs")
            for account in result["accounts"]:
                validate_account(account)
            account_map(result["accounts"])
        if not isinstance(result["reason"], str) or not isinstance(result["details"], list):
            raise fixture.FixtureError("native rejection fields have invalid types")
        if kind == "AuthenticationRejected" and result["authentication"]["verified"]:
            raise fixture.FixtureError("authentication rejection cannot be verified")
        for detail in result["details"]:
            unsigned(detail)
    elif kind in ("Malformed", "Incomplete"):
        exact_fields(result, common)
    else:
        raise fixture.FixtureError(f"unknown native result kind {kind!r}")
    return result


def account_map(accounts: list[dict]) -> dict:
    result = {}
    for source in accounts:
        address = source["address"]
        if address in result:
            raise fixture.FixtureError("duplicate native account address")
        storage = sorted(source["storage"])
        transient = sorted(source["transient_storage"])
        if len({key for key, _ in storage}) != len(storage) or len({key for key, _ in transient}) != len(transient):
            raise fixture.FixtureError("duplicate native storage key")
        result[address] = {**source, "storage": storage, "transient_storage": transient}
    return result


def decoded_rejection_envelope(case: dict) -> dict | None:
    """Crosscheck structural decoding without recovering or asserting a sender."""
    raw = case["expectation"]["txbytes"]
    if not isinstance(raw, list) or not raw or case["expectation"]["state_root"] is None:
        return None
    try:
        envelope = fixture.signed_envelope(bytes(raw))
    except (fixture.FixtureError, ValueError, TypeError):
        return None
    if not envelope.get("supported") or envelope["nonce"] >= 1 << 64 or envelope["gas_limit"] >= 1 << 64:
        return None
    if envelope["tx_type"] == 3 and (envelope["target"] is None or any(value >= 1 << 256 for value in (
            envelope["chain_id"], envelope["gas_price"], envelope["max_priority_fee"], envelope["value"],
            envelope["max_fee_per_blob_gas"], *envelope["signature"].values()))):
        return None
    if envelope["tx_type"] == 4:
        if any(envelope[key] >= 1 << 256 for key in (
                "chain_id", "gas_price", "max_priority_fee", "value")):
            return None
        if any(value >= 1 << 256 for value in envelope["signature"].values()):
            return None
        for authorization in envelope["authorization_list"]:
            widths = {"chain_id": 256, "address": 160, "nonce": 64,
                      "y_parity": 8, "r": 256, "s": 256}
            if any(not 0 <= authorization[key] < 1 << width for key, width in widths.items()):
                return None
    if (any(case["transaction"].get(key) != value for key, value in envelope.items()
                   if key not in {"supported", "signature"})):
        return None
    return envelope


def validated_authentication_rejection(case: dict, output: dict) -> str | None:
    """Match exact validation failures that occur before signature recovery.

    This checks the scalar/parity and chain/type prerequisites used by Rocq.
    It never runs ECDSA recovery or promotes Unsupported into a rejection.
    """
    if output["kind"] != "AuthenticationRejected" or case["fork"] not in fixture.SUPPORTED_FORKS:
        return None
    envelope = decoded_rejection_envelope(case)
    if envelope is None:
        return None
    alternatives = set((case["expectation"]["exception"] or "").split("|"))
    tx_type, fork = envelope["tx_type"], case["fork"]
    creation_name = "TransactionException.TYPE_4_TX_CONTRACT_CREATION"
    if (tx_type == 4 and envelope["target"] is None and creation_name in alternatives
            and output["reason"] == "MalformedFields" and output["details"] == []):
        return creation_name
    pre_berlin = {"Frontier", "Homestead", "TangerineWhistle", "SpuriousDragon", "Byzantium",
                  "ConstantinopleFix", "Istanbul"}
    enabled = {0: fixture.SUPPORTED_FORKS, 1: fixture.SUPPORTED_FORKS - pre_berlin,
               2: fixture.LONDON_FORKS, 3: fixture.BLOB_FORKS,
               4: {"Prague", "Osaka"}}[tx_type]
    prefork_name = f"TransactionException.TYPE_{tx_type}_TX_PRE_FORK"
    if (output["reason"] == "TransactionTypeNotSupported" and output["details"] == [tx_type]
            and fork not in enabled and prefork_name in alternatives):
        return prefork_name
    if fork not in enabled:
        return None
    have, expected = envelope["chain_id"], case["input"]["chain_id"]
    protected_before_eip155 = tx_type == 0 and have is not None and fork in {
        "Frontier", "Homestead", "TangerineWhistle"}
    chain_name = "TransactionException.INVALID_CHAINID"
    if (chain_name in alternatives and output["reason"] == "ChainIdMismatch"
            and have is not None and have != expected and output["details"] == [have, expected]
            and not protected_before_eip155):
        return chain_name
    signature_name = "TransactionException.INVALID_SIGNATURE_VRS"
    if signature_name not in alternatives or output["reason"] != "InvalidSignature" or output["details"] != []:
        return None
    if not protected_before_eip155 and have is not None and have != expected:
        return None  # Rocq checks chain ID before signature scalar validity.
    signature = envelope["signature"]
    v, r, s = signature["v"], signature["r"], signature["s"]
    parity = v if tx_type else v - 27 if have is None else v - 2 * have - 35
    order = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    invalid = parity not in (0, 1) or not 0 < r < order or not 0 < s < order or (fork != "Frontier" and s > order // 2)
    return signature_name if protected_before_eip155 or invalid else None


def mapped_rejection_prerequisites(case: dict, output: dict) -> bool:
    """Check the exact fixture inputs for newly mapped nonce and blob-fee errors."""
    reason, details = output["reason"], output["details"]
    tx = case["transaction"]
    if reason == "EmptyAuthorizationList":
        return (details == [] and tx["tx_type"] == 4
                and case["fork"] in {"Prague", "Osaka"}
                and tx["target"] is not None and tx.get("authorization_list") == [])
    if reason == "NonceOverflow":
        return details == [] and tx["nonce"] == (1 << 64) - 1
    if reason in {"NonceTooHigh", "NonceTooLow"}:
        sender = next((account for account in case["input"]["accounts"] if account["address"] == tx["caller"]), None)
        sender_nonce = sender["nonce"] if sender is not None else 0
        return details == [] and (tx["nonce"] > sender_nonce if reason == "NonceTooHigh" else tx["nonce"] < sender_nonce)
    if reason == "BlobGasPriceGreaterThanMax":
        price, maximum = case["input"]["block"]["blob_base_fee"], tx["max_fee_per_blob_gas"]
        return tx["tx_type"] == 3 and price > maximum and details == [price, maximum]
    return True


def compare_execution(case: dict, output: dict) -> dict:
    output = parse_output(json.dumps(output))
    verified = output["authentication"]["verified"]
    result = {"engine": ENGINE, "fixture": {"name": case["name"], "fork": case["fork"],
              "post_index": case["post_index"]},
              "scope": "authenticated_state" if verified else "execution_only", "full_eest_pass": False,
              "fixture_identity_verified": False, "authentication_verified": verified,
              "classification": "unsupported", "differences": []}
    signed_rejection = output["kind"] == "AuthenticationRejected"
    gaps = execution_gaps(case, verified or signed_rejection)
    if gaps:
        result["reasons"] = gaps
        return result
    if output["kind"] == "Incomplete":
        result["classification"] = "incomplete"
        result["reasons"] = ["native_execution_incomplete"]
        return result
    if output["kind"] == "Unsupported":
        result["reasons"] = [output["reason"]]
        return result
    expected = case["expectation"]
    expected_rejection = expected["exception"] is not None
    matched_authentication = validated_authentication_rejection(case, output)
    if matched_authentication is not None:
        result["scope"] = "validated_state_rejection"
        result["matched_exception"] = matched_authentication
    if expected_rejection and matched_authentication is None:
        alternatives = expected["exception"].split("|")
        reasons = set().union(*(EXPECTED_REJECTIONS.get(name, set()) for name in alternatives))
        if not reasons:
            result["reasons"] = ["transaction_exception_mapping_required"]
            return result
        if output["kind"] != "Rejected":
            result["classification"] = "execution_mismatch"
            result["differences"] = [{"field": "result_kind", "expected": "Rejected", "actual": output["kind"]}]
            return result
        if not verified:
            result["reasons"] = ["rejection_authentication_required"]
            return result
        if output["reason"] not in reasons:
            result["classification"] = "execution_mismatch"
            result["differences"] = [{"field": "rejection", "expected": sorted(reasons), "actual": output["reason"]}]
            return result
        if not mapped_rejection_prerequisites(case, output):
            result["classification"] = "execution_mismatch"
            result["differences"] = [{"field": "rejection_prerequisites", "expected": "fixture inputs and exact details", "actual": output["details"]}]
            return result
        result["matched_exception"] = next(name for name in alternatives
            if output["reason"] in EXPECTED_REJECTIONS.get(name, set()))
    if not expected_rejection and output["kind"] != "Completed":
        result["classification"] = "authentication_mismatch" if signed_rejection else "execution_mismatch"
        result["differences"] = [{"field": "result_kind", "expected": "Completed", "actual": output["kind"]}]
        if "reason" in output:
            result["rejection"] = {"reason": output["reason"], "details": output["details"]}
        return result
    differences = []
    if verified:
        actual_tx = output["authentication"]["transaction"]
        for field, value in case["transaction"].items():
            if field == "caller" and value is None:
                continue
            if actual_tx[field] != value:
                differences.append({"field": "authenticated_transaction." + field,
                                    "expected": value, "actual": actual_tx[field]})
    actual_accounts = account_map(output["accounts"])
    if expected_rejection and actual_accounts != account_map(case["input"]["accounts"]):
        differences.append({"field": "rejected_pre_state", "expected": "unchanged", "actual": "changed"})
    if expected["accounts"] is not None:
        expected_accounts = account_map(expected["accounts"])
        for address in sorted(set(actual_accounts) | set(expected_accounts)):
            if address not in actual_accounts or address not in expected_accounts:
                differences.append({"field": "account_presence", "address": address,
                                    "expected": address in expected_accounts, "actual": address in actual_accounts})
            else:
                for field in ("balance", "nonce", "code", "code_hash", "storage", "transient_storage"):
                    if actual_accounts[address][field] != expected_accounts[address][field]:
                        differences.append({"field": field, "address": address,
                                            "expected": expected_accounts[address][field],
                                            "actual": actual_accounts[address][field]})
    elif expected["state_root"] is None:
        result["reasons"] = ["state_oracle_missing"]
        return result
    if expected["state_root"] is not None and output["commitments"]["state_root"] != expected["state_root"]:
        differences.append({"field": "state_root", "expected": expected["state_root"],
                            "actual": output["commitments"]["state_root"]})
    if expected["logs_hash"] is None:
        result["reasons"] = ["logs_oracle_missing"]
        return result
    if output["commitments"]["logs_hash"] != expected["logs_hash"]:
        differences.append({"field": "logs_hash", "expected": expected["logs_hash"],
                            "actual": output["commitments"]["logs_hash"]})
    result["classification"] = "execution_mismatch" if differences else (
        "validated_state_rejection" if matched_authentication is not None else
        "authenticated_state_pass" if verified else "execution_pass")
    result["differences"] = differences
    return result
