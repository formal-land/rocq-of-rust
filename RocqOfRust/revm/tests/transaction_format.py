"""Strict raw-transaction fixture adapter; only Rocq computes validation outcomes.

A negative fixture checks definite transaction rejection, as in the client
transaction-test contract. Unsupported and incomplete results are not rejections.
"""

from __future__ import annotations

import json

import eest_corpus as corpus
import transaction_compare as wire
import transaction_fixture as fixture


SCOPE = "raw_transaction"
PASS_CLASSIFICATIONS = {"validated_transaction_pass", "validated_transaction_rejection"}


def bounded_uint(value: object, bits: int, field: str) -> int:
    value = wire.unsigned(value)
    if value >= 1 << bits:
        raise fixture.FixtureError(f"{field} exceeds {bits}-bit unsigned width")
    return value


def fixture_gas(value: object) -> int:
    if type(value) is int:
        return bounded_uint(value, 64, "intrinsicGas")
    if not isinstance(value, str) or not value:
        raise fixture.FixtureError("intrinsicGas must be a hexadecimal or decimal integer")
    if value.startswith("0x"):
        result = fixture.hex_int(value, "intrinsicGas")
    elif value.isascii() and value.isdecimal():
        result = int(value, 10)
    else:
        raise fixture.FixtureError("intrinsicGas must be a hexadecimal or decimal integer")
    return bounded_uint(result, 64, "intrinsicGas")


def normalize_case(test: dict, fork: str, name: str) -> dict:
    if not isinstance(test, dict) or set(test) != {"_info", "txbytes", "result"}:
        raise fixture.FixtureError("raw fixture requires exact _info, txbytes and result fields")
    results = fixture.object_field(test["result"], "raw fixture.result")
    if set(results) != {fork}:
        raise fixture.FixtureError("indexed raw case must have exactly its metadata result fork")
    expected = fixture.object_field(results[fork], "raw fixture result")
    negative = "exception" in expected
    required = {"exception", "intrinsicGas"} if negative else {"sender", "hash", "intrinsicGas"}
    if set(expected) != required:
        raise fixture.FixtureError("raw fixture result has missing, unknown or conflicting fields")
    exception = expected.get("exception")
    if negative and (not isinstance(exception, str) or not exception):
        raise fixture.FixtureError("raw fixture exception must be a nonempty string")
    return {"name": name, "fork": fork, "raw": list(fixture.hex_bytes(test["txbytes"], "txbytes")),
            "expectation": {"exception": exception, "intrinsic_gas": fixture_gas(expected["intrinsicGas"]),
                            "sender": None if negative else int.from_bytes(fixture.hex_bytes(expected["sender"], "sender", 20), "big"),
                            "hash": None if negative else list(fixture.hex_bytes(expected["hash"], "hash", 32))}}


def load_case(index: dict, case: dict, test: dict | None = None) -> dict:
    if case["format"] != "transaction_test":
        raise fixture.FixtureError("raw adapter requires transaction_test format")
    if test is None:
        test = corpus.load_test(index, case)
    return normalize_case(test, case["fork"], case["id"])


def serialize_input(case: dict) -> str:
    if case["fork"] not in fixture.SUPPORTED_FORKS:
        raise fixture.FixtureError("raw validation fork is outside the extracted handler")
    raw = case["raw"]
    if not isinstance(raw, list):
        raise fixture.FixtureError("raw transaction must be a byte array")
    for byte in raw:
        bounded_uint(byte, 8, "transaction byte")
    message = {"protocol": wire.PROTOCOL, "request": "validate_signed_transaction", "fork": case["fork"],
               "chain_id": 1, "signed_transaction": raw}
    encoded = json.dumps(message, separators=(",", ":"), allow_nan=False) + "\n"
    if len(encoded.encode()) > wire.MAX_WIRE_BYTES:
        raise fixture.FixtureError("raw request exceeds wire size limit")
    return encoded


def parse_output(encoded: str) -> dict:
    if len(encoded.encode()) > wire.MAX_WIRE_BYTES:
        raise fixture.FixtureError("raw result exceeds wire size limit")
    output = corpus.read_json(encoded)
    if (not isinstance(output, dict) or type(output.get("protocol")) is not int
            or output["protocol"] != wire.PROTOCOL or output.get("engine") != wire.ENGINE
            or output.get("scope") != SCOPE):
        raise fixture.FixtureError("raw result requires the Rocq REVM protocol and raw_transaction scope")
    common = {"protocol", "engine", "scope", "kind"}
    kind = output.get("kind")
    if not isinstance(kind, str):
        raise fixture.FixtureError("raw result kind must be a string")
    if kind == "Valid":
        wire.exact_fields(output, common | {"sender", "hash", "intrinsic_gas"})
        bounded_uint(output["sender"], 160, "sender")
        bounded_uint(output["intrinsic_gas"], 64, "intrinsic_gas")
        if not isinstance(output["hash"], list) or len(output["hash"]) != 32:
            raise fixture.FixtureError("raw transaction hash must have 32 bytes")
        for byte in output["hash"]:
            bounded_uint(byte, 8, "hash byte")
    elif kind in {"Rejected", "Unsupported"}:
        wire.exact_fields(output, common | {"reason", "details"})
        if not isinstance(output["reason"], str) or not output["reason"] or not isinstance(output["details"], list):
            raise fixture.FixtureError("raw rejection requires a nonempty reason and details array")
        for value in output["details"]:
            wire.unsigned(value)
    elif kind == "Incomplete":
        wire.exact_fields(output, common)
    else:
        raise fixture.FixtureError("unknown raw validation result kind")
    return output


def compare_result(case: dict, output: dict) -> dict:
    output = parse_output(json.dumps(output, allow_nan=False))
    result = {"engine": wire.ENGINE, "fixture": {"name": case["name"], "fork": case["fork"]},
              "scope": SCOPE, "full_eest_pass": False, "fixture_identity_verified": False,
              "authentication_verified": output["kind"] == "Valid", "validation_verified": False,
              "classification": "unsupported", "differences": []}
    if output["kind"] == "Unsupported":
        result["reasons"] = [output["reason"]]
        return result
    if output["kind"] == "Incomplete":
        result.update(classification="incomplete", reasons=["native_validation_incomplete"])
        return result
    result["validation_verified"] = True
    expected = case["expectation"]
    negative = expected["exception"] is not None
    if (output["kind"] == "Rejected") != negative:
        result.update(classification="transaction_mismatch", differences=[{
            "field": "validity", "expected": not negative, "actual": output["kind"] == "Valid"}])
    elif negative:
        # Exception names are diagnostic alternatives. The raw transaction-test
        # contract checks definite rejection, not an implementation's error text.
        result.update(classification="validated_transaction_rejection",
                      rejection={"reason": output["reason"], "details": output["details"]})
    else:
        result["differences"] = [{"field": field, "expected": expected[field], "actual": output[field]}
                                 for field in ("sender", "hash", "intrinsic_gas")
                                 if expected[field] != output[field]]
        result["classification"] = "transaction_mismatch" if result["differences"] else "validated_transaction_pass"
    return result
