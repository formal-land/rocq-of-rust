#!/usr/bin/env python3
"""Verify exact selected-case accounting and authenticated pinned fixture passes."""

from __future__ import annotations

import argparse
import hashlib
import math
import json
from pathlib import Path

import eest_corpus as corpus
import run_eest_corpus as runner
import transaction_compare as compare
import transaction_fixture as fixture
import transaction_format as raw_format


RECORD_FIELDS = {"protocol", "engine", "fixture", "pin", "fuel", "timeout_seconds",
                 "duration_seconds", "bridge_sha256", "request_sha256", "status", "comparison",
                 "native_output", "reasons"}


def digest_or_none(value):
    if value is not None and (not isinstance(value, str) or len(value) != 64
            or any(char not in "0123456789abcdef" for char in value)):
        raise fixture.FixtureError("invalid result SHA256 digest")


def validate_record(index: dict, case: dict, record: dict):
    if not isinstance(record, dict) or set(record) not in (RECORD_FIELDS, RECORD_FIELDS | {"execution"}):
        raise fixture.FixtureError("result record has missing or unknown fields")
    if type(record["protocol"]) is not int or record["protocol"] != corpus.RECORD_VERSION:
        raise fixture.FixtureError("wrong result protocol")
    if record["engine"] != compare.ENGINE:
        raise fixture.FixtureError("wrong result engine")
    if record["fixture"] != case:
        raise fixture.FixtureError("result fixture identity differs from selected index case")
    if not isinstance(record["pin"], dict) or type(record["pin"].get("verified")) is not bool or record["pin"] != index["pin"]:
        raise fixture.FixtureError("result fixture pin differs from loaded index")
    runner.check_limits(record["fuel"], record["timeout_seconds"])
    if "execution" in record:
        execution = record["execution"]
        if not isinstance(execution, dict) or set(execution) != {
                "bridge_sha256", "harness_sha256", "fuel", "timeout_seconds"}:
            raise fixture.FixtureError("invalid execution identity")
        for key in ("bridge_sha256", "harness_sha256"):
            if execution[key] is None:
                raise fixture.FixtureError("execution identity requires digests")
            digest_or_none(execution[key])
        for key in ("bridge_sha256", "fuel", "timeout_seconds"):
            if execution[key] != record[key]:
                raise fixture.FixtureError("execution identity disagrees with result")
    duration = record["duration_seconds"]
    if type(duration) not in (int, float) or not math.isfinite(duration) or duration < 0:
        raise fixture.FixtureError("invalid result duration")
    for key in ("bridge_sha256", "request_sha256"):
        digest_or_none(record[key])
    if not isinstance(record["status"], str) or record["status"] not in runner.STATUSES:
        raise fixture.FixtureError("unrecognized result status")
    if not isinstance(record["reasons"], list) or any(not isinstance(reason, str) for reason in record["reasons"]):
        raise fixture.FixtureError("invalid result reasons")
    output = record["native_output"]
    if output is not None:
        output = runner.parse_native_output(case, json.dumps(output, allow_nan=False))
    comparison = record["comparison"]
    if comparison is not None:
        if output is None or case["format"] not in {"state_test", "transaction_test"}:
            raise fixture.FixtureError("comparison requires an executable fixture format and native output")
        request = runner.serialize_case_request(index, case, record["fuel"])
        if record["request_sha256"] != hashlib.sha256(request.encode()).hexdigest():
            raise fixture.FixtureError("signed request digest differs from selected fixture")
        status, expected = runner.classification(index, case, output)
        if comparison != expected or record["status"] != status or record["reasons"] != expected.get("reasons", []):
            raise fixture.FixtureError("recorded result differs from independent fixture comparison")
    elif record["status"] in {"pass", "authenticated_state_pass", "validated_state_rejection",
                              "validated_transaction_pass", "validated_transaction_rejection", "execution_only", "mismatch",
                              "authentication_mismatch", "incomplete"}:
        raise fixture.FixtureError("result classification requires retained native comparison evidence")
    if record["status"] == "pass":
        if record["bridge_sha256"] is None or not index["pin"]["verified"]:
            raise fixture.FixtureError("complete pass requires an identified bridge and immutable fixture pin")
        if comparison["full_eest_pass"] is not True or not (
                comparison["authentication_verified"] is True
                or (comparison["classification"] == "validated_state_rejection"
                    and comparison["scope"] == "validated_state_rejection")
                or (comparison["classification"] in raw_format.PASS_CLASSIFICATIONS
                    and comparison["scope"] == raw_format.SCOPE
                    and comparison["validation_verified"] is True)):
            raise fixture.FixtureError("execution-only output cannot count as complete fixture pass")


def verify_records(index: dict, cases: list[dict], records, expected_bridge_sha256: str | None = None) -> dict:
    selected = {case["id"]: case for case in cases}
    statuses = {}
    identity = None
    for record in records:
        if not isinstance(record, dict) or not isinstance(record.get("fixture"), dict):
            raise fixture.FixtureError("result record requires a fixture identity")
        case_id = record["fixture"].get("id")
        if not isinstance(case_id, str) or case_id not in selected:
            raise fixture.FixtureError(f"result contains an unselected case {case_id!r}")
        if case_id in statuses:
            raise fixture.FixtureError(f"duplicate result for exact case {case_id!r}")
        validate_record(index, selected[case_id], record)
        if expected_bridge_sha256 is not None and record["bridge_sha256"] != expected_bridge_sha256:
            raise fixture.FixtureError("result bridge differs from expected executable")
        current_identity = (record.get("execution"), record["bridge_sha256"],
                            record["fuel"], record["timeout_seconds"])
        if identity is not None and current_identity != identity:
            raise fixture.FixtureError("results mix different execution identities")
        identity = current_identity
        statuses[case_id] = record["status"]
    missing = selected.keys() - statuses.keys()
    if missing:
        raise fixture.FixtureError(f"result inventory is missing {len(missing)} selected case(s), first {sorted(missing)[0]!r}")
    return runner.summarize(index, cases, statuses)


def read_records(paths):
    for path in paths:
        with path.open("rb") as source:
            number = 0
            limit = 2 * compare.MAX_WIRE_BYTES
            while line := source.readline(limit + 1):
                number += 1
                if len(line) > limit:
                    raise fixture.FixtureError(f"result line exceeds size limit {path}:{number}")
                if not line.strip():
                    raise fixture.FixtureError(f"blank result line {path}:{number}")
                try:
                    yield corpus.read_json(line)
                except fixture.FixtureError as error:
                    raise fixture.FixtureError(f"invalid result {path}:{number}: {error}") from error


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    corpus.add_selection_arguments(parser)
    parser.add_argument("--results", type=Path, nargs="+", required=True)
    parser.add_argument("--bridge", type=Path, help="require results from this executable")
    args = parser.parse_args()
    try:
        index, cases = corpus.selected_index(args)
        expected_hash = hashlib.sha256(args.bridge.read_bytes()).hexdigest() if args.bridge else None
        summary = verify_records(index, cases, read_records(args.results), expected_hash)
        print(json.dumps(summary, sort_keys=True))
        return 0 if summary["all_selected_pass"] else 1
    except (fixture.FixtureError, OSError, ValueError) as error:
        parser.exit(2, f"EEST verification error: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
