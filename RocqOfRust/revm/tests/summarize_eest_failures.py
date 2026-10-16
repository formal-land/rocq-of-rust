#!/usr/bin/env python3
"""Group retained nonpassing outcomes for triage, without asserting coverage."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import transaction_fixture as fixture
import verify_eest_corpus as verify


def summarize(records):
    groups = {}
    observed = 0
    for record in records:
        observed += 1
        try:
            status = record["status"]
            case_id = record["fixture"]["id"]
            reasons = record["reasons"]
        except (KeyError, TypeError) as error:
            raise fixture.FixtureError("diagnostic record lacks status, fixture ID or reasons") from error
        if (not isinstance(status, str) or not isinstance(case_id, str)
                or not isinstance(reasons, list) or any(not isinstance(reason, str) for reason in reasons)):
            raise fixture.FixtureError("diagnostic fields have invalid types")
        if status == "pass":
            continue
        function = case_id.split("[", 1)[0]
        key = (status, function)
        group = groups.setdefault(key, {"status": status, "test_function": function,
                                       "count": 0, "examples": []})
        group["count"] += 1
        if len(group["examples"]) < 3:
            group["examples"].append({"case_id": case_id, "reasons": reasons})
    return {"scope": "diagnostic_only", "observed_records": observed,
            "note": "Grouping does not verify evidence, completeness or common root causes.",
            "groups": sorted(groups.values(), key=lambda group: (-group["count"], group["status"], group["test_function"]))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        report = summarize(verify.read_records(args.results))
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    except (fixture.FixtureError, OSError, ValueError) as error:
        parser.exit(2, f"EEST diagnostic error: {error}\n")


if __name__ == "__main__":
    main()
