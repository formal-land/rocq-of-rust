"""Standalone immutable EEST index and payload identity checks for Rocq REVM."""

from __future__ import annotations

from collections import Counter
import functools
import hashlib
import json
from pathlib import Path

import transaction_fixture as fixture


PINNED_REF = "refs/tags/tests@v20.0.2"
PINNED_COMMIT = "abbe05777ab83fb94ce18c425daaa7ab79e779c1"
PINNED_INDEX_SHA256 = "ea6470549fccf1e51fcbe84e9106e2aadd488a02b905e161c5f27cdcb776b910"
PINNED_COUNTS = {
    "state_test": 61813, "blockchain_test": 72715,
    "blockchain_test_engine": 55275, "blockchain_test_engine_x": 55275,
    "blockchain_test_sync": 9, "transaction_test": 124,
}
PINNED_FORK_COUNTS = {
    "Berlin": 3009, "Byzantium": 1915, "Cancun": 11653,
    "ConstantinopleFix": 2045, "Frontier": 584, "Homestead": 599,
    "Istanbul": 2157, "London": 3286, "Osaka": 14614, "Paris": 3301,
    "Prague": 13949, "Shanghai": 3499, "SpuriousDragon": 606, "TangerineWhistle": 596,
}
FORMAT_DIRECTORIES = {
    "state_test": "state_tests", "blockchain_test": "blockchain_tests",
    "transaction_test": "transaction_tests",
    "blockchain_test_engine": "blockchain_tests_engine",
    "blockchain_test_engine_x": "blockchain_tests_engine_x",
    "blockchain_test_sync": "blockchain_tests_sync",
}
RECORD_VERSION = 1


def reject_constant(value):
    raise fixture.FixtureError(f"non-finite JSON constant {value!r}")


def read_json(encoded: str | bytes):
    try:
        return json.loads(encoded, object_pairs_hook=fixture_object,
                          parse_constant=reject_constant)
    except (ValueError, TypeError, UnicodeError) as error:
        raise fixture.FixtureError(f"invalid fixture JSON: {error}") from error


def fixture_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise fixture.FixtureError(f"duplicate fixture JSON key {key!r}")
        result[key] = value
    return result


def canonical_hash(test: dict) -> str:
    # EEST BaseFixture.hash: sort_keys=True, separators=(",", ":"), without _info.
    # https://steel.ethereum.foundation/docs/execution-specs/library/execution_testing_fixtures/
    payload = {key: value for key, value in test.items() if key != "_info"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()
    return "0x" + hashlib.sha256(encoded).hexdigest()


def check_hash(value: object, field: str) -> str:
    return "0x" + fixture.hex_bytes(value, field, 32).hex()


def load_index(root: Path, *, require_pin: bool = True) -> dict:
    root = root.resolve()
    path = root / ".meta/index.json"
    try:
        encoded = path.read_bytes()
    except OSError as error:
        raise fixture.FixtureError(f"cannot read EEST index {path}: {error}") from error
    digest = hashlib.sha256(encoded).hexdigest()
    if require_pin and digest != PINNED_INDEX_SHA256:
        raise fixture.FixtureError(f"EEST index digest does not match {PINNED_REF}")
    metadata = fixture.object_field(read_json(encoded), "metadata")
    raw_cases = metadata.get("test_cases")
    if not isinstance(raw_cases, list) or not raw_cases:
        raise fixture.FixtureError("EEST index requires a nonempty test_cases array")
    cases = {}
    for raw in raw_cases:
        raw = fixture.object_field(raw, "metadata case")
        fields = ("id", "fixture_hash", "fork", "json_path", "format")
        if any(not isinstance(raw.get(field), str) or not raw[field] for field in fields):
            raise fixture.FixtureError("invalid EEST metadata case fields")
        case = {field: raw[field] for field in fields}
        fixture_format = case["format"]
        if fixture_format not in FORMAT_DIRECTORIES:
            raise fixture.FixtureError(f"unrecognized EEST metadata format {fixture_format!r}")
        rel = Path(case["json_path"])
        if (rel.is_absolute() or ".." in rel.parts
                or rel.parts[:1] != (FORMAT_DIRECTORIES[fixture_format],)):
            raise fixture.FixtureError(f"unsafe EEST fixture path {case['json_path']!r}")
        check_hash(case["fixture_hash"], "metadata.fixture_hash")
        if case["id"] in cases:
            raise fixture.FixtureError(f"duplicate EEST case ID {case['id']!r}")
        cases[case["id"]] = case
    verified = require_pin
    if verified:
        counts = Counter(case["format"] for case in cases.values())
        forks = Counter(case["fork"] for case in cases.values() if case["format"] == "state_test")
        if counts != PINNED_COUNTS or forks != PINNED_FORK_COUNTS:
            raise fixture.FixtureError("EEST index census does not match immutable pin")
    return {"root": root, "cases": cases, "pin": {
        "verified": verified, "ref": PINNED_REF if verified else None,
        "commit": PINNED_COMMIT if verified else None, "index_sha256": digest,
    }}


def shard_for_id(case_id: str, count: int) -> int:
    return int.from_bytes(hashlib.sha256(case_id.encode()).digest()[:4], "big") % count


def select_cases(index: dict, *, fixture_format: str = "state_test", exact_ids=(),
                 fork: str | None = None, shard_index: int | None = None,
                 shard_count: int | None = None) -> list[dict]:
    if fixture_format not in {*FORMAT_DIRECTORIES, "all"}:
        raise fixture.FixtureError("unrecognized EEST format selector")
    if len(set(exact_ids)) != len(exact_ids):
        raise fixture.FixtureError("duplicate exact case selector")
    if (shard_count is None) != (shard_index is None):
        raise fixture.FixtureError("shard index and count must be supplied together")
    if shard_count is not None and (type(shard_count) is not int or shard_count <= 0
            or type(shard_index) is not int or not 0 <= shard_index < shard_count):
        raise fixture.FixtureError("invalid shard coordinates")
    if fork is not None and fork not in {case["fork"] for case in index["cases"].values()}:
        raise fixture.FixtureError(f"unknown fork {fork!r}")
    if exact_ids:
        unknown = set(exact_ids) - index["cases"].keys()
        if unknown:
            raise fixture.FixtureError(f"unknown exact EEST case ID {sorted(unknown)[0]!r}")
        selected = [index["cases"][case_id] for case_id in exact_ids]
        if any((fixture_format != "all" and case["format"] != fixture_format)
               or (fork is not None and case["fork"] != fork) for case in selected):
            raise fixture.FixtureError("exact cases conflict with format/fork selection")
    else:
        selected = [case for case in index["cases"].values()
                    if (fixture_format == "all" or case["format"] == fixture_format)
                    and (fork is None or case["fork"] == fork)]
    if shard_count is not None:
        selected = [case for case in selected if shard_for_id(case["id"], shard_count) == shard_index]
    if not selected:
        raise fixture.FixtureError("selection contains no EEST cases")
    return sorted(selected, key=lambda case: case["id"])


@functools.lru_cache(maxsize=4)
def fixture_document(root: Path, json_path: str) -> dict:
    path = (root / json_path).resolve()
    if not path.is_relative_to(root):
        raise fixture.FixtureError("EEST fixture path escapes its root")
    try:
        return fixture.object_field(read_json(path.read_bytes()), "fixture document")
    except OSError as error:
        raise fixture.FixtureError(f"cannot read EEST fixture {json_path}: {error}") from error


def load_test(index: dict, case: dict) -> dict:
    document = fixture_document(index["root"], case["json_path"])
    if case["id"] not in document:
        raise fixture.FixtureError(f"fixture lacks exact metadata ID {case['id']!r}")
    test = fixture.object_field(document[case["id"]], "indexed fixture")
    info = fixture.object_field(test.get("_info"), "fixture._info")
    expected = check_hash(case["fixture_hash"], "metadata.fixture_hash")
    if check_hash(info.get("hash"), "fixture._info.hash") != expected or canonical_hash(test) != expected:
        raise fixture.FixtureError("EEST fixture payload hash differs from pinned identity")
    if case["format"] == "state_test":
        post = fixture.object_field(test.get("post"), "fixture.post")
        if set(post) != {case["fork"]} or not isinstance(post[case["fork"]], list) or len(post[case["fork"]]) != 1:
            raise fixture.FixtureError("indexed state case must have exactly one post for its metadata fork")
    return test


def normalize(index: dict, case: dict, test: dict | None = None) -> dict:
    if case["format"] != "state_test":
        raise fixture.FixtureError("state adapter cannot execute another format")
    if test is None:
        test = load_test(index, case)
    return fixture.normalize_case({case["id"]: test}, case["fork"], 0, test_name=case["id"])


def add_selection_arguments(parser):
    parser.add_argument("--fixtures", type=Path, required=True)
    parser.add_argument("--format", choices=[*FORMAT_DIRECTORIES, "all"], default="all")
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--fork")
    parser.add_argument("--shard-index", type=int)
    parser.add_argument("--shard-count", type=int)
    parser.add_argument("--allow-unpinned", action="store_true",
                        help="development index only; cannot produce pinned fixture/corpus passes")


def selected_index(args) -> tuple[dict, list[dict]]:
    index = load_index(args.fixtures, require_pin=not args.allow_unpinned)
    cases = select_cases(index, fixture_format=args.format, exact_ids=args.case, fork=args.fork,
                         shard_index=args.shard_index, shard_count=args.shard_count)
    return index, cases
