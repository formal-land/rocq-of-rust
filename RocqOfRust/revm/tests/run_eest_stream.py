#!/usr/bin/env python3
"""Bounded EEST archive execution with live comparison and compact checkpoints.

Receipts are local execution attestations, not retained semantic witnesses. Replay
executes the bridge again; checking receipt hashes alone never verifies execution.
"""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import sqlite3
import sys
import tarfile
import tempfile
import time
import zlib

import eest_corpus as corpus
import run_eest_corpus as runner
import transaction_compare as compare
import transaction_fixture as fixture
import transaction_format as raw_format
import verify_eest_corpus as verify


ARCHIVE_SHA256 = "1280540950a4c3470a421416b6f35458a9b635827265c29e5aef1ae839ae1788"
MAX_ARCHIVE_BYTES = 540487005
CHUNK_BYTES = 65536
MAX_INDEX_ITEM_BYTES = 65536
DEFAULT_MEMBER_BYTES = 128 * 1024 * 1024
DEFAULT_EVIDENCE_BYTES = 512 * 1024 * 1024
EXECUTABLE_FORMATS = {"state_test", "transaction_test"}
ZERO_HASH = "0" * 64


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def sha256(value):
    return hashlib.sha256(value).hexdigest()


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while block := source.read(CHUNK_BYTES):
            digest.update(block)
    return digest.hexdigest()


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def read_chunk(state):
    block = state["source"].read(CHUNK_BYTES)
    state["hash"].update(block)
    state["buffer"] = block
    state["position"] = 0
    return bool(block)


def peek(state):
    if state["position"] == len(state["buffer"]) and not read_chunk(state):
        return None
    return state["buffer"][state["position"]]


def take(state):
    byte = peek(state)
    if byte is None:
        raise fixture.FixtureError("truncated streaming index")
    state["position"] += 1
    return byte


def whitespace(state):
    while peek(state) in (9, 10, 13, 32):
        take(state)


def expect(state, byte):
    whitespace(state)
    if take(state) != byte:
        raise fixture.FixtureError("invalid streaming index delimiter")


def json_value(state):
    """Scan one bounded value; the canonical JSON reader validates its grammar."""
    whitespace(state)
    result = bytearray()
    depth = 0
    quoted = False
    escaped = False
    first = peek(state)
    if first is None or first in (44, 93, 125):
        raise fixture.FixtureError("missing streaming index value")
    compound = first in (91, 123)
    string = first == 34
    while True:
        byte = peek(state)
        if byte is None:
            if quoted or depth:
                raise fixture.FixtureError("truncated streaming index value")
            break
        if result and not quoted and depth == 0 and not compound and not string and byte in (9, 10, 13, 32, 44, 93, 125):
            break
        byte = take(state)
        result.append(byte)
        if len(result) > MAX_INDEX_ITEM_BYTES:
            raise fixture.FixtureError("streaming index item exceeds bound")
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
                if string and depth == 0:
                    break
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            if depth > 256:
                raise fixture.FixtureError("streaming index nesting exceeds bound")
        elif byte in (93, 125):
            depth -= 1
            if compound and depth == 0:
                break
    return corpus.read_json(bytes(result))


def index_cases(source, digest):
    """The actual pin has a top-level test_cases array, not a nested wrapper."""
    state = {"source": source, "hash": digest, "buffer": b"", "position": 0}
    expect(state, 123)
    keys = set()
    while True:
        key = json_value(state)
        if not isinstance(key, str) or key in keys:
            raise fixture.FixtureError("duplicate or invalid streaming index key")
        keys.add(key)
        expect(state, 58)
        if key == "test_cases":
            expect(state, 91)
            whitespace(state)
            if peek(state) == 93:
                raise fixture.FixtureError("streaming index has no cases")
            while True:
                yield json_value(state)
                whitespace(state)
                delimiter = take(state)
                if delimiter == 93:
                    break
                if delimiter != 44:
                    raise fixture.FixtureError("invalid streaming case delimiter")
        else:
            json_value(state)
        whitespace(state)
        delimiter = take(state)
        if delimiter == 125:
            break
        if delimiter != 44:
            raise fixture.FixtureError("invalid streaming object delimiter")
    whitespace(state)
    if peek(state) is not None or "test_cases" not in keys:
        raise fixture.FixtureError("trailing index data or missing test_cases")


def validated_case(raw):
    raw = fixture.object_field(raw, "metadata case")
    fields = ("id", "fixture_hash", "fork", "json_path", "format")
    if any(not isinstance(raw.get(key), str) or not raw[key] for key in fields):
        raise fixture.FixtureError("invalid EEST metadata case fields")
    case = {key: raw[key] for key in fields}
    if case["format"] not in corpus.FORMAT_DIRECTORIES:
        raise fixture.FixtureError("unknown EEST metadata format")
    path = PurePosixPath(case["json_path"])
    if (path.is_absolute() or ".." in path.parts or str(path) != case["json_path"]
            or path.parts[:1] != (corpus.FORMAT_DIRECTORIES[case["format"]],)):
        raise fixture.FixtureError("unsafe or noncanonical EEST metadata path")
    corpus.check_hash(case["fixture_hash"], "metadata.fixture_hash")
    return case


def connect(path):
    connection = sqlite3.connect(path)
    connection.execute("PRAGMA cache_size=-8192")
    connection.execute("PRAGMA temp_store=FILE")
    connection.execute("PRAGMA synchronous=FULL")
    connection.execute("PRAGMA journal_mode=DELETE")
    return connection


def set_meta(db, key, value):
    db.execute("INSERT OR REPLACE INTO meta VALUES (?, ?)", (key, encoded(value).decode()))


def get_meta(db, key):
    row = db.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    if row is None:
        raise fixture.FixtureError("checkpoint metadata missing: " + key)
    return corpus.read_json(row[0])


def make_inventory(index_path, target, require_pin=True):
    """Publish the disk index only after the entire source and census validate."""
    target = target.resolve()
    if target.exists():
        raise fixture.FixtureError("inventory already exists")
    temporary = target.with_name(target.name + ".building")
    # Exclusive creation also refuses an earlier interrupted build.
    with temporary.open("xb"):
        pass
    db = connect(temporary)
    try:
        db.executescript("CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);"
                         "CREATE TABLE cases (number INTEGER PRIMARY KEY, id TEXT UNIQUE NOT NULL,"
                         " format TEXT NOT NULL, path TEXT NOT NULL, fork TEXT NOT NULL, hash TEXT NOT NULL);"
                         "CREATE INDEX case_path ON cases(path);"
                         "CREATE TABLE results (sequence INTEGER PRIMARY KEY, number INTEGER UNIQUE NOT NULL,"
                         " receipt TEXT NOT NULL, chain TEXT NOT NULL);"
                         "CREATE TABLE visits (path TEXT PRIMARY KEY);")
        counts, forks = Counter(), Counter()
        digest = hashlib.sha256()
        with index_path.open("rb") as source:
            for number, raw in enumerate(index_cases(source, digest), 1):
                case = validated_case(raw)
                if require_pin and number > sum(corpus.PINNED_COUNTS.values()):
                    raise fixture.FixtureError("streaming index exceeds pinned case count")
                db.execute("INSERT INTO cases VALUES (?, ?, ?, ?, ?, ?)",
                           (number, case["id"], case["format"], case["json_path"], case["fork"], case["fixture_hash"]))
                counts[case["format"]] += 1
                if case["format"] == "state_test":
                    forks[case["fork"]] += 1
                if number % 1000 == 0:
                    db.commit()
        actual_hash = digest.hexdigest()
        if require_pin and (actual_hash != corpus.PINNED_INDEX_SHA256
                            or counts != corpus.PINNED_COUNTS or forks != corpus.PINNED_FORK_COUNTS):
            raise fixture.FixtureError("streaming index SHA256/census differs from immutable pin")
        pin = {"verified": require_pin, "ref": corpus.PINNED_REF if require_pin else None,
               "commit": corpus.PINNED_COMMIT if require_pin else None, "index_sha256": actual_hash}
        set_meta(db, "pin", pin)
        set_meta(db, "counts", dict(counts))
        set_meta(db, "chain", ZERO_HASH)
        set_meta(db, "archive_verified", False)
        set_meta(db, "complete", False)
        db.commit()
        db.close()
        os.rename(temporary, target)
        sync_directory(target.parent)
    except Exception:
        db.close()
        temporary.unlink(missing_ok=True)
        raise


def case_from_row(row):
    number, case_id, case_format, path, fork, payload_hash = row
    return number, {"id": case_id, "format": case_format, "json_path": path,
                    "fork": fork, "fixture_hash": payload_hash}


def append_receipt(db, number, receipt):
    body = encoded(receipt)
    chain = sha256(bytes.fromhex(get_meta(db, "chain")) + body)
    db.execute("INSERT INTO results(number, receipt, chain) VALUES (?, ?, ?)", (number, body.decode(), chain))
    set_meta(db, "chain", chain)


def compact(record, number, evidence=None):
    semantic = {key: value for key, value in record.items() if key != "duration_seconds"}
    return {"number": number, "status": record["status"],
            "request_sha256": record["request_sha256"],
            "native_sha256": sha256(encoded(record["native_output"])),
            "record_sha256": sha256(encoded(record)), "semantic_sha256": sha256(encoded(semantic)),
            "reasons": record["reasons"], "evidence": evidence}


RECEIPT_FIELDS = {"number", "status", "request_sha256", "native_sha256", "record_sha256",
                  "semantic_sha256", "reasons", "evidence"}


def verify_receipts(db, work):
    """Accounting/integrity check only. No discarded output is reclassified."""
    chain = ZERO_HASH
    checked_evidence = set()
    for number, body, stored_chain, case_format in db.execute(
            "SELECT r.number,r.receipt,r.chain,c.format FROM results r JOIN cases c USING(number) ORDER BY sequence"):
        receipt = corpus.read_json(body)
        if not isinstance(receipt, dict) or set(receipt) != RECEIPT_FIELDS or receipt["number"] != number:
            raise fixture.FixtureError("invalid compact receipt identity/schema")
        if type(receipt["number"]) is not int or not isinstance(receipt["status"], str) or receipt["status"] not in runner.STATUSES:
            raise fixture.FixtureError("invalid compact receipt status")
        for key in ("request_sha256", "native_sha256", "record_sha256", "semantic_sha256"):
            verify.digest_or_none(receipt[key])
            if key != "request_sha256" and receipt[key] is None:
                raise fixture.FixtureError("missing compact receipt digest")
        if not isinstance(receipt["reasons"], list) or any(not isinstance(reason, str) for reason in receipt["reasons"]):
            raise fixture.FixtureError("invalid compact receipt reasons")
        if receipt["status"] == "pass" and (case_format not in EXECUTABLE_FORMATS or receipt["request_sha256"] is None):
            raise fixture.FixtureError("invalid complete pass receipt")
        chain = sha256(bytes.fromhex(chain) + encoded(receipt))
        if chain != stored_chain:
            raise fixture.FixtureError("compact receipt chain differs")
        evidence = receipt["evidence"]
        if evidence is not None:
            if not isinstance(evidence, dict) or set(evidence) != {"record", "member"}:
                raise fixture.FixtureError("invalid failure evidence fields")
            for label, entry in evidence.items():
                if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
                    raise fixture.FixtureError("invalid failure evidence entry")
                if not isinstance(entry["path"], str):
                    raise fixture.FixtureError("invalid failure evidence path")
                verify.digest_or_none(entry["sha256"])
                relative = PurePosixPath(entry["path"])
                if relative.is_absolute() or ".." in relative.parts or relative.parts[:1] != ("evidence",):
                    raise fixture.FixtureError("unsafe failure evidence path")
                if entry["path"] != "evidence/" + label + "-" + str(entry["sha256"]) + ".zlib":
                    raise fixture.FixtureError("noncanonical failure evidence path")
                path = (work / entry["path"]).resolve()
                if not path.is_relative_to(work.resolve()):
                    raise fixture.FixtureError("failure evidence digest differs")
                identity = (entry["path"], entry["sha256"])
                if identity not in checked_evidence:
                    if file_sha256(path) != entry["sha256"]:
                        raise fixture.FixtureError("failure evidence digest differs")
                    checked_evidence.add(identity)
        elif case_format in EXECUTABLE_FORMATS and receipt["status"] != "pass":
            raise fixture.FixtureError("executable failure lacks retained evidence")
    if chain != get_meta(db, "chain"):
        raise fixture.FixtureError("checkpoint receipt root differs")
    if db.execute("SELECT count(*) FROM results").fetchone()[0] != db.execute(
            "SELECT count(*) FROM results JOIN cases USING(number)").fetchone()[0]:
        raise fixture.FixtureError("checkpoint contains unindexed result")


def config_for(db, bridge, fuel, timeout, member_bytes, evidence_bytes):
    runner.check_limits(fuel, timeout)
    if type(member_bytes) is not int or member_bytes <= 0 or type(evidence_bytes) is not int or evidence_bytes <= 0:
        raise fixture.FixtureError("stream byte limits must be positive integers")
    return {"protocol": 1, "engine": compare.ENGINE, "pin": get_meta(db, "pin"),
            "archive_sha256": ARCHIVE_SHA256, "bridge_sha256": file_sha256(bridge),
            "fuel": fuel, "timeout_seconds": timeout, "member_bytes": member_bytes,
            "evidence_bytes": evidence_bytes,
            "harness_sha256": {Path(module.__file__).name: file_sha256(Path(module.__file__))
                               for module in (corpus, runner, compare, fixture, raw_format, verify)}
            | {"run_eest_stream.py": file_sha256(Path(__file__))}}


def inventory_check(db):
    counts = dict(db.execute("SELECT format,count(*) FROM cases GROUP BY format"))
    if counts != get_meta(db, "counts"):
        raise fixture.FixtureError("checkpoint census changed")
    # Pin must be bound to source index every invocation, not inferred from SQL.
    return counts


def preserve(work, member, record, budget, state):
    directory = work / "evidence"
    directory.mkdir(exist_ok=True)
    if state["bytes"] is None:
        state["bytes"] = sum(item.stat().st_size for item in directory.iterdir() if item.name.endswith(".zlib"))
    # Shared member snapshots use a content digest; records are individually retained.
    sources = {"member": member, "record": encoded(record)}
    evidence = {}
    pending = []
    try:
        for label, source in sources.items():
            if label == "member" and source in state["members"]:
                evidence[label] = state["members"][source]
                continue
            compressor = zlib.compressobj()
            with tempfile.NamedTemporaryFile(dir=directory, prefix="pending-", delete=False) as output:
                path = Path(output.name)
                pending.append(path)
                if isinstance(source, Path):
                    with source.open("rb") as input_file:
                        while block := input_file.read(CHUNK_BYTES):
                            output.write(compressor.compress(block))
                else:
                    output.write(compressor.compress(source))
                output.write(compressor.flush())
                output.flush()
                os.fsync(output.fileno())
            digest = file_sha256(path)
            destination = directory / (label + "-" + digest + ".zlib")
            if not destination.exists():
                size = path.stat().st_size
                if state["bytes"] + size > budget:
                    raise fixture.FixtureError("failure evidence budget exhausted; checkpoint remains incomplete")
                os.rename(path, destination)
                sync_directory(directory)
                state["bytes"] += size
            evidence[label] = {"path": str(destination.relative_to(work)), "sha256": digest}
            if label == "member":
                state["members"][source] = evidence[label]
        return evidence
    finally:
        for path in pending:
            path.unlink(missing_ok=True)


class HashReader:
    """Minimal file protocol adapter; no archive bytes are retained."""
    def __init__(self, source):
        self.source = source
        self.digest = hashlib.sha256()
        self.bytes_read = 0
        self.last_progress = time.monotonic()

    def read(self, size=-1):
        if size < 0:
            raise fixture.FixtureError("unbounded archive read refused")
        block = self.source.read(size)
        self.bytes_read += len(block)
        if self.bytes_read > MAX_ARCHIVE_BYTES:
            raise fixture.FixtureError("compressed archive exceeds immutable byte bound")
        self.digest.update(block)
        if time.monotonic() - self.last_progress >= 30:
            print(json.dumps({"progress": "archive_stream", "compressed_bytes": self.bytes_read,
                              "archive_verified": False}), file=sys.stderr, flush=True)
            self.last_progress = time.monotonic()
        return block


def safe_member(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts:
        raise fixture.FixtureError("unsafe archive member path")
    # The immutable release is rooted at fixtures/.
    if not path.parts or path.parts[0] != "fixtures":
        return None
    return str(PurePosixPath(*path.parts[1:])) if len(path.parts) > 1 else None


def seed_unsupported(db):
    config = get_meta(db, "config")
    pin = config["pin"]
    batch = 0
    for row in db.execute("SELECT * FROM cases WHERE format NOT IN ('state_test','transaction_test') AND number NOT IN (SELECT number FROM results) ORDER BY number"):
        number, case = case_from_row(row)
        record = {"protocol": corpus.RECORD_VERSION, "engine": compare.ENGINE,
                  "fixture": case, "pin": pin, "fuel": config["fuel"],
                  "timeout_seconds": config["timeout_seconds"], "duration_seconds": 0,
                  "bridge_sha256": config["bridge_sha256"], "request_sha256": None,
                  "status": "unsupported", "comparison": None, "native_output": None,
                  "reasons": ["format:" + case["format"]]}
        verify.validate_record({"root": Path("."), "pin": pin}, case, record)
        append_receipt(db, number, compact(record, number))
        batch += 1
        if batch % 1000 == 0:
            db.commit()
    db.commit()


def summary(db, replayed=0):
    counts = inventory_check(db)
    grouped = list(db.execute("SELECT c.format,json_extract(r.receipt,'$.status'),count(*) FROM results r JOIN cases c USING(number) GROUP BY c.format,json_extract(r.receipt,'$.status')"))
    statuses, done, passed = Counter(), Counter(), Counter()
    for case_format, status, count in grouped:
        statuses[status] += count
        done[case_format] += count
        if status == "pass":
            passed[case_format] += count
    archive_verified = get_meta(db, "archive_verified") is True
    complete = archive_verified and done == counts and get_meta(db, "complete") is True
    pinned = get_meta(db, "pin")["verified"] is True
    return {"protocol": 1, "engine": compare.ENGINE, "pin": get_meta(db, "pin"),
            "archive_verified": archive_verified, "inventory_complete": complete,
            "selected": sum(counts.values()), "recorded": sum(done.values()),
            "statuses": dict(statuses), "missing_by_format": {key: count - done[key] for key, count in counts.items()},
            "verification_scope": "live_comparison_receipts",
            "compact_hashes_independently_verify_execution": False,
            "replayed_executable_cases": replayed,
            "full_state_corpus_pass": complete and pinned and passed["state_test"] == corpus.PINNED_COUNTS["state_test"],
            "full_transaction_corpus_pass": complete and pinned and passed["transaction_test"] == corpus.PINNED_COUNTS["transaction_test"],
            "full_eest_corpus_pass": complete and pinned and passed == counts,
            "receipt_root_sha256": get_meta(db, "chain")}


def execute_archive(db, source, bridge_path, work, replay=False):
    config = get_meta(db, "config")
    pin = get_meta(db, "pin")
    set_meta(db, "archive_verified", False)
    set_meta(db, "complete", False)
    db.commit()
    verify_receipts(db, work)
    # An interrupted process can leave its own uncommitted current-member copy.
    # Only these reserved directories are removed, under the caller's work lock.
    for path in work.glob("member-*"):
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
    for path in (work / "evidence").glob("pending-*"):
        if path.is_file() and not path.is_symlink():
            path.unlink()
    db.execute("DELETE FROM visits")
    db.commit()
    seed_unsupported(db)
    hashed = HashReader(source)
    bridge = {}
    replayed = 0
    evidence_state = {"bytes": None, "members": {}}
    try:
        with tempfile.TemporaryDirectory(prefix="member-", dir=work) as temporary:
            root = Path(temporary)
            with gzip.GzipFile(fileobj=hashed, mode="rb") as decompressed:
                with tarfile.open(fileobj=decompressed, mode="r|") as archive:
                    for member in archive:
                        archive.members.clear()
                        path = safe_member(member.name)
                        if path is None:
                            continue
                        rows = db.execute("SELECT * FROM cases WHERE path=? AND format IN ('state_test','transaction_test') ORDER BY number", (path,))
                        first = rows.fetchone()
                        if first is None:
                            continue
                        if not member.isfile() or member.size > config["member_bytes"]:
                            raise fixture.FixtureError("selected archive member is nonregular or exceeds member bound: " + path)
                        try:
                            db.execute("INSERT INTO visits VALUES (?)", (path,))
                        except sqlite3.IntegrityError as error:
                            raise fixture.FixtureError("duplicate selected archive member: " + path) from error
                        db.commit()
                        target = root / path
                        target.parent.mkdir(parents=True, exist_ok=True)
                        with archive.extractfile(member) as input_file, target.open("xb") as output:
                            remaining = member.size
                            while remaining:
                                block = input_file.read(min(CHUNK_BYTES, remaining))
                                if not block:
                                    raise fixture.FixtureError("truncated selected archive member")
                                output.write(block)
                                remaining -= len(block)
                        corpus.fixture_document.cache_clear()
                        def run_row(row):
                            nonlocal replayed
                            number, case = case_from_row(row)
                            prior = db.execute("SELECT receipt FROM results WHERE number=?", (number,)).fetchone()
                            if prior is not None and not replay:
                                return
                            index = {"root": root, "pin": pin, "cases": {case["id"]: case}}
                            record = runner.run_case(index, case, bridge, bridge_path, config["fuel"],
                                                     config["timeout_seconds"], config["bridge_sha256"])
                            # Separate verifier regenerates the signed request and compares
                            # parsed retained output to the exact fixture before deletion.
                            verify.validate_record(index, case, record)
                            receipt = compact(record, number)
                            if prior is not None:
                                previous = corpus.read_json(prior[0])
                                if any(previous[key] != receipt[key] for key in ("status", "request_sha256", "native_sha256", "semantic_sha256")):
                                    raise fixture.FixtureError("replayed native result differs: " + case["id"])
                                replayed += 1
                                return
                            if record["status"] != "pass":
                                receipt["evidence"] = preserve(work, target, record, config["evidence_bytes"], evidence_state)
                            append_receipt(db, number, receipt)
                            db.commit()
                        run_row(first)
                        for row in rows:
                            run_row(row)
                        corpus.fixture_document.cache_clear()
                        target.unlink()
                        evidence_state["members"].clear()
                # tar stops at its end marker; drain gzip and the compressed input
                # to validate gzip CRC and hash every archive byte, including trailers.
                while decompressed.read(CHUNK_BYTES):
                    pass
            while hashed.read(CHUNK_BYTES):
                pass
        if hashed.digest.hexdigest() != config["archive_sha256"]:
            raise fixture.FixtureError("full archive SHA256 differs from immutable pin")
        missing = db.execute("SELECT count(*) FROM cases c LEFT JOIN results r USING(number) WHERE r.number IS NULL").fetchone()[0]
        if missing:
            raise fixture.FixtureError(f"archive/checkpoint lacks {missing} indexed executable cases")
        missing_members = db.execute("SELECT count(DISTINCT c.path) FROM cases c LEFT JOIN visits v ON c.path=v.path WHERE c.format IN ('state_test','transaction_test') AND v.path IS NULL").fetchone()[0]
        if missing_members:
            raise fixture.FixtureError(f"archive lacks {missing_members} indexed executable members")
        verify_receipts(db, work)
        set_meta(db, "archive_verified", True)
        set_meta(db, "complete", True)
        db.commit()
        return summary(db, replayed)
    finally:
        runner.stop_bridge(bridge)
        corpus.fixture_document.cache_clear()


def check_index_identity(db, index_path):
    digest = hashlib.sha256()
    count = 0
    with index_path.open("rb") as source:
        for count, raw in enumerate(index_cases(source, digest), 1):
            case = validated_case(raw)
            row = db.execute("SELECT * FROM cases WHERE number=?", (count,)).fetchone()
            if row is None or case_from_row(row) != (count, case):
                raise fixture.FixtureError("checkpoint identity differs from source index")
    if count != db.execute("SELECT count(*) FROM cases").fetchone()[0]:
        raise fixture.FixtureError("checkpoint identity inventory has extra cases")
    pin = get_meta(db, "pin")
    if digest.hexdigest() != pin["index_sha256"]:
        raise fixture.FixtureError("resume index source differs")
    if pin["verified"] is True:
        expected = {"verified": True, "ref": corpus.PINNED_REF, "commit": corpus.PINNED_COMMIT,
                    "index_sha256": corpus.PINNED_INDEX_SHA256}
        if pin != expected or inventory_check(db) != corpus.PINNED_COUNTS:
            raise fixture.FixtureError("resume immutable pin/census differs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--archive", required=True, help="pinned tar.gz file, or - for a streamed stdin")
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--bridge", type=Path, default=runner.DEFAULT_BRIDGE)
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--member-bytes", type=int, default=DEFAULT_MEMBER_BYTES)
    parser.add_argument("--evidence-bytes", type=int, default=DEFAULT_EVIDENCE_BYTES)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--replay", action="store_true", help="execute every saved executable case again and check its receipt")
    args = parser.parse_args()
    db = None
    try:
        # A process lock prevents parallel workers from sharing bridge/checkpoints.
        import fcntl
        args.work.mkdir(parents=True, exist_ok=True)
        with (args.work / "lock").open("a+b") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            inventory = args.work / "inventory.sqlite3"
            if args.replay and not args.resume:
                raise fixture.FixtureError("replay requires --resume")
            if not args.resume:
                make_inventory(args.index, inventory)
            db = connect(inventory)
            if args.resume:
                check_index_identity(db, args.index)
            config = config_for(db, args.bridge.resolve(), args.fuel, args.timeout, args.member_bytes, args.evidence_bytes)
            if args.resume:
                previous = get_meta(db, "config")
                storage_limits = {"member_bytes", "evidence_bytes"}
                if ({key: value for key, value in config.items() if key not in storage_limits}
                        != {key: value for key, value in previous.items() if key not in storage_limits}
                        or any(config[key] < previous[key] for key in storage_limits)):
                    raise fixture.FixtureError("resume bridge/harness/pin/resource configuration differs")
                set_meta(db, "config", config)
                db.commit()
            else:
                set_meta(db, "config", config)
                db.commit()
            if args.archive == "-":
                result = execute_archive(db, sys.stdin.buffer, args.bridge.resolve(), args.work, args.replay)
            else:
                with Path(args.archive).open("rb") as source:
                    result = execute_archive(db, source, args.bridge.resolve(), args.work, args.replay)
            print(json.dumps(result, sort_keys=True))
            return 0 if result["full_eest_corpus_pass"] else 1
    except (fixture.FixtureError, OSError, ValueError, sqlite3.Error, tarfile.TarError, EOFError, zlib.error) as error:
        if db is not None:
            db.rollback()
            set_meta(db, "archive_verified", False)
            set_meta(db, "complete", False)
            db.commit()
        parser.exit(2, "EEST stream error: " + runner.bounded_message(error) + "\n")
    finally:
        if db is not None:
            db.close()


if __name__ == "__main__":
    raise SystemExit(main())
