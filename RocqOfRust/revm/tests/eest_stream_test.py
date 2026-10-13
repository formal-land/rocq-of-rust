"""Synthetic bounded-stream/checkpoint tests; no pinned execution is claimed."""

from __future__ import annotations

from collections import Counter
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
from unittest.mock import patch
import zlib

import eest_corpus as corpus
import eest_corpus_test as existing
import run_eest_corpus as runner
import run_eest_stream as stream
import transaction_fixture as fixture


def expect_error(function, text=""):
    try:
        function()
    except (fixture.FixtureError, OSError, ValueError, tarfile.TarError, EOFError) as error:
        assert text in str(error), str(error)
    else:
        raise AssertionError("expected error " + repr(text))


def archive_bytes(root, extra=(), omitted=()):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w") as archive:
        for path in sorted(root.rglob("*.json")):
            relative = str(path.relative_to(root))
            if relative in omitted:
                continue
            data = path.read_bytes()
            member = tarfile.TarInfo("fixtures/" + relative)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
        for name, data in extra:
            member = tarfile.TarInfo(name)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    return gzip.compress(output.getvalue(), mtime=0)


def setup(root, *, bad_state=False):
    fixtures = root / "fixtures"
    fixtures.mkdir()
    index = existing.create_index(fixtures, extra_formats=True)
    state = corpus.select_cases(index)[0]
    output = existing.native_result(index, state)
    if bad_state:
        output["commitments"]["state_root"][0] = 99
    counter = root / "requests.txt"
    bridge = existing.mock_bridge(root,
        "import json, sys\n"
        "for line in sys.stdin:\n"
        "    request = json.loads(line)\n"
        "    with open(" + repr(str(counter)) + ", 'a') as log: log.write(request['request'] + '\\n')\n"
        "    result = " + repr(json.dumps(output)) + " if request['request'] == 'execute_signed_transaction' else "
        + repr(json.dumps({"protocol": 1, "engine": "rocq_revm", "scope": "raw_transaction",
                           "kind": "Rejected", "reason": "NonceOverflow", "details": []})) + "\n"
        "    print(result, flush=True)\n")
    data = archive_bytes(fixtures)
    work = root / "work"
    work.mkdir()
    db_path = work / "inventory.sqlite3"
    counts = Counter(case["format"] for case in index["cases"].values())
    forks = Counter(case["fork"] for case in index["cases"].values() if case["format"] == "state_test")
    with patch.object(corpus, "PINNED_INDEX_SHA256", index["pin"]["index_sha256"]), \
            patch.object(corpus, "PINNED_COUNTS", dict(counts)), patch.object(corpus, "PINNED_FORK_COUNTS", dict(forks)):
        stream.make_inventory(fixtures / ".meta/index.json", db_path)
    db = stream.connect(db_path)
    with patch.object(stream, "ARCHIVE_SHA256", hashlib.sha256(data).hexdigest()):
        stream.set_meta(db, "config", stream.config_for(db, bridge, 1000, 2, 65536, 1048576))
    db.commit()
    return db, fixtures, bridge, work, data, counter, dict(counts)


def test_incremental_index_parser_is_strict_and_bounded():
    class ShortSource:
        def __init__(self, encoded):
            self.source = io.BytesIO(encoded)
            self.calls = []

        def read(self, size):
            assert 0 < size <= stream.CHUNK_BYTES
            self.calls.append(size)
            return self.source.read(min(size, 17))

    encoded = json.dumps({"root_hash": "fake", "test_cases": [{"id": "a\\\"b"}, {"id": "c"}], "extra": [1, 2]}).encode()
    source = ShortSource(encoded)
    digest = hashlib.sha256()
    assert list(stream.index_cases(source, digest)) == [{"id": "a\\\"b"}, {"id": "c"}]
    assert digest.hexdigest() == hashlib.sha256(encoded).hexdigest()
    assert len(source.calls) > 3
    for encoded in (b'{"test_cases":[]}', b'{"test_cases":[{}],"test_cases":[{}]}',
                    b'{"test_cases":[{},]}', b'{"test_cases":[{}],}', b'{"test_cases":[{}]}junk',
                    b'{"test_cases":[{"id":1,"id":2}]}', b'{"test_cases":[{"id":NaN}]}',
                    b'{"test_cases":[{"id":"bad\\x"}]}', b'{"test_cases":[{}]', b'{"other":1}'):
        expect_error(lambda: list(stream.index_cases(io.BytesIO(encoded), hashlib.sha256())))
    with patch.object(stream, "MAX_INDEX_ITEM_BYTES", 32):
        expect_error(lambda: list(stream.index_cases(io.BytesIO(b'{"test_cases":[{"id":"' + b'x' * 100 + b'"}]}'), hashlib.sha256())), "bound")


def test_inventory_publish_is_atomic_and_resume_checks_actual_identities():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        fixtures = root / "fixtures"
        fixtures.mkdir()
        index = existing.create_index(fixtures)
        target = root / "inventory.sqlite3"
        expect_error(lambda: stream.make_inventory(fixtures / ".meta/index.json", target), "immutable pin")
        assert not target.exists() and not target.with_name(target.name + ".building").exists()
        stream.make_inventory(fixtures / ".meta/index.json", target, require_pin=False)
        db = stream.connect(target)
        try:
            stream.check_index_identity(db, fixtures / ".meta/index.json")
            db.execute("UPDATE cases SET fork='Prague'")
            db.commit()
            expect_error(lambda: stream.check_index_identity(db, fixtures / ".meta/index.json"), "identity")
        finally:
            db.close()


def test_all_six_formats_are_accounted_and_only_executable_formats_can_pass():
    with tempfile.TemporaryDirectory() as directory:
        db, fixtures, bridge, work, data, counter, counts = setup(Path(directory))
        try:
            with patch.object(corpus, "PINNED_COUNTS", counts):
                result = stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert result["inventory_complete"] and result["archive_verified"]
            assert result["selected"] == result["recorded"] == 6
            assert result["statuses"] == {"pass": 2, "unsupported": 4}
            assert result["full_state_corpus_pass"] and result["full_transaction_corpus_pass"]
            assert not result["full_eest_corpus_pass"]
            assert not result["compact_hashes_independently_verify_execution"]
            assert counter.read_text().count("\n") == 2
            assert not list(work.glob("member-*"))
            assert not list(work.glob("evidence/*"))
            stream.verify_receipts(db, work)
        finally:
            db.close()


def test_full_archive_digest_and_missing_members_gate_completion_even_on_resume():
    with tempfile.TemporaryDirectory() as directory:
        db, fixtures, bridge, work, data, counter, counts = setup(Path(directory))
        try:
            config = stream.get_meta(db, "config")
            wrong_hash = dict(config, archive_sha256="f" * 64)
            stream.set_meta(db, "config", wrong_hash)
            db.commit()
            expect_error(lambda: stream.execute_archive(db, io.BytesIO(data), bridge, work), "SHA256")
            assert not stream.summary(db)["inventory_complete"]
            assert counter.read_text().count("\n") == 2
            stream.set_meta(db, "config", config)
            db.commit()
            stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert counter.read_text().count("\n") == 2  # durable completed cases skip safely
            missing_data = archive_bytes(fixtures, omitted=("state_tests/case.json",))
            stream.set_meta(db, "config", dict(config, archive_sha256=hashlib.sha256(missing_data).hexdigest()))
            db.commit()
            expect_error(lambda: stream.execute_archive(db, io.BytesIO(missing_data), bridge, work), "members")
            assert not stream.summary(db)["inventory_complete"]
            expect_error(lambda: stream.execute_archive(db, io.BytesIO(data[:-10]), bridge, work))
            assert not stream.summary(db)["inventory_complete"]
        finally:
            db.close()


def test_failure_evidence_is_retained_and_budget_exhaustion_never_omits_cases():
    with tempfile.TemporaryDirectory() as directory:
        db, fixtures, bridge, work, data, counter, counts = setup(Path(directory), bad_state=True)
        try:
            result = stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert result["statuses"] == {"pass": 1, "mismatch": 1, "unsupported": 4}
            assert not result["full_state_corpus_pass"]
            receipt = corpus.read_json(db.execute("SELECT receipt FROM results r JOIN cases c USING(number) WHERE c.format='state_test'").fetchone()[0])
            evidence = receipt["evidence"]
            record = corpus.read_json(zlib.decompress((work / evidence["record"]["path"]).read_bytes()))
            member = corpus.read_json(zlib.decompress((work / evidence["member"]["path"]).read_bytes()))
            assert record["status"] == "mismatch" and record["fixture"]["id"] in member
            stream.verify_receipts(db, work)
            (work / evidence["record"]["path"]).write_bytes(b"tampered")
            expect_error(lambda: stream.verify_receipts(db, work), "digest")
        finally:
            db.close()
    with tempfile.TemporaryDirectory() as directory:
        db, fixtures, bridge, work, data, counter, counts = setup(Path(directory), bad_state=True)
        try:
            config = stream.get_meta(db, "config")
            stream.set_meta(db, "config", dict(config, evidence_bytes=1))
            db.commit()
            expect_error(lambda: stream.execute_archive(db, io.BytesIO(data), bridge, work), "budget")
            assert not stream.summary(db)["inventory_complete"]
            assert db.execute("SELECT count(*) FROM results r JOIN cases c USING(number) WHERE c.format='state_test'").fetchone()[0] == 0
        finally:
            db.close()


def test_duplicates_unsafe_paths_and_member_bounds_fail_before_completion():
    for extra, maximum, error in (
            (("fixtures/state_tests/case.json", b"{}"), 65536, "duplicate"),
            (("fixtures/../escaped", b"evil"), 65536, "unsafe"),
            (("other", b""), 1, "bound")):
        with tempfile.TemporaryDirectory() as directory:
            db, fixtures, bridge, work, data, counter, counts = setup(Path(directory))
            try:
                modified = archive_bytes(fixtures, extra=(extra,))
                config = stream.get_meta(db, "config")
                stream.set_meta(db, "config", dict(config, archive_sha256=hashlib.sha256(modified).hexdigest(), member_bytes=maximum))
                db.commit()
                expect_error(lambda: stream.execute_archive(db, io.BytesIO(modified), bridge, work), error)
                assert not stream.summary(db)["inventory_complete"]
            finally:
                db.close()


def test_live_wire_verification_precedes_receipt_and_replay_executes_again():
    with tempfile.TemporaryDirectory() as directory:
        db, fixtures, bridge, work, data, counter, counts = setup(Path(directory))
        try:
            # A malformed authenticated output must be rejected by the separate
            # wire validator before a forged pass can reach the compact journal.
            record = existing.make_record(corpus.load_index(fixtures, require_pin=False),
                                          corpus.select_cases(corpus.load_index(fixtures, require_pin=False))[0])
            record["pin"] = stream.get_meta(db, "pin")
            record["native_output"]["authentication"]["verified"] = 1
            with patch.object(runner, "run_case", return_value=record):
                expect_error(lambda: stream.execute_archive(db, io.BytesIO(data), bridge, work), "authentication")
            assert db.execute("SELECT count(*) FROM results r JOIN cases c USING(number) WHERE c.format='state_test'").fetchone()[0] == 0
            stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert counter.read_text().count("\n") == 2
            result = stream.execute_archive(db, io.BytesIO(data), bridge, work, replay=True)
            assert result["replayed_executable_cases"] == 2
            assert counter.read_text().count("\n") == 4
            changed = {"protocol": 1, "engine": "rocq_revm", "kind": "Unsupported",
                       "authentication": {"verified": False, "transaction": None},
                       "reason": "SyntheticChangedResult", "details": []}
            with patch.object(runner, "bridge_exchange", return_value=changed):
                expect_error(lambda: stream.execute_archive(db, io.BytesIO(data), bridge, work, replay=True), "replayed")
            assert not stream.summary(db)["inventory_complete"]
            # Tampered hashes cannot be treated as independently verified output.
            row = db.execute("SELECT sequence,receipt FROM results WHERE json_extract(receipt,'$.status')='pass' LIMIT 1").fetchone()
            receipt = corpus.read_json(row[1])
            receipt["native_sha256"] = "0" * 64
            db.execute("UPDATE results SET receipt=? WHERE sequence=?", (stream.encoded(receipt).decode(), row[0]))
            db.commit()
            expect_error(lambda: stream.execute_archive(db, io.BytesIO(data), bridge, work), "chain")
        finally:
            db.close()


def test_multiple_cases_in_one_member_execute_and_checkpoint_individually():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        db, fixtures, bridge, work, data, counter, counts = setup(root)
        db.close()
        # Rebuild a synthetic inventory with two state IDs sharing one member.
        document = corpus.read_json((fixtures / "state_tests/case.json").read_bytes())
        original_id = next(iter(document))
        document["synthetic[second-state]"] = document[original_id]
        (fixtures / "state_tests/case.json").write_text(json.dumps(document))
        metadata = corpus.read_json((fixtures / ".meta/index.json").read_bytes())
        original_case = next(case for case in metadata["test_cases"] if case["format"] == "state_test")
        metadata["test_cases"].append(dict(original_case, id="synthetic[second-state]"))
        (fixtures / ".meta/index.json").write_text(json.dumps(metadata))
        (work / "inventory.sqlite3").unlink()
        stream.make_inventory(fixtures / ".meta/index.json", work / "inventory.sqlite3", require_pin=False)
        db = stream.connect(work / "inventory.sqlite3")
        data = archive_bytes(fixtures)
        with patch.object(stream, "ARCHIVE_SHA256", hashlib.sha256(data).hexdigest()):
            stream.set_meta(db, "config", stream.config_for(db, bridge, 1000, 2, 65536, 1048576))
        db.commit()
        try:
            result = stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert result["recorded"] == result["selected"] == 7
            assert result["statuses"] == {"authenticated_state_pass": 2, "validated_transaction_rejection": 1, "unsupported": 4}
            assert counter.read_text().count("\n") == 3
            stream.verify_receipts(db, work)
            stream.execute_archive(db, io.BytesIO(data), bridge, work)
            assert counter.read_text().count("\n") == 3
        finally:
            db.close()


TESTS = tuple(value for name, value in tuple(globals().items()) if name.startswith("test_"))

if __name__ == "__main__":
    for test in TESTS:
        test()
    print(f"{len(TESTS)} synthetic streaming tests passed; no pinned corpus execution claimed")
