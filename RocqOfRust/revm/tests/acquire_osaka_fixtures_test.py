"""Bounded acquisition rejects stale or incomplete fixture bundles."""

import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import acquire_osaka_fixtures as acquire
import transaction_fixture as fixture


def archive_bytes(members):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w:gz") as archive:
        for name, value in members:
            info = tarfile.TarInfo("fixtures/" + name)
            info.size = len(value)
            archive.addfile(info, io.BytesIO(value))
    return output.getvalue()


class AcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.directory = self.enterContext(tempfile.TemporaryDirectory())
        self.tmp_path = Path(self.directory)

    def configure(self, data):
        self.enterContext(patch.object(acquire.stream, "ARCHIVE_SHA256", hashlib.sha256(data).hexdigest()))
        self.enterContext(patch.object(acquire, "EXPECTED_COUNTS", {"state_test": 1, "transaction_test": 1}))
        self.enterContext(patch.object(acquire.corpus, "load_index", lambda root: {"cases": {
            "state": {"fork": "Osaka", "format": "state_test", "json_path": "state_tests/osaka.json"},
            "raw": {"fork": "Osaka", "format": "transaction_test", "json_path": "transaction_tests/osaka.json"},
            "other": {"fork": "Prague", "format": "state_test", "json_path": "state_tests/prague.json"},
        }}))

    def test_retains_exact_selection_and_index(self):
        data = archive_bytes([(".meta/index.json", b"index"),
                              ("state_tests/prague.json", b"skip"),
                              ("state_tests/osaka.json", b"state"),
                              ("transaction_tests/osaka.json", b"raw")])
        self.configure(data)
        destination = self.tmp_path / "fixtures"
        result = acquire.acquire(io.BytesIO(data), destination)
        assert result["counts"] == {"state_test": 1, "transaction_test": 1}
        assert result["payload_files"] == 2
        assert result["retained_bytes"] == 13
        assert not (destination / "state_tests/prague.json").exists()
        assert json.loads((destination / "acquisition.json").read_text()) == result

    def test_missing_payload_cannot_produce_manifest(self):
        data = archive_bytes([(".meta/index.json", b"index")])
        self.configure(data)
        with self.assertRaisesRegex(fixture.FixtureError, "lacks selected"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")
        assert not (self.tmp_path / "fixtures/acquisition.json").exists()

    def test_full_archive_hash_checked_even_for_unselected_member(self):
        data = archive_bytes([(".meta/index.json", b"index"),
                              ("state_tests/osaka.json", b"state"),
                              ("transaction_tests/osaka.json", b"raw")])
        self.configure(data)
        self.enterContext(patch.object(acquire.stream, "ARCHIVE_SHA256", "0" * 64))
        with self.assertRaisesRegex(fixture.FixtureError, "SHA256"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")

    def test_existing_destination_is_never_overwritten(self):
        with self.assertRaises(FileExistsError):
            acquire.acquire(io.BytesIO(), self.tmp_path)

    def test_selected_payload_bound(self):
        data = archive_bytes([(".meta/index.json", b"index")])
        self.configure(data)
        self.enterContext(patch.object(acquire, "MAX_MEMBER_BYTES", 2))
        with self.assertRaisesRegex(fixture.FixtureError, "oversized"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")

    def test_index_is_required_before_payload(self):
        data = archive_bytes([("state_tests/osaka.json", b"state")])
        self.configure(data)
        with self.assertRaisesRegex(fixture.FixtureError, "index must precede"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")

    def test_duplicate_selected_member_is_rejected(self):
        data = archive_bytes([(".meta/index.json", b"index"), (".meta/index.json", b"index")])
        self.configure(data)
        with self.assertRaisesRegex(fixture.FixtureError, "duplicate"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")

    def test_retention_bound_prevents_partial_manifest(self):
        data = archive_bytes([(".meta/index.json", b"index"),
                              ("state_tests/osaka.json", b"state")])
        self.configure(data)
        self.enterContext(patch.object(acquire, "MAX_RETAINED_BYTES", 7))
        with self.assertRaisesRegex(fixture.FixtureError, "retention bound"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")
        assert not (self.tmp_path / "fixtures/acquisition.json").exists()

    def test_path_traversal_is_rejected(self):
        data = archive_bytes([("../escape", b"bad")])
        self.configure(data)
        with self.assertRaisesRegex(fixture.FixtureError, "unsafe archive"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")
        assert not (self.tmp_path / "escape").exists()

    def test_symlink_index_is_rejected(self):
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode="w:gz") as archive:
            info = tarfile.TarInfo("fixtures/.meta/index.json")
            info.type = tarfile.SYMTYPE
            info.linkname = "/etc/passwd"
            archive.addfile(info)
        data = output.getvalue()
        self.configure(data)
        with self.assertRaisesRegex(fixture.FixtureError, "nonregular"):
            acquire.acquire(io.BytesIO(data), self.tmp_path / "fixtures")


if __name__ == "__main__":
    unittest.main()
