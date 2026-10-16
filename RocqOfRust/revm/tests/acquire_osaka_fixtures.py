#!/usr/bin/env python3
"""Retain only pinned Osaka state/transaction payloads from the official release."""

from __future__ import annotations

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import shutil
import tarfile
import urllib.request

import eest_corpus as corpus
import run_eest_stream as stream
import transaction_fixture as fixture


ARCHIVE_URL = "https://github.com/ethereum/execution-specs/releases/download/tests%40v20.0.2/fixtures.tar.gz"
EXPECTED_COUNTS = {"state_test": 14614, "transaction_test": 56}
MAX_RETAINED_BYTES = 4 * 1024**3
MAX_MEMBER_BYTES = 256 * 1024**2


def acquire(source, destination: Path) -> dict:
    # Exclusive destination prevents a partial or stale acquisition being reused.
    destination.mkdir(parents=True, exist_ok=False)
    hashed = stream.HashReader(source)
    selected_paths = None
    seen = set()
    retained = 0
    counts = None
    with gzip.GzipFile(fileobj=hashed, mode="rb") as decompressed:
        with tarfile.open(fileobj=decompressed, mode="r|") as archive:
            for member in archive:
                archive.members.clear()
                path = stream.safe_member(member.name)
                if path is None:
                    continue
                if selected_paths is None and path != ".meta/index.json":
                    raise fixture.FixtureError("pinned archive index must precede payloads")
                if path != ".meta/index.json" and path not in selected_paths:
                    continue
                if path in seen or not member.isfile() or not 0 <= member.size <= MAX_MEMBER_BYTES:
                    raise fixture.FixtureError("duplicate, nonregular or oversized selected archive member")
                retained += member.size
                if retained > MAX_RETAINED_BYTES:
                    raise fixture.FixtureError("selected fixtures exceed retention bound")
                seen.add(path)
                target = destination / path
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(member) as payload, target.open("xb") as output:
                    shutil.copyfileobj(payload, output, stream.CHUNK_BYTES)
                if target.stat().st_size != member.size:
                    raise fixture.FixtureError("truncated selected archive member")
                if path == ".meta/index.json":
                    index = corpus.load_index(destination)
                    cases = [case for case in index["cases"].values()
                             if case["fork"] == "Osaka" and case["format"] in EXPECTED_COUNTS]
                    counts = dict(Counter(case["format"] for case in cases))
                    if counts != EXPECTED_COUNTS:
                        raise fixture.FixtureError("pinned Osaka census differs from expected scope")
                    selected_paths = {case["json_path"] for case in cases}
                    del index, cases
        while decompressed.read(stream.CHUNK_BYTES):
            pass
    while hashed.read(stream.CHUNK_BYTES):
        pass
    if hashed.digest.hexdigest() != stream.ARCHIVE_SHA256:
        raise fixture.FixtureError("full archive SHA256 differs from immutable pin")
    if selected_paths is None or selected_paths - seen:
        raise fixture.FixtureError("archive lacks selected Osaka payloads")
    manifest = {"archive_sha256": stream.ARCHIVE_SHA256,
                "index_sha256": corpus.PINNED_INDEX_SHA256,
                "fixture_commit": corpus.PINNED_COMMIT,
                "fork": "Osaka", "counts": counts,
                "payload_files": len(selected_paths), "retained_bytes": retained}
    (destination / "acquisition.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--archive", type=Path, help="Use an existing official archive without downloading")
    args = parser.parse_args()
    try:
        source = args.archive.open("rb") if args.archive else urllib.request.urlopen(ARCHIVE_URL, timeout=120)
        with source:
            print(json.dumps(acquire(source, args.output), sort_keys=True))
    except (fixture.FixtureError, OSError, ValueError, tarfile.TarError) as error:
        parser.exit(2, f"Osaka acquisition error: {error}\n")


if __name__ == "__main__":
    main()
