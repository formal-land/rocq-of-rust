#!/usr/bin/env python3
"""Run every selected pinned fixture with explicit accounting and signed Rocq requests."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import math
import os
from pathlib import Path
import resource
import selectors
import subprocess
import tempfile
import time
import json

import eest_corpus as corpus
import transaction_compare as compare
import transaction_fixture as fixture
import transaction_format as raw_format


STATUSES = {"pass", "authenticated_state_pass", "validated_state_rejection", "validated_transaction_pass", "validated_transaction_rejection", "execution_only", "mismatch",
            "authentication_mismatch", "unsupported", "incomplete", "timeout",
            "runner_error", "fixture_error", "internal_error"}
MAX_ADDRESS_SPACE = 2 * 1024 * 1024 * 1024
MAX_STDERR_BYTES = 8 * 1024 * 1024
MAX_ERROR_CHARS = 4096
DEFAULT_BRIDGE = Path(__file__).resolve().parents[3] / "target/revm-native/native_transaction_bridge"


def check_limits(fuel: int, timeout: float):
    if type(fuel) is not int or not 0 <= fuel <= compare.MAX_FUEL:
        raise fixture.FixtureError("fuel must be within extracted bridge limits")
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
        raise fixture.FixtureError("timeout must be a finite positive number")


def child_limits():
    for limit, maximum in ((resource.RLIMIT_AS, MAX_ADDRESS_SPACE),
                           (resource.RLIMIT_CORE, 0), (resource.RLIMIT_FSIZE, MAX_STDERR_BYTES)):
        soft, hard = resource.getrlimit(limit)
        finite = [value for value in (soft, hard, maximum) if value != resource.RLIM_INFINITY]
        bounded = min(finite)
        resource.setrlimit(limit, (bounded, bounded))
    # The extracted list operations in large identity-precompile calls need
    # more than the process default. AS still caps the total address space.
    _, hard_stack = resource.getrlimit(resource.RLIMIT_STACK)
    stack_limit = 64 * 1024 * 1024
    if hard_stack != resource.RLIM_INFINITY:
        stack_limit = min(stack_limit, hard_stack)
    resource.setrlimit(resource.RLIMIT_STACK, (stack_limit, stack_limit))


def bounded_message(value) -> str:
    message = str(value)
    return message if len(message) <= MAX_ERROR_CHARS else message[:MAX_ERROR_CHARS] + " [truncated]"


def stop_bridge(bridge: dict) -> str:
    diagnostic = ""
    process = bridge.get("process")
    if process is not None:
        if process.poll() is None:
            process.kill()
        process.wait()
        process.stdin.close()
        process.stdout.close()
        errors = bridge["stderr"]
        size = errors.seek(0, os.SEEK_END)
        errors.seek(max(0, size - MAX_ERROR_CHARS))
        diagnostic = errors.read(MAX_ERROR_CHARS).decode("utf-8", errors="replace").strip()
        errors.close()
    bridge.clear()
    return diagnostic


def bridge_exchange(bridge: dict, executable: Path, request: str, timeout: float,
                    parse_result=compare.parse_output) -> dict:
    """One persistent JSONL request with a wall deadline covering both pipe directions."""
    deadline = time.monotonic() + timeout
    try:
        if not bridge:
            errors = tempfile.TemporaryFile()
            try:
                process = subprocess.Popen([str(executable)], stdin=subprocess.PIPE,
                                           stdout=subprocess.PIPE, stderr=errors, bufsize=0,
                                           preexec_fn=child_limits)
            except OSError:
                errors.close()
                raise
            bridge.update(process=process, stderr=errors)
            os.set_blocking(process.stdin.fileno(), False)
            os.set_blocking(process.stdout.fileno(), False)
        process = bridge["process"]
        if process.poll() is not None:
            raise fixture.FixtureError(f"native bridge exited with status {process.returncode}")
        remaining = memoryview(request.encode())
        received = bytearray()
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdin, selectors.EVENT_WRITE)
            selector.register(process.stdout, selectors.EVENT_READ)
            while True:
                wait = deadline - time.monotonic()
                if wait <= 0:
                    raise TimeoutError("native bridge exceeded per-case wall deadline")
                events = selector.select(wait)
                if not events:
                    raise TimeoutError("native bridge exceeded per-case wall deadline")
                for key, _ in events:
                    if key.fileobj is process.stdin:
                        sent = os.write(process.stdin.fileno(), remaining[:65536])
                        remaining = remaining[sent:]
                        if not remaining:
                            selector.unregister(process.stdin)
                    else:
                        chunk = os.read(process.stdout.fileno(), 65536)
                        if not chunk:
                            raise fixture.FixtureError("native bridge closed output without a complete result")
                        received.extend(chunk)
                        if len(received) > compare.MAX_WIRE_BYTES:
                            raise fixture.FixtureError("native bridge output exceeds wire limit")
                        if b"\n" in received:
                            line, extra = received.split(b"\n", 1)
                            if remaining or extra:
                                raise fixture.FixtureError("native bridge emitted unexpected additional/early output")
                            return parse_result(line.decode("utf-8"))
    except Exception as error:
        diagnostic = stop_bridge(bridge)
        if diagnostic:
            message = bounded_message(f"{error}; bridge stderr: {diagnostic}")
            if isinstance(error, TimeoutError):
                raise TimeoutError(message) from error
            raise fixture.FixtureError(message) from error
        raise


def parse_native_output(case: dict, encoded: str) -> dict:
    if case["format"] == "transaction_test":
        return raw_format.parse_output(encoded)
    if case["format"] == "state_test":
        return compare.parse_output(encoded)
    raise fixture.FixtureError("native output has no parser for selected fixture format")


def serialize_case_request(index: dict, case: dict, fuel: int) -> str:
    if case["format"] == "transaction_test":
        return raw_format.serialize_input(raw_format.load_case(index, case))
    return compare.serialize_input(corpus.normalize(index, case), fuel, signed=True)


def classification(index: dict, case: dict, output: dict, test: dict | None = None) -> tuple[str, dict]:
    if case["format"] == "transaction_test":
        result = raw_format.compare_result(raw_format.load_case(index, case, test), output)
    else:
        result = compare.compare_execution(corpus.normalize(index, case, test), output)
    passes = {"authenticated_state_pass", "validated_state_rejection"} | raw_format.PASS_CLASSIFICATIONS
    result["fixture_identity_verified"] = index["pin"]["verified"]
    result["full_eest_pass"] = index["pin"]["verified"] and result["classification"] in passes
    status = result["classification"]
    if status in passes and index["pin"]["verified"]:
        status = "pass"
    elif status == "execution_pass":
        status = "execution_only"
    elif status in {"execution_mismatch", "transaction_mismatch"}:
        status = "mismatch"
    return status, result

def run_case(index: dict, case: dict, bridge: dict, executable: Path,
             fuel: int, timeout: float, executable_hash: str | None = None) -> dict:
    check_limits(fuel, timeout)
    started = time.monotonic()
    record = {"protocol": corpus.RECORD_VERSION, "engine": compare.ENGINE,
              "fixture": dict(case), "pin": dict(index["pin"]),
              "fuel": fuel, "timeout_seconds": timeout, "duration_seconds": 0,
              "bridge_sha256": executable_hash, "request_sha256": None,
              "status": "fixture_error", "comparison": None, "native_output": None,
              "reasons": []}
    try:
        test = corpus.load_test(index, case)
        if case["format"] == "transaction_test" and case["fork"] in fixture.SUPPORTED_FORKS:
            normalized = raw_format.load_case(index, case, test)
            request = raw_format.serialize_input(normalized)
            record["request_sha256"] = hashlib.sha256(request.encode()).hexdigest()
            record["status"] = "runner_error"
            output = bridge_exchange(bridge, executable, request, timeout, raw_format.parse_output)
            record["native_output"] = output
            status, comparison = classification(index, case, output, test)
            record.update(status=status, comparison=comparison, reasons=comparison.get("reasons", []))
        elif case["format"] not in {"state_test", "transaction_test"}:
            record.update(status="unsupported", reasons=["format:" + case["format"]])
        elif case["fork"] not in fixture.SUPPORTED_FORKS:
            record.update(status="unsupported", reasons=["fork:" + case["fork"]])
        else:
            normalized = corpus.normalize(index, case, test)
            gaps = compare.execution_gaps(normalized, True)
            if normalized["expectation"]["txbytes"] is None:
                gaps.append("missing_signed_transaction")
            if gaps:
                record.update(status="unsupported", reasons=gaps)
            else:
                request = compare.serialize_input(normalized, fuel, signed=True)
                record["request_sha256"] = hashlib.sha256(request.encode()).hexdigest()
                record["status"] = "runner_error"
                output = bridge_exchange(bridge, executable, request, timeout)
                record["native_output"] = output
                status, comparison = classification(index, case, output, test)
                record.update(status=status, comparison=comparison,
                              reasons=comparison.get("reasons", []))
    except TimeoutError as error:
        record.update(status="timeout", reasons=[bounded_message(error)])
    except (fixture.FixtureError, OSError, UnicodeError, ValueError) as error:
        record["reasons"] = [bounded_message(error)]
    except Exception as error:
        record.update(status="internal_error", reasons=[bounded_message(f"{type(error).__name__}: {error}")])
    finally:
        record["duration_seconds"] = time.monotonic() - started
        if record["status"] not in {"pass", "authenticated_state_pass", "validated_transaction_pass", "validated_transaction_rejection"}:
            stop_bridge(bridge)
    return record


def summarize(index: dict, cases: list[dict], statuses: dict) -> dict:
    counts = Counter(statuses.values())
    all_pass = counts.get("pass", 0) == len(cases)
    selected = {case["id"] for case in cases}
    state_ids = {case["id"] for case in index["cases"].values() if case["format"] == "state_test"}
    state_pass = (index["pin"]["verified"] and state_ids <= selected
                  and all(statuses.get(case_id) == "pass" for case_id in state_ids)
                  and len(state_ids) == corpus.PINNED_COUNTS["state_test"])
    transaction_ids = {case["id"] for case in index["cases"].values() if case["format"] == "transaction_test"}
    transaction_pass = (index["pin"]["verified"] and transaction_ids <= selected
                        and all(statuses.get(case_id) == "pass" for case_id in transaction_ids)
                        and len(transaction_ids) == corpus.PINNED_COUNTS["transaction_test"])
    return {"protocol": corpus.RECORD_VERSION, "engine": compare.ENGINE,
            "pin": dict(index["pin"]), "selected": len(cases), "statuses": dict(sorted(counts.items())),
            "all_selected_pass": index["pin"]["verified"] and all_pass,
            "full_state_corpus_pass": state_pass,
            "full_transaction_corpus_pass": transaction_pass,
            "full_eest_corpus_pass": index["pin"]["verified"] and all_pass
                                     and selected == set(index["cases"]),
            "pinned_corpus_counts": corpus.PINNED_COUNTS,
            "unsupported_formats": [name for name in corpus.FORMAT_DIRECTORIES
                                    if name not in {"state_test", "transaction_test"}]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    corpus.add_selection_arguments(parser)
    parser.add_argument("--bridge", type=Path, default=DEFAULT_BRIDGE)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--summary", type=Path)
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    bridge = {}
    try:
        check_limits(args.fuel, args.timeout)
        index, cases = corpus.selected_index(args)
        executable = args.bridge.resolve()
        executable_hash = hashlib.sha256(executable.read_bytes()).hexdigest() if executable.is_file() else None
        statuses = {}
        # Exclusive creation prevents clobbering an earlier inventory or a parallel worker.
        with args.results.open("x", encoding="utf-8") as results:
            for case in cases:
                record = run_case(index, case, bridge, executable, args.fuel, args.timeout, executable_hash)
                statuses[case["id"]] = record["status"]
                results.write(json.dumps(record, separators=(",", ":"), allow_nan=False) + "\n")
                results.flush()
        summary = summarize(index, cases, statuses)
        if args.summary:
            with args.summary.open("x", encoding="utf-8") as output:
                output.write(json.dumps(summary, indent=2, allow_nan=False) + "\n")
        print(json.dumps(summary, sort_keys=True))
        return 0 if summary["all_selected_pass"] else 1
    except (fixture.FixtureError, OSError, ValueError) as error:
        parser.exit(2, f"EEST corpus error: {error}\n")
    finally:
        stop_bridge(bridge)


if __name__ == "__main__":
    raise SystemExit(main())
