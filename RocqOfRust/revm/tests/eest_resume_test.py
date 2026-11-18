#!/usr/bin/env python3
"""Checkpoint integrity tests without compiling or executing the native bridge."""
import io
import json
from pathlib import Path
import tempfile
import sys
from contextlib import redirect_stdout
import unittest
from unittest.mock import patch

import run_eest_corpus as runner
import verify_eest_corpus as verifier
import eest_corpus as corpus
import transaction_compare as compare
import transaction_fixture as fixture


class ResumeTests(unittest.TestCase):
    def setUp(self):
        self.case = {"id": "case-one", "format": "state_test"}
        self.index = {"pin": {"verified": False}, "cases": {"case-one": self.case}}
        self.execution = {"bridge_sha256": "a" * 64, "harness_sha256": "b" * 64,
                          "fuel": 100, "timeout_seconds": 2.0}
        self.record = {"protocol": corpus.RECORD_VERSION, "engine": compare.ENGINE,
                       "fixture": self.case, "pin": self.index["pin"], "fuel": 100,
                       "timeout_seconds": 2.0, "duration_seconds": 0.1,
                       "bridge_sha256": "a" * 64, "request_sha256": None,
                       "status": "fixture_error", "comparison": None,
                       "native_output": None, "reasons": ["example error"],
                       "execution": self.execution}

    def encoded(self, record=None):
        return (json.dumps(record or self.record) + "\n").encode()

    def test_resume_preserves_complete_records_and_discards_only_partial_tail(self):
        source = io.BytesIO(self.encoded() + b'{"fixture":')
        statuses = runner.resume_records(source, self.index, [self.case], self.execution)
        self.assertEqual(statuses, {"case-one": "fixture_error"})
        self.assertEqual(source.getvalue(), self.encoded())

    def test_complete_malformed_line_is_not_discarded(self):
        source = io.BytesIO(self.encoded() + b'{broken}\n')
        original = source.getvalue()
        with self.assertRaises(fixture.FixtureError):
            runner.resume_records(source, self.index, [self.case], self.execution)
        self.assertEqual(source.getvalue(), original)

    def test_duplicate_case_rejected(self):
        with self.assertRaises(fixture.FixtureError):
            runner.resume_records(io.BytesIO(self.encoded() * 2), self.index, [self.case], self.execution)

    def test_changed_execution_rejected(self):
        for key, value in (("bridge_sha256", "c" * 64), ("harness_sha256", "d" * 64),
                           ("fuel", 101), ("timeout_seconds", 3.0)):
            with self.subTest(key=key), self.assertRaises(fixture.FixtureError):
                runner.resume_records(io.BytesIO(self.encoded()), self.index, [self.case],
                                      dict(self.execution, **{key: value}))

    def test_changed_pin_rejected(self):
        with self.assertRaises(fixture.FixtureError):
            runner.resume_records(io.BytesIO(self.encoded()), {"pin": {"verified": True}},
                                  [self.case], self.execution)

    def test_changed_selection_manifest_differs(self):
        manifest = runner.checkpoint_manifest(self.index, [self.case], self.execution)
        self.assertNotEqual(manifest, runner.checkpoint_manifest(self.index, [], self.execution))

    def test_mixed_execution_cannot_be_verified_across_shards(self):
        other = dict(self.record, fixture={"id": "case-two", "format": "state_test"},
                     execution=dict(self.execution, harness_sha256="c" * 64))
        with self.assertRaisesRegex(fixture.FixtureError, "mix different"):
            verifier.verify_records(self.index, [self.case, other["fixture"]], [self.record, other])

    def test_legacy_records_cannot_mix_with_identified_records(self):
        other = dict(self.record, fixture={"id": "case-two", "format": "state_test"})
        del other["execution"]
        with self.assertRaisesRegex(fixture.FixtureError, "mix different"):
            verifier.verify_records(self.index, [self.case, other["fixture"]], [self.record, other])

    def test_consistent_records_verify(self):
        summary = verifier.verify_records(self.index, [self.case], [self.record])
        self.assertEqual(summary["selected"], 1)
        self.assertFalse(summary["all_selected_pass"])

    def test_changed_executable_aborts_before_bridge_start(self):
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / "bridge"
            executable.write_bytes(b"changed")
            with patch.object(runner.subprocess, "Popen") as launch:
                with self.assertRaises(runner.ExecutionIdentityError):
                    runner.bridge_exchange({}, executable, "request", 1,
                                           expected_hash="a" * 64)
                launch.assert_not_called()

    def test_identity_failure_is_not_recorded_as_fixture_error(self):
        case = dict(self.case, format="transaction_test", fork="Osaka")
        with patch.object(corpus, "load_test", return_value={}), \
                patch.object(runner.raw_format, "load_case", return_value={}), \
                patch.object(runner.raw_format, "serialize_input", return_value="request"), \
                patch.object(runner, "bridge_exchange", side_effect=runner.ExecutionIdentityError("changed")):
            with self.assertRaises(runner.ExecutionIdentityError):
                runner.run_case(self.index, case, {}, Path("bridge"), 100, 2, "a" * 64)

    def test_expected_executable_rejects_uniform_wrong_build(self):
        with self.assertRaisesRegex(fixture.FixtureError, "expected executable"):
            verifier.verify_records(self.index, [self.case], [self.record], "e" * 64)
        self.assertEqual(verifier.verify_records(self.index, [self.case], [self.record],
                                                "a" * 64)["selected"], 1)

    def test_empty_checkpoint_has_no_completed_work(self):
        self.assertEqual(runner.resume_records(io.BytesIO(), self.index, [self.case],
                                               self.execution), {})

    def test_cli_resume_skips_completed_work_and_rejects_changed_binary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / "bridge"
            executable.write_bytes(b"first executable")
            results = root / "results.jsonl"
            argv = ["runner", "--fixtures", str(root), "--bridge", str(executable),
                    "--results", str(results), "--fuel", "100", "--timeout", "2"]
            with patch.object(corpus, "selected_index", return_value=(self.index, [self.case])), \
                    patch.object(runner, "run_case", return_value=dict(self.record)) as run, \
                    patch.object(sys, "argv", argv), redirect_stdout(io.StringIO()):
                # The simulated runner must describe the executable actually identified.
                import hashlib
                run.return_value["bridge_sha256"] = hashlib.sha256(executable.read_bytes()).hexdigest()
                self.assertEqual(runner.main(), 1)
                run.assert_called_once()
                saved = results.read_bytes()
                run.reset_mock()
                with patch.object(sys, "argv", argv + ["--resume"]):
                    self.assertEqual(runner.main(), 1)
                run.assert_not_called()
                self.assertEqual(results.read_bytes(), saved)
                executable.write_bytes(b"changed executable")
                with patch.object(sys, "argv", argv + ["--resume"]), \
                        self.assertRaises(SystemExit) as error:
                    runner.main()
                self.assertEqual(error.exception.code, 2)
                run.assert_not_called()
                self.assertEqual(results.read_bytes(), saved)

    def test_execution_metadata_cannot_override_record_fields(self):
        other = dict(self.record, execution=dict(self.execution, fuel=101))
        with self.assertRaises(fixture.FixtureError):
            verifier.validate_record(self.index, self.case, other)


if __name__ == "__main__":
    unittest.main()
