"""Diagnostic grouping is separate from evidence and coverage verification."""

import unittest

import summarize_eest_failures as diagnostic
import transaction_fixture as fixture


def record(case_id, status="incomplete", reasons=None):
    return {"fixture": {"id": case_id}, "status": status, "reasons": reasons or []}


class DiagnosticTests(unittest.TestCase):
    def test_groups_variants_by_status_and_function_with_three_examples(self):
        records = [record(f"path/test_x.py::test_x[i={i}]", reasons=[str(i)]) for i in range(5)]
        records += [record("path/test_x.py::test_x[i=5]", "timeout"),
                    record("path/test_y.py::test_y", "mismatch"),
                    record("path/test_x.py::test_x[i=6]", "pass")]
        result = diagnostic.summarize(records)
        assert result["scope"] == "diagnostic_only"
        assert result["observed_records"] == 8
        assert len(result["groups"]) == 3
        largest = result["groups"][0]
        assert largest["test_function"] == "path/test_x.py::test_x"
        assert largest["count"] == 5
        assert len(largest["examples"]) == 3
        assert largest["examples"][0]["reasons"] == ["0"]

    def test_empty_report_never_claims_passing_or_complete(self):
        result = diagnostic.summarize([])
        assert result["groups"] == []
        assert result["scope"] == "diagnostic_only"
        assert "all_selected_pass" not in result
        assert "complete" not in result

    def test_malformed_record_is_rejected(self):
        for invalid in ({}, record("x", reasons=[None]), record(42)):
            with self.assertRaises(fixture.FixtureError):
                diagnostic.summarize([invalid])


if __name__ == "__main__":
    unittest.main()
