"""Integrity tests for source mappings and claims of complete verification."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

import paper_coverage as coverage


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="circular-law-coverage-test-")
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        (self.repo / "sections").mkdir()
        for source in list(coverage.REPO.glob("*.tex")) + list((coverage.REPO / "sections").glob("*.tex")):
            shutil.copy2(source, self.repo / source.relative_to(coverage.REPO))
        self.catalog = self.repo / "paper-coverage.json"
        shutil.copy2(coverage.CATALOG, self.catalog)
        self.data = json.loads(self.catalog.read_text())
        for name, value in (("REPO", self.repo), ("CATALOG", self.catalog)):
            patcher = patch.object(coverage, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_check(self, *arguments):
        self.catalog.write_text(json.dumps(self.data))
        with patch.object(sys, "argv", ["paper_coverage.py", *arguments]), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            return coverage.main()

    def test_manuscript_definition_change_requires_review(self):
        with (self.repo / "main.tex").open("a") as stream:
            stream.write("\n% Changed manuscript source\n")
        with self.assertRaisesRegex(ValueError, "manuscript source changed"):
            self.run_check()

    def test_valid_partial_catalog_passes(self):
        self.assertEqual(self.run_check(), 0)

    def test_missing_supporting_declaration_is_rejected(self):
        self.data["results"][0]["supporting_declarations"].append(
            "CircularLaw.coverage_integrity_missing_declaration"
        )
        self.assertEqual(self.run_check(), 1)

    def test_omitting_an_open_result_does_not_satisfy_coverage(self):
        self.data["results"].pop()
        with self.assertRaisesRegex(ValueError, "all manuscript result labels"):
            self.run_check()

    def test_proved_result_requires_a_proof_declaration(self):
        self.data["results"][0]["status"] = "proved"
        self.data["results"][0]["proof_declaration"] = None
        with self.assertRaisesRegex(ValueError, "requires a target proposition and its proof"):
            self.run_check()

    def test_lean_rejects_a_proof_of_a_different_statement(self):
        item = next(item for item in self.data["results"] if item["label"] == "lem:max-weight")
        item["statement_declaration"] = "CircularLaw.MainTheorem"
        self.assertEqual(self.run_check(), 1)

    def test_full_paper_gate_rejects_any_missing_result(self):
        self.data["results"][0]["status"] = "open"
        self.assertEqual(self.run_check("--require-complete"), 1)


if __name__ == "__main__":
    unittest.main()
