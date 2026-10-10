"""Ensure the shared dependency traversal still rejects forbidden axioms."""

from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    def test_rejects_a_disallowed_transitive_dependency(self):
        source = (ROOT / "Audit.lean").read_text()
        allowed = "#[``propext, ``Classical.choice, ``Quot.sound]"
        self.assertEqual(source.count(allowed), 1)
        # Deny a known existing dependency in a temporary audit. No axiom
        # or admitted proof is added to the project or to the test fixture.
        source = source.replace(allowed, "#[``propext, ``Quot.sound]")
        with tempfile.TemporaryDirectory(prefix="circular-law-audit-test-") as directory:
            fixture = Path(directory) / "RejectChoice.lean"
            fixture.write_text(source)
            result = subprocess.run(
                ["lake", "env", "lean", "-DwarningAsError=true", str(fixture)],
                cwd=ROOT, text=True, capture_output=True,
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("depends on disallowed axiom Classical.choice", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
