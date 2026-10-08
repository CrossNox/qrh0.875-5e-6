"""Check enforcement of the upstream proof revision."""

import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts import verify_oai


class UpstreamCheckoutTests(unittest.TestCase):
    def setUp(self) -> None:
        self.checkout_directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.checkout_directory.cleanup)
        self.upstream_repo = Path(self.checkout_directory.name)
        self.run_git("init", "--quiet")
        self.run_git("config", "user.name", "Verification test")
        self.run_git("config", "user.email", "verification@example.invalid")
        self.proof_source = self.upstream_repo / "Proof.lean"
        self.proof_source.write_text("theorem checked : True := True.intro\n")
        self.run_git("add", "Proof.lean")
        self.run_git("-c", "commit.gpgsign=false", "commit", "--quiet", "-m", "Add proof")
        self.expected_revision = self.run_git("rev-parse", "HEAD").strip()

    def run_git(self, *arguments: str) -> str:
        return subprocess.run(
            ["git", "-C", str(self.upstream_repo), *arguments],
            check=True,
            capture_output=True,
            text=True,
        ).stdout

    def test_accepts_clean_pinned_checkout(self) -> None:
        verify_oai.verify_upstream_checkout(self.upstream_repo, self.expected_revision)

    def test_rejects_wrong_revision(self) -> None:
        with self.assertRaisesRegex(ValueError, "revision mismatch"):
            verify_oai.verify_upstream_checkout(self.upstream_repo, "0" * 40)

    def test_rejects_modified_proof_at_pinned_revision(self) -> None:
        self.proof_source.write_text("axiom checked : False\n")
        with self.assertRaisesRegex(ValueError, "uncommitted changes"):
            verify_oai.verify_upstream_checkout(self.upstream_repo, self.expected_revision)

    def test_rejects_staged_proof_at_pinned_revision(self) -> None:
        self.proof_source.write_text("axiom checked : False\n")
        self.run_git("add", "Proof.lean")
        with self.assertRaisesRegex(ValueError, "uncommitted changes"):
            verify_oai.verify_upstream_checkout(self.upstream_repo, self.expected_revision)

    def test_rejects_untracked_source_at_pinned_revision(self) -> None:
        (self.upstream_repo / "Untracked.lean").write_text("axiom unproved : False\n")
        with self.assertRaisesRegex(ValueError, "uncommitted changes"):
            verify_oai.verify_upstream_checkout(self.upstream_repo, self.expected_revision)


if __name__ == "__main__":
    unittest.main()
