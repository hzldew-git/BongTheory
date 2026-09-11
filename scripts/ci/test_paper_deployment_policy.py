from __future__ import annotations

import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def paper_manifests() -> list[tuple[Path, dict[str, object]]]:
    manifests = []
    for path in sorted((ROOT / "papers").glob("*/paper.json")):
        manifests.append((path, json.loads(path.read_text(encoding="utf-8"))))
    return manifests


class PaperDeploymentPolicyTests(unittest.TestCase):
    def test_every_paper_has_a_unique_theorem_index_prefix(self) -> None:
        manifests = paper_manifests()
        theorem_index = (ROOT / "THEOREM_INDEX.md").read_text(encoding="utf-8")
        prefixes: list[str] = []
        for path, manifest in manifests:
            prefix = manifest.get("theoremIndexRowPrefix")
            with self.subTest(manifest=path.parent.name):
                self.assertIsInstance(prefix, str)
                assert isinstance(prefix, str)
                self.assertTrue(prefix.strip())
                self.assertNotRegex(prefix, r"[|\r\n]")
                self.assertIn(f"| {prefix}", theorem_index)
            prefixes.append(prefix)
        self.assertEqual(len(prefixes), len(set(prefixes)))

    def test_review_kit_generates_paper_specific_review_materials(self) -> None:
        generator = (
            ROOT / "scripts/paper-kits/Build-PaperReviewKit.ps1"
        ).read_text(encoding="utf-8")
        fixed_block = generator.split("$fixedFiles = @(", 1)[1].split(")", 1)[0]
        for global_review_file in (
            "CITATION.cff",
            "SOURCES.md",
            "TRUST.md",
            "THEOREM_INDEX.md",
            "REVIEWING.md",
            "docs/audit/README.md",
            "docs/audit/IndependentReviewSignoff.md",
        ):
            with self.subTest(file=global_review_file):
                self.assertNotIn(f"'{global_review_file}'", fixed_block)
        self.assertIn("theoremIndexRowPrefix", generator)
        self.assertIn("Rows for unrelated papers are intentionally excluded", generator)
        verifier = (
            ROOT / "scripts/paper-kits/Test-PaperReviewKit.ps1"
        ).read_text(encoding="utf-8")
        self.assertIn("Unrelated theorem-index row", verifier)
        self.assertIn("exactly its own paper-specific audit directory", verifier)

    def test_every_deployment_override_is_typed_and_explained(self) -> None:
        manifests = paper_manifests()
        self.assertTrue(manifests)
        for path, manifest in manifests:
            deployment = manifest.get("deployment")
            if deployment is None:
                continue
            with self.subTest(manifest=path.parent.name):
                self.assertIsInstance(deployment, dict)
                github_review_kit = deployment.get("githubReviewKit")
                self.assertIsInstance(github_review_kit, bool)
                if github_review_kit is False:
                    reason = deployment.get("reason")
                    self.assertIsInstance(reason, str)
                    self.assertTrue(reason.strip())

    def test_github_workflows_use_manifest_policy(self) -> None:
        review_workflow = (ROOT / ".github/workflows/paper-review-kits.yml").read_text(
            encoding="utf-8"
        )
        release_workflow = (ROOT / ".github/workflows/reproducibility.yml").read_text(
            encoding="utf-8"
        )
        build_all = (ROOT / "scripts/paper-kits/Build-AllPaperReviewKits.ps1").read_text(
            encoding="utf-8"
        )
        self.assertIn("deployment.githubReviewKit", review_workflow)
        self.assertIn("-GitHubDeployableOnly", review_workflow)
        self.assertIn("deployment.githubReviewKit", release_workflow)
        self.assertIn("GitHubDeployableOnly", build_all)

    def test_exact_review_kit_receipts_have_valid_archive_hashes(self) -> None:
        receipts = sorted((ROOT / "docs" / "audit").rglob("*review_kit_receipt.md"))
        self.assertTrue(receipts)
        digest_pattern = re.compile(r"- SHA-256:\s*`([0-9A-F]+)`")
        for path in receipts:
            text = path.read_text(encoding="utf-8")
            digests = digest_pattern.findall(text)
            with self.subTest(receipt=path.relative_to(ROOT)):
                self.assertTrue(digests)
                for digest in digests:
                    self.assertRegex(digest, r"^[0-9A-F]{64}$")
                self.assertNotIn("outer archive itself", text)


if __name__ == "__main__":
    unittest.main()
