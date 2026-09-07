from __future__ import annotations

import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]


def paper_manifests() -> list[tuple[Path, dict[str, object]]]:
    manifests = []
    for path in sorted((ROOT / "papers").glob("*/paper.json")):
        manifests.append((path, json.loads(path.read_text(encoding="utf-8"))))
    return manifests


class PaperDeploymentPolicyTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
