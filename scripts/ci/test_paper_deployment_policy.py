from __future__ import annotations

import csv
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def manifests() -> list[tuple[Path, dict[str, object]]]:
    return [
        (path, json.loads(path.read_text(encoding="utf-8-sig")))
        for path in sorted((ROOT / "papers").glob("*/paper.json"))
    ]


class PaperMetadataTests(unittest.TestCase):
    def test_manifest_entries_and_audits_are_migrated(self) -> None:
        papers = manifests()
        if not papers:
            self.skipTest("foundation repository has no paper manifests")
        with (ROOT / "MIGRATION_MODULES.tsv").open(encoding="utf-8") as handle:
            modules = {row["module"] for row in csv.DictReader(handle, delimiter="\t")}
        for path, manifest in papers:
            with self.subTest(manifest=path.parent.name):
                self.assertIn(manifest["entryModule"], modules)
                for audit in manifest.get("auditModules", []):
                    self.assertIn(audit, modules)
                self.assertTrue((ROOT / str(manifest["auditDirectory"])).is_dir())

    def test_theorem_prefixes_are_unique_and_present(self) -> None:
        papers = manifests()
        if not papers:
            self.skipTest("foundation repository has no paper manifests")
        theorem_index = (ROOT / "THEOREM_INDEX.md").read_text(encoding="utf-8")
        prefixes = [str(manifest["theoremIndexRowPrefix"]) for _, manifest in papers]
        self.assertEqual(len(prefixes), len(set(prefixes)))
        for prefix in prefixes:
            self.assertIn(f"| {prefix}", theorem_index)

    def test_source_hashes_have_sha256_shape(self) -> None:
        papers = manifests()
        if not papers:
            self.skipTest("foundation repository has no paper manifests")
        for path, manifest in papers:
            source = manifest.get("authoritativeSource")
            digest = source.get("sha256") if isinstance(source, dict) else manifest.get("sourceSha256")
            with self.subTest(manifest=path.parent.name):
                self.assertRegex(str(digest), r"^[0-9A-F]{64}$")


if __name__ == "__main__":
    unittest.main()
