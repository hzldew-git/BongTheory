from __future__ import annotations

import unittest

import plan_lean_build_shards as planner


class LeanBuildShardPlanTests(unittest.TestCase):
    def test_plan_covers_every_manifest_module_once(self) -> None:
        expected = {row["module"] for row in planner.migration_rows()}
        shards = planner.plan(6, 12)
        actual = [name for shard in shards for name in str(shard["modules"]).split()]
        self.assertEqual(len(actual), len(set(actual)))
        self.assertEqual(set(actual), expected)
        self.assertEqual(sum(int(shard["moduleCount"]) for shard in shards), len(expected))

    def test_every_manifest_destination_is_tracked(self) -> None:
        tracked = set(planner.all_tracked_lean_files())
        expected_paths = {planner.Path(row["destination_path"]) for row in planner.migration_rows()}
        self.assertTrue(expected_paths)
        self.assertTrue(expected_paths <= tracked)


if __name__ == "__main__":
    unittest.main()
