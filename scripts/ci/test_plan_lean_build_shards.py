from __future__ import annotations

import unittest

import plan_lean_build_shards as planner


class LeanBuildShardPlanTests(unittest.TestCase):
    def test_plan_covers_every_nonumbrella_tracked_lean_module(self) -> None:
        all_paths = set(planner.all_tracked_lean_files())
        expected_paths = {
            path for path in all_paths
            if len(path.parts) >= 2 and path.parts[0] in planner.SOURCE_ROOTS
        }
        expected = {planner.module_name(path) for path in expected_paths}

        shards = planner.plan(6, 12)
        actual = [name for shard in shards for name in shard["modules"].split()]

        self.assertTrue(any(len(path.parts) > 2 for path in expected_paths))
        self.assertEqual(len(actual), len(set(actual)))
        self.assertEqual(set(actual), expected)
        self.assertEqual(sum(shard["moduleCount"] for shard in shards), len(expected))
        for shard in shards:
            self.assertEqual(shard["moduleCount"], len(shard["modules"].split()))
            if shard["axiomGate"]:
                self.assertTrue(shard["buildModules"].endswith(" BongTest.AxiomGate"))
            else:
                self.assertEqual(shard["buildModules"], shard["modules"])


if __name__ == "__main__":
    unittest.main()
