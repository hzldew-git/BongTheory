#!/usr/bin/env python3
"""Plan deterministic build shards for any repository in the three-way split."""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "MIGRATION_MODULES.tsv"


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    weight: int


def migration_rows() -> list[dict[str, str]]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def all_tracked_lean_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return sorted(Path(item.decode()) for item in result.stdout.split(b"\0") if item)


def module_name(path: Path) -> str:
    for row in migration_rows():
        if Path(row["destination_path"]) == path:
            return row["module"]
    raise RuntimeError(f"Tracked Lean source is absent from MIGRATION_MODULES.tsv: {path}")


def source_weight(path: Path) -> int:
    text = (ROOT / path).read_text(encoding="utf-8-sig")
    imports = sum(line.lstrip().startswith("import ") for line in text.splitlines())
    return len(text.encode("utf-8")) + 20_000 * imports


def tracked_modules() -> list[Module]:
    tracked = set(all_tracked_lean_files())
    modules: list[Module] = []
    missing: list[Path] = []
    for row in migration_rows():
        path = Path(row["destination_path"])
        if path not in tracked:
            missing.append(path)
        else:
            modules.append(Module(row["module"], path, source_weight(path)))
    if missing:
        raise RuntimeError(f"Manifest modules are not tracked: {missing}")
    return modules


def partition(modules: list[Module], count: int, prefix: str) -> list[dict[str, object]]:
    bins: list[list[Module]] = [[] for _ in range(count)]
    loads = [0] * count
    for module in sorted(modules, key=lambda item: (-item.weight, item.name)):
        target = min(range(count), key=lambda index: (loads[index], index))
        bins[target].append(module)
        loads[target] += module.weight
    return [
        {
            "name": f"{prefix}-{index:02d}",
            "modules": " ".join(sorted(item.name for item in items)),
            "moduleCount": len(items),
        }
        for index, items in enumerate(bins, start=1)
        if items
    ]


def plan(production_shards: int, test_shards: int) -> list[dict[str, object]]:
    modules = tracked_modules()
    production = [module for module in modules if module.name.startswith("Bong.")]
    tests = [module for module in modules if module.name.startswith("BongTest.")]
    shards = partition(production, production_shards, "production")
    shards += partition(tests, test_shards, "tests")
    actual = [name for shard in shards for name in str(shard["modules"]).split()]
    expected = {module.name for module in modules}
    if len(actual) != len(set(actual)) or set(actual) != expected:
        raise RuntimeError("CI shard plan does not cover every manifest module exactly once")
    return shards


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--production-shards", type=int, default=6)
    parser.add_argument("--test-shards", type=int, default=12)
    parser.add_argument("--github-output", type=Path)
    args = parser.parse_args()
    if args.production_shards <= 0 or args.test_shards <= 0:
        parser.error("shard counts must be positive")
    shards = plan(args.production_shards, args.test_shards)
    payload = json.dumps(shards, separators=(",", ":"))
    if args.github_output:
        with args.github_output.open("a", encoding="utf-8", newline="\n") as stream:
            stream.write(f"matrix={payload}\n")
    print(
        f"LEAN_SHARD_PLAN_PASS: {sum(int(item['moduleCount']) for item in shards)} "
        f"manifest modules in {len(shards)} shards"
    )


if __name__ == "__main__":
    main()
