#!/usr/bin/env python3
"""Plan deterministic CI shards covering every tracked Lean source module."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOTS = {"Bong", "BongTest"}
UMBRELLAS = {Path("Bong.lean"), Path("BongTest.lean")}
IMPORT_LINE = re.compile(r"import ([A-Za-z0-9_'.]+)")


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    weight: int


def all_tracked_lean_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    paths = [Path(item.decode()) for item in result.stdout.split(b"\0") if item]
    return sorted(paths)


def validate_umbrellas(paths: set[Path]) -> None:
    for umbrella in sorted(UMBRELLAS):
        imports: list[str] = []
        for line_number, line in enumerate(
                (ROOT / umbrella).read_text(encoding="utf-8").splitlines(), start=1):
            stripped = line.strip()
            if not stripped or stripped.startswith("--"):
                continue
            match = IMPORT_LINE.fullmatch(stripped)
            if match is None:
                raise RuntimeError(
                    f"{umbrella}:{line_number} is not an import-only umbrella line"
                )
            imports.append(match.group(1))
        if not imports:
            raise RuntimeError(f"{umbrella} has no imports")
        if len(imports) != len(set(imports)):
            raise RuntimeError(f"{umbrella} contains duplicate imports")
        missing = sorted(
            name for name in imports
            if Path(*name.split(".")).with_suffix(".lean") not in paths
        )
        if missing:
            raise RuntimeError(f"{umbrella} imports untracked modules: {missing}")


def tracked_lean_files() -> list[Path]:
    all_paths = set(all_tracked_lean_files())
    unexpected = sorted(
        path for path in all_paths
        if path not in UMBRELLAS
        and (len(path.parts) < 2 or path.parts[0] not in SOURCE_ROOTS)
    )
    if unexpected:
        raise RuntimeError(f"Lean sources outside the covered roots: {unexpected}")
    missing_umbrellas = sorted(UMBRELLAS - all_paths)
    if missing_umbrellas:
        raise RuntimeError(f"Missing tracked umbrella modules: {missing_umbrellas}")
    validate_umbrellas(all_paths)
    return sorted(all_paths - UMBRELLAS)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def source_weight(path: Path) -> int:
    text = (ROOT / path).read_text(encoding="utf-8")
    import_count = sum(line.lstrip().startswith("import ") for line in text.splitlines())
    return len(text.encode("utf-8")) + 20_000 * import_count


def partition(modules: list[Module], count: int, prefix: str, axiom_gate: bool) -> list[dict]:
    bins: list[list[Module]] = [[] for _ in range(count)]
    loads = [0] * count
    for module in sorted(modules, key=lambda item: (-item.weight, item.name)):
        target = min(range(count), key=lambda index: (loads[index], index))
        bins[target].append(module)
        loads[target] += module.weight
    shards = []
    for index, items in enumerate(bins, start=1):
        if not items:
            continue
        names = sorted(item.name for item in items)
        build_names = names + (["BongTest.AxiomGate"] if axiom_gate else [])
        shards.append(
            {
                "name": f"{prefix}-{index:02d}",
                "modules": " ".join(names),
                "buildModules": " ".join(build_names),
                "moduleCount": len(names),
                "axiomGate": axiom_gate,
            }
        )
    return shards


def plan(production_shards: int, test_shards: int) -> list[dict]:
    paths = tracked_lean_files()
    expected = {module_name(path) for path in paths}
    production = [
        Module(module_name(path), path, source_weight(path))
        for path in paths
        if path.parts[0] == "Bong"
    ]
    tests = [
        Module(module_name(path), path, source_weight(path))
        for path in paths
        if path.parts[0] == "BongTest"
    ]
    shards = partition(production, production_shards, "production", True)
    shards += partition(tests, test_shards, "tests", False)
    actual = [name for shard in shards for name in shard["modules"].split()]
    if len(actual) != len(set(actual)):
        raise RuntimeError("CI shard plan contains duplicate modules")
    if set(actual) != expected:
        missing = sorted(expected - set(actual))
        extra = sorted(set(actual) - expected)
        raise RuntimeError(f"CI shard coverage mismatch; missing={missing}, extra={extra}")
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
        f"LEAN_SHARD_PLAN_PASS: {sum(item['moduleCount'] for item in shards)} "
        f"modules in {len(shards)} shards; {len(UMBRELLAS)} import-only roots validated"
    )


if __name__ == "__main__":
    main()
