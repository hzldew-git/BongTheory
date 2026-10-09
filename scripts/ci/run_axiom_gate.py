"""Run the complete or a CI-sharded enforcing axiom gate."""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


GATES = {
    "BongTheory": Path("BongTest/CoreAxiomGate.lean"),
    "BeliPapers": Path("BeliTestSrc/BongTest/BeliPapersAxiomGate.lean"),
    "HePapers": Path("HeTestSrc/BongTest/HePapersAxiomGate.lean"),
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--entry",
        action="append",
        default=[],
        help="Import and check one production module; repeat for a CI shard",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    gate = GATES.get(root.name)
    if gate is None or not (root / gate).is_file():
        raise RuntimeError(f"No enforcing axiom gate configured for {root.name}")
    if args.entry:
        invalid = [name for name in args.entry if not re.fullmatch(r"[A-Za-z0-9_'.]+", name)]
        if invalid:
            raise RuntimeError(f"Invalid Lean module names: {invalid}")
        source = "\n".join(
            [*(f"import {name}" for name in args.entry), "import BongTest.AxiomGate"]
        )
        source += "\nset_option maxHeartbeats 0 in\nrun_cmd BongCI.checkAxioms #[`Bong]\n"
        print(f"Checking focused production shard: {len(args.entry)} imports", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=root,
            input=source,
            text=True,
            encoding="utf-8",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    else:
        result = subprocess.run(
            ["lake", "env", "lean", gate.as_posix()],
            cwd=root,
            text=True,
            encoding="utf-8",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    print(result.stdout, end="", flush=True)
    if result.returncode or "AXIOM_GATE_PASS:" not in result.stdout:
        return result.returncode or 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
