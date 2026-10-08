"""Run the enforcing axiom gate selected for the current split repository."""

from __future__ import annotations

import subprocess
from pathlib import Path


GATES = {
    "BongTheory": Path("BongTest/CoreAxiomGate.lean"),
    "BeliPapers": Path("BeliTestSrc/BongTest/BeliPapersAxiomGate.lean"),
    "HePapers": Path("HeTestSrc/BongTest/HePapersAxiomGate.lean"),
}


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    gate = GATES.get(root.name)
    if gate is None or not (root / gate).is_file():
        raise RuntimeError(f"No enforcing axiom gate configured for {root.name}")
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
