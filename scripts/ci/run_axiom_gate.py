"""Import every tracked production module, then enforce transitive axiom bounds.

Requires a successful Lake build. All generated Lean input stays in memory;
the repository and dependencies are not edited. Import errors, empty scans,
forbidden dependencies and a missing success marker all fail the command.
"""

from __future__ import annotations

import subprocess
import argparse
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--entry", action="append", default=[],
                        help="Focused imported-closure check, not the complete project gate")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    tracked = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=root, check=True, stdout=subprocess.PIPE,
    ).stdout.decode("utf-8").split("\0")
    paths = sorted(path for path in tracked if path in ("Bong.lean", "BongTest.lean")
                   or path.startswith("Bong/"))
    if not paths:
        raise RuntimeError("No project modules were found")
    modules = args.entry or [path.removesuffix(".lean").replace("/", ".") for path in paths]
    imports = ["import " + module for module in modules] + ["import BongTest.AxiomGate"]
    source = "\n".join(imports) + (
        "\nset_option maxHeartbeats 0\n"
        "run_cmd BongCI.checkAxioms #[`Bong, `BongTest]\n"
    )
    scope = "focused imported closure" if args.entry else "all tracked production modules and audit-root closure"
    print(f"Checking {scope}: {len(modules)} imports", flush=True)
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"], cwd=root,
        input=source, text=True, encoding="utf-8", stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    print(result.stdout, end="", flush=True)
    if result.returncode or "AXIOM_GATE_PASS:" not in result.stdout:
        return result.returncode or 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
