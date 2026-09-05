"""Exercise the actual Lean gate on positive and forbidden-dependency fixtures.

Negative examples are deliberately not mathematical project modules. They
are supplied to Lean on stdin, and must produce both a nonzero exit and the
gate's own rejection marker. A syntax/import failure cannot count as a pass.
"""

from __future__ import annotations

import subprocess
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    fixtures = [
        ("constructive", "theorem Bong.probe : True := True.intro", "PASS", None),
        ("standard", "theorem Bong.probe (p q : Prop) (h : p ↔ q) : p = q := propext h",
         "PASS", None),
        ("unfinished", "theorem Bong.probe : False := by sorry", "REJECT", "sorryAx"),
        ("custom", "axiom Bong.probe : False", "REJECT", "Bong.probe"),
        ("transitive", "axiom Outside.bad : False\ndef Outside.bridge : False := Outside.bad\n"
         "theorem Bong.probe : False := Outside.bridge", "REJECT", "Outside.bad"),
        ("private", "namespace Bong\nprivate axiom bad : False\n"
         "theorem probe : False := bad\nend Bong", "REJECT", "bad"),
        ("native", "theorem Bong.probe : 1 + 1 = 2 := by native_decide",
         "REJECT", "native_decide"),
        ("empty", "", "EMPTY", None),
        ("owned-positive", "def Outside.probe : Nat := 0", "PASS", None),
        ("owned-outside", "axiom Outside.bad : False", "REJECT", "Outside.bad"),
        ("owned-private-unused", "namespace Bong\nprivate axiom bad : False\nend Bong",
         "REJECT", "bad"),
    ]
    for label, declaration, outcome, dependency in fixtures:
        scope = "#[(← Lean.getEnv).mainModule]" if label.startswith("owned-") else "#[`Bong]"
        source = ("import BongTest.AxiomGate\n" + declaration
                  + "\nrun_cmd BongCI.checkAxioms " + scope + "\n")
        result = subprocess.run(
            ["lake", "env", "lean", "--stdin"], cwd=root,
            input=source, text=True, encoding="utf-8", stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        marker = "AXIOM_GATE_" + outcome
        correct_exit = result.returncode == 0 if outcome == "PASS" else result.returncode != 0
        if not correct_exit or marker not in result.stdout or (
                dependency is not None and dependency not in result.stdout):
            print(f"FAIL {label}: exit {result.returncode}\n{result.stdout}", flush=True)
            return 1
        print(f"PASS {label}: Lean exit {result.returncode}, {marker}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
