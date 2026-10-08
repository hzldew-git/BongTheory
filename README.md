# BongTheory

`BongTheory` is the reusable Lean 4 foundation for quadratic lattices and
bases of norm generators over dyadic local fields. It contains definitions,
local quadratic-lattice infrastructure, BONG constructions, and results whose
proof dependencies are independent of the paper-specific Beli and He layers.

The formalizations of papers by Constantin N. Beli are maintained in the
downstream `BeliPapers` package. Formalizations of papers by Zilong He and his
collaborators are maintained in `HePapers`.

## Reproduce

The project pins Lean and Mathlib. From a fresh checkout, run:

```text
lake exe cache get
lake build
lake env lean BongTest/CoreAxiomGate.lean
```

The enforcing gate rejects transitive axioms other than `propext`,
`Classical.choice`, and `Quot.sound` for declarations in namespace `Bong`.
Compilation establishes kernel acceptance of the encoded statements; it does
not establish that a paper has been translated faithfully.

See `SOURCES.md` for the attribution boundary, `TRUST.md` for the trust model,
and `PUBLISHING.md` for the clean-clone release gate.

## Split provenance

This candidate was extracted from `hzldew-git/BongTheory` public commit
`a81fa2edf7d79c7740ea58539b809ce93f1612c0`, with the He Classic additions
recorded at local clean commit `1f3d92e7419db481c0e1ac229c5b7c0b1fdc5dd7`.
See `MIGRATION.md` and `MIGRATION_MODULES.tsv`.
