# Trust and axiom report

## Focused kernel audit

`BongTest/Beli2020Audit.lean` checks and prints axioms for:

- the Section 2 preliminary reductions and Theorem 2.1;
- the arbitrary-Jordan and literal zero-scale Theorem 3.1 endpoints;
- Lemmas 4.1--4.9;
- all four clauses of Corollary 4.5;
- Corollary 4.10.

Every advertised proved endpoint reports only some or all of:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

These are standard Lean/mathlib logical dependencies.  No project-defined
axiom appears in the reports.

## Placeholder and interface boundary

The audited modules contain no `sorry`, `admit`, `sorryAx`, project
`axiom`, proof-hiding `opaque`, external oracle, or unsafe computation
used as a proof.  Public paper endpoints contain no project-specific
`...Laws` or `...Data` parameters.

Internal structures such as `UniversalLemma49AdaptedData` are constructed by
checked proof terms.  Their presence in implementation lemmas does not enlarge
the assumptions of the public results.

## Why compilation is not enough

`#print axioms` establishes the kernel trust boundary, not source fidelity.
It cannot decide whether an index shift or printed exponent agrees with the
paper.  The Theorem 3.1 normalization discrepancy is therefore tracked in the
correspondence report even though both formal predicates and all proved
comparisons have the standard axiom set.

## Trusted computing base

- Lean 4.32.1 kernel;
- pinned mathlib revision from `lake-manifest.json`;
- the current source files and generated `.olean` artifacts;
- the local executable, filesystem, and operating system.
