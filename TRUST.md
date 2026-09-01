# Trust boundary

This project separates three claims that must not be conflated.

1. **Kernel acceptance.** Lean accepts the encoded declarations and proof
   terms.
2. **Technical reproducibility.** A clean checkout can reconstruct and check
   those declarations from pinned inputs.
3. **Semantic fidelity.** The encoded definitions, hypotheses, quantifiers,
   endpoints, and conclusions agree with the identified paper versions.

The first two can be mechanically checked. The third also requires
independent mathematical and formalization review.

## Public proof boundary

`BongTest/FinalPublicTheoremAudit.lean` checks the public Beli endpoints. Their
elaborated signatures contain the standard field/module/topology assumptions
and `DyadicContext`; they contain no project-specific `...Laws` or `...Data`
parameters. `DyadicContext` packages a nonarchimedean local field with a
normalized valuation, a chosen uniformizer, and positive valuation of `2`.
It does not contain a Beli classification or representation conclusion.

The public endpoints report only `propext`, `Classical.choice`, and
`Quot.sound`. These are standard Lean/mathlib logical dependencies. No use of
`sorry`, `sorryAx`, a project `axiom`, `unsafe`, `extern`, `implemented_by`,
`native_decide`, or `run_tac` occurs in the formal source. Occurrences of the
English word “admit” are prose in documentation comments, not Lean commands.

Three `noncomputable opaque` declarations have explicit proof bodies:

- `Lattice.JordanDecomposition.saturationStepResult`;
- `Lattice.omearaTwoPlaneAddLatticeIsometry`;
- `Lattice.omearaTwoPlaneSquareAddLatticeIsometry`.

Opacity prevents client reduction; it does not make these declarations
axioms. Their axiom reports contain the same standard set.

## Current semantic status

The current machine-assisted audit found no critical mismatch in the public
theorem correspondences. The status remains `PROVISIONAL_MATCH`, Grade B,
until a paper author or independent domain expert and an independent Lean
expert record their decisions in the review package. Compilation is not an
independent semantic endorsement.

The Beli 2020 package has coverage status
`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`.  Its direct Theorem 3.1
endpoint uses the coefficient obtained by substitution into Theorem 2.1; the
paper's printed coefficient is exposed separately and proved equivalent under
the documented zero-scale hypothesis.  This source-level difference remains
part of the semantic review boundary.
