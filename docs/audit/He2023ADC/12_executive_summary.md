# Executive summary

Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), 981--1022, publisher version of record.

Proof assistant: Lean 4.32.1. The new profile proof checkpoint is
`2a151a8024d10ae094df958cd3626dbd13c447c2`.

The concrete dyadic development now contains the ADC definition, maximal
testing, equal-rank and stable-rank equivalences, Section 3 endpoints, and
substantial Section 4 foundations. The new Lemma 4.11--4.12 endpoints prove
arbitrary-lattice equivalences for all ten displayed canonical-model branches,
using maximal volume and good-BONG order invariance. Their focused kernel and
axiom checks pass.

Global definitions and regularity are present as abstract predicates. The
global reductions still require arithmetic premises whose concrete proofs
have not been supplied. Non-dyadic results, the ADC classifications in
Sections 6--7, global classifications and enumeration remain incomplete.

Semantic status: provisional, with unsigned human review cards and remaining
model/notation checks. Trust status: the new concrete endpoints use only the
standard logical axioms; conditional global inputs remain explicit.
Reproducibility status: incremental checks passed; exact-revision clean-kit
validation remains required. Coverage grade: C. Whole-paper verdict:
`NOT_COMPLETE`.
