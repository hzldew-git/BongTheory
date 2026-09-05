# Executive summary

Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), 981--1022, publisher version of record.

Proof assistant: Lean 4.32.1. The current proof checkpoint is
`5fff59784a0a3dd4442405f204519c36e0a8e468`.

The concrete dyadic development now contains the ADC definition, maximal
testing, equal-rank and stable-rank equivalences, Section 3 endpoints, and
substantial Section 4 foundations. The new Lemma 4.11--4.12 endpoints prove
arbitrary-lattice equivalences for all ten concrete-model branches, and then
connect them to thirteen published `W/N` branches, including rank one.
The formerly missing space/lattice correspondence is now proved, and the
auxiliary defect and unit facts are derived internally. Their focused kernel
and axiom checks pass. See report 14 for the exact scope.

Proposition 4.13 is now proved in all three parts for arbitrary odd-rank
maximal lattices. The ternary boundary, the omission of the nonexistent
leftmost alpha cap, and the finite equality at 2e-1 passed separate AI review.
See report 15. No unit representative or order-profile premise was added.

Both clauses of Proposition 4.16 are also proved over dyadic fields. The
exact representation exception is accompanied by the integral isometry
`N_2^4(1) = A perp A^(pi)`, interpreted up to isometry, with the half-scaled
Gram matrix verified. Report 16 records this specialization; the published
proposition also includes non-dyadic fields and is not complete as a whole.

Global definitions and regularity are present as abstract predicates. The
global reductions still require arithmetic premises whose concrete proofs
have not been supplied. Non-dyadic results, the ADC classifications in
Sections 6--7, global classifications and enumeration remain incomplete.

Semantic status: provisional, with unsigned human review cards and remaining
semantic checks elsewhere in the paper. Trust status: the new concrete endpoints use only the
standard logical axioms; conditional global inputs remain explicit.
Reproducibility status: the published-profile tree passed clean-kit CI in run
33929872783; the later Proposition 4.13 and dyadic 4.16 proofs passed local checks but
still requires its own clean-kit run. Coverage grade: C. Whole-paper verdict:
`NOT_COMPLETE`.
