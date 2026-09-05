# Executive summary

Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), 981--1022, publisher version of record.

Proof assistant: Lean 4.32.1. The current proof checkpoint is
`b0f832e5ff4dd1fe0f305371c029ce2015b004e5`.

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

All four clauses of Lemma 6.4 now pass local kernel and axiom checks. They
use the actual named maximal tests, retain the exact defect/order conclusions,
and cover the binary boundaries. Report 17 records independent review and
the remaining clean-kit obligations. Those testing clauses alone do not
complete either classification theorem.

Both clauses of Lemma 6.5 now also pass local checks and independent AI
review. The conclusions identify the exact failing Theorem 3.6(ii)
inequalities at n and n-1, with both named targets and n=2 covered. Report 18
records the capped-defect argument and pending clean-kit obligations.

Theorem 6.1 is now complete locally and independently AI-reviewed: for
every even n >= 2 and arbitrary full lattice of rank n+1, n-ADC is
equivalent to maximality. The endpoint constructs its own good BONG and
retains no profile or law premise. The necessity proof uses actual tests,
concrete ambient embeddings and a proved maximal-superlattice volume
argument. Report 19 records the 12 new standard-only axiom queries and the
n=2/e=1 checks. This completes 1/2 of Section 6's numbered classification
theorems, not Theorem 6.2.

Both Lemma 6.6 clauses are also complete locally and independently
AI-reviewed. They use the exact published central trigger, distinguish
raw and capped defects, and prove the required prefix-space exclusion
for arbitrary good BONGs on the actual targets. All 12 new queries have
the standard-only axiom set. Report 21 records boundaries and pending
deployment gates.

Both Lemma 6.7 clauses are complete locally and independently AI-reviewed.
Actual representation gives the terminal alpha alternatives, and the raw
adjacent defect is proved equal to the capped defect in the alpha-one
branch. All five new axiom queries have the standard set. Report 22 records
the n=2/e=1 and omitted-cap checks. Section 6 now has 5/12 numbered items
with complete local proofs.

Global definitions and regularity are present as abstract predicates. The
global reductions still require arithmetic premises whose concrete proofs
have not been supplied. Non-dyadic results, the remaining ADC classifications in
Sections 6--7, global classifications and enumeration remain incomplete.

Semantic status: provisional, with unsigned human review cards and remaining
semantic checks elsewhere in the paper. Trust status: the new concrete endpoints use only the
standard logical axioms; conditional global inputs remain explicit.
Reproducibility status: the published-profile tree passed clean-kit CI in run
33929872783; the later Proposition 4.13, dyadic 4.16, Lemmas 6.4--6.7 and Theorem 6.1 proofs
passed local checks but still require their own clean-kit run. Coverage grade: C. Whole-paper verdict:
`NOT_COMPLETE`.
