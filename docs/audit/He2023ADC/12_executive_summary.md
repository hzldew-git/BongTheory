# Executive summary

Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), 981--1022, publisher version of record.

Proof assistant: Lean 4.32.1. The current proof checkpoint is
`cf9f83be635d6e459cfb429ad73b4c7a31f1ddf4`.

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

Lemma 6.8(i)--(ii) is now also complete clause by clause and independently
AI-reviewed, using actual tests and full determinant transport. Clause (i)
includes n=2; clause (ii) retains n>=4. All 15 new queries have exactly
the standard three dependencies. Report 23 covers only 2/6 clauses;
the full-Section-6 count remains 5/12 and Theorem 6.2 is not completed.

Report 24 subsequently completes clauses (v),(vi) with independent AI
review and 16 standard-only new dependency sets. Internal normalization
returns actual integral isometry with the original parameter. The printed
V domain explicitly exposes compatible Delta in U; it is not inferred
from normalization alone. This checkpoint supplied 4/6 clauses.

Report 25 adds full (iii) and the n>=4 special case of (iv), independently
replayed with twelve standard-only new sets and a focused gate on 57,667
declarations. Reports 26--30 then construct and independently audit an actual
nonmaximal 2-ADC lattice in `W_2^4(Delta)`. Report 31 records the formal
negation of the n=2 implication printed in Lemma 6.8(iv), with a concrete
`Q_2` nonvacuity check. The source result is `SEMANTIC_MISMATCH` at n=2.

Report 26 independently checks the subsequent 9ec46e6 construction of an
actual integral nonmaximal lattice in W_2^4(Delta) with good-BONG orders
(0,-2e,1,3-2e). Its seven new axiom sets are standard-only and its focused
gate checks 57,679 declarations. No 2-ADC property is asserted, so this
supporting construction neither refutes the paper nor changes coverage.

Report 27 checks the a074fae representation helper for `0 <= d < 2e`:
all four literal conditions yield actual binary lattice representation,
under explicit source and target hypotheses. Twelve new standard-only
sets and a 57,708-declaration focused gate pass. The `d=2e` endpoint,
infinite defect, candidate instantiation and full testing reduction are
outside this checkpoint; no 2-ADC or refutation claim follows from it alone.

Reports 28--29 audit the actual exceptional tests and normalized generic
families. Report 30 exhausts the full binary maximal-testing catalogue,
checks square normalization back to the original integral targets, and proves
the candidate is 2-ADC and nonmaximal. Independent review traversed 80,790
proof dependencies and found no circular use of Lemma 6.8 or Theorem 6.2.
Report 31 freezes the exact published binary proposition and its negation.

Report 32 completes Lemma 6.12 at `cf9f83b`. The actual exceptional lattice
`H perp <1, -Delta * pi^(2 - 2e)>` in `W_1^4(Delta)` is proved integral,
nonmaximal, 2-ADC, and not 3-ADC. The 2-ADC proof exhausts the maximal binary
catalogue, including both endpoints and normalized generic families; the
3-ADC obstruction proves terminal defect zero against comparison alpha at
least one half. A concrete `Q_2` module establishes nonvacuity. Sixteen new
axiom reports have exactly the standard three dependencies, the enforcing
gate checks 57,886 declarations, and the scanner covers 2,705 Lean files.
This raises Section 6 to 6/12 fully matched numbered items. Exact-revision
clean-kit CI and human sign-off remain pending, and Lemmas 6.9--6.11 and
Theorem 6.2 are not supplied.

Global definitions and regularity are present as abstract predicates. The
global reductions still require arithmetic premises whose concrete proofs
have not been supplied. Non-dyadic results, the remaining ADC classifications in
Sections 6--7, global classifications and enumeration remain incomplete.

Semantic status: one confirmed theorem-level mismatch plus provisional and
incomplete material elsewhere; human review cards remain unsigned. Trust status: the new concrete endpoints use only the
standard logical axioms; conditional global inputs remain explicit.
Reproducibility status: the f6f7485/c82668b source tree passed clean-kit CI
in run 33942437722, including Proposition 4.13, dyadic 4.16, Theorem 6.1,
full Lemmas 6.4--6.7 and a real enforcing gate on 57,480 declarations.
The later Lemma 6.8, discrepancy, and Lemma 6.12 additions through cf9f83b
still need their own clean run. The monolithic run 33942437720 hit its six-hour timeout; the
separate paper-kit run passed for all eight papers at f6f7485/c82668b.
Project grade: D because a substantive mismatch occurs in a core classification
lemma. Whole-paper verdict:
`NOT_COMPLETE`.
