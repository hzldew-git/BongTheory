# Executive summary

Paper: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), 981--1022, publisher version of record.

Proof assistant: Lean 4.32.1. The current proof checkpoint is
`6c528031d27cc050a1f10c2ec953500f9b4c3c2c`.

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
This raised Section 6 to 6/12 fully matched numbered items at that checkpoint.

Report 33 adds complete Lemmas 6.9--6.11 at `382ef7a`. Lemma 6.9 derives the
published terminal-order dichotomy from actual represented kappa lattices;
Lemma 6.10 verifies the four Beli classification conditions and proves actual
exceptional-lattice isometry; Lemma 6.11 derives every binary test from the
2-ADC hypothesis and exports the printed maximal-or-exceptional disjunction.
The three modules, canonical entry, and full audit compile directly. Ten new
axiom reports are standard-only, the enforcing gate checks 57,918
declarations, and the scanner checks 2,708 tracked Lean files. Section 6 now
had 9/12 fully matched numbered items at that checkpoint. Exact-revision
package CI and human sign-off remained pending there; Theorem 6.2 and Remark
6.3 were not yet supplied, and the separate published Lemma 6.8(iv) mismatch
was unchanged.

Report 34 adds the complete published Remark 6.3 and a boundary-complete
audit of Theorem 6.2 at `70580bb`. The exact `n=2` biconditional of Theorem
6.2 is formally refuted by the actual second-column 2-ADC lattice; the full
`n>=4` restriction is proved for arbitrary lattices. Eight new axiom reports
are standard-only, the enforcing gate checks 57,933 declarations, and the
scanner checks 2,711 tracked Lean files. Section 6 is now completely triaged:
10/12 numbered items match, while Lemma 6.8 and Theorem 6.2 each have a
documented false `n=2` boundary. Downstream theorems still require fresh audit
instead of inheriting the unqualified published Theorem 6.2.

Global definitions and regularity are present as abstract predicates. The
global reductions still require arithmetic premises whose concrete proofs
have not been supplied. Non-dyadic results, most Section 7 ADC
classifications, global classifications and enumeration remain incomplete.

Report 35 adds the complete Theorem 7.1 at `c3e6092`. The theorem statement
is correct, but the publisher's proof is incomplete because it inherits the
false binary classification and omits the second `W_2^4(Delta)` boundary
class. The formal proof first establishes the corrected three-way binary
classification and proves that the omitted class, like the published
exception, is not 3-ADC. Seven new dependency reports are standard-only, the
focused gate checks 58,019 declarations, and the scanner checks 2,715 tracked
Lean sources. At that checkpoint, the other 20 Section 7 items were not
covered by this result.

Report 36 adds the complete Theorem 7.4 and Lemmas 7.5--7.10 and 7.12 at
`2417a4f`. The full Lemma 7.5 four-condition equivalence is proved in both
directions, including the rank-five large-gap branch and the endpoint
`R_(n+1)=2-2e`. Report 37 completes Lemma 7.11 at `832d10c`: its unit and
unit-times-uniformizer rows jointly cover every normalized nonzero square
class, while the latter row remains sufficient for the Lemma 7.5 necessity
argument. The formalization also detects that Lemma 7.13's printed
per-target conclusion is stronger than its proof, which establishes only that
the two targets cannot both be represented. The proof-supported disjunction
is formalized and suffices downstream. The complete Lemma 7.11 checkpoint has
standard-only new dependency reports, a 59,204-declaration focused gate, and
a 2,727-source scanner. Report 38 adds both clauses of Lemma 7.14 at
`6c52803`: both ambient columns and both parameter parities are retained,
with a 59,218-declaration gate and 2,728-source scanner. Report 39 adds the
complete Lemma 7.15 isometry classification at `06d2507`: the maximal branch
and all four Beli conditions in the nonmaximal branch are proved internally,
with a 59,348-declaration gate and 2,729-source scanner. Reports 40--42 add
Definition 7.16, Remark 7.17, and Lemmas 7.18--7.19 at `7b21fe0`. Lemma 7.19
is proved on both literal named `N` products after explicit maximal-lattice
isometries. The focused gate checks 59,555 declarations and the scanner checks
2,735 sources. Report 43 completes Lemma 7.20 at `b86a9d4`: its maximal
endpoints, all four Hilbert-selected ambient combinations, both named
products, every lower-row existence statement, and the unique undefined
triple are proved. The focused gate checks 59,643 declarations and the
scanner checks 2,738 sources. Section 7 had 17/21 fully formalized numbered
items at that checkpoint. Report 44 adds the full Theorem 7.2 at `07cd548`:
both the representative-independent and literal finite maximal-or-product
biconditionals, integral square normalization, and the published
maximal-overlap assertion are proved. Six selected reports are standard-only,
the focused gate checks 59,692 declarations, and the scanner checks 2,740
sources. Section 7 had 18/21 fully formalized numbered items at that
checkpoint. Report 45 adds all three literal formulas of Remark 7.3 at
`287b202`, including the exact negative powers, sharp scale, half-scaled
`A` normalization, ordered ternary tail, and finite representative domain.
Eight selected reports are standard-only, the focused gate checks 59,743
declarations, and the scanner checks 2,741 sources. Section 7 now has 19/21
fully formalized numbered items, one quantifier-mismatched item, and one
pending item.

Semantic status: two confirmed theorem-level boundary mismatches plus provisional and
incomplete material elsewhere; human review cards remain unsigned. Trust status: the new concrete endpoints use only the
standard logical axioms; conditional global inputs remain explicit.
Reproducibility status: the f6f7485/c82668b source tree passed clean-kit CI
in run 33942437722, including Proposition 4.13, dyadic 4.16, Theorem 6.1,
full Lemmas 6.4--6.7 and a real enforcing gate on 57,480 declarations.
The later additions through 287b202
still need their own clean run. The monolithic run 33942437720 hit its six-hour timeout; the
separate paper-kit run passed for all eight papers at f6f7485/c82668b.
Project grade: D because a substantive mismatch occurs in a core classification
lemma. Whole-paper verdict:
`NOT_COMPLETE`.
