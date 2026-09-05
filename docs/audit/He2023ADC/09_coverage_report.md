# Coverage report

Coverage status: `IN_PROGRESS_WITH_PUBLISHED_BOUNDARY_MISMATCH`.

- Publisher inventory: 78/78 directly numbered items identified.
- Local dyadic definition, maximal testing, maximal-implies-ADC, equal-rank
  equivalence and stable-rank ADC/universality equivalence are proved.
- Section 3 has direct endpoints for all six numbered items.
- Section 4 has the space and maximal-table endpoints, representation
  reductions, rank-at-least-two minimal testing sets, the coordinate component
  of Remark 4.10, ten concrete-model profile criteria, and all thirteen
  published-family branches covering Lemmas 4.11--4.12. Proposition 4.13 now
  has a complete endpoint for arbitrary odd-rank maximal lattices, including
  all alpha and bracketed-defect conclusions and the ternary boundary.
- Both clauses of Proposition 4.16 have completed dyadic proofs: the
  hyperbolic representation exception and its explicit integral model.
  The whole published proposition is `SPECIAL_CASE_ONLY`, since its
  non-dyadic part is not supplied by the current field context.
- Section 6 has local kernel-complete proofs of all four clauses of
  Lemma 6.4, on the actual named tests and including their short-rank
  boundaries. This is one numbered lemma, not four paper results, and it
  does not complete either of the even ADC classification theorems.
- Both clauses of Lemma 6.5 are also locally kernel-complete and independently
  AI-reviewed. They prove the two exact pointwise obstructions, not merely
  non-representation.
- Theorem 6.1 is now locally complete and independently AI-reviewed: every
  full lattice of rank n+1, for even n >= 2, is n-ADC iff it is maximal.
  This completes 1/2 of Section 6's numbered classification theorems;
  Theorem 6.2 remains pending.
  The needed actual even corank-one case of Lemma 4.6(i) is also proved;
  it does not complete all of Lemma 4.6.
- Both Lemma 6.6 clauses are now locally complete and independently
  AI-reviewed. The exact central trigger and prefix non-representation
  are proved on arbitrary good BONGs of both actual targets.
- Both Lemma 6.7 clauses are locally complete and independently AI-reviewed:
  actual representation gives the exact alpha alternatives and raw/capped
  defect equalities. At that checkpoint Section 6 totaled 5/12 numbered items,
  not a whole-paper
  completion percentage; Theorem 6.2 remains pending.
- Lemma 6.8(i)--(ii) now passes local and independent checks, with actual
  lattice isometry and exact n=2/n>=4 boundaries. This is only 2/6 clauses
  of that lemma; the count of fully complete Section 6 items remains 5/12.
  Its own clean-kit CI remains pending. The earlier f6f7485/c82668b kit
  passed clean CI and enforced dependency checks through full Lemma 6.7.
- Report 24 adds locally proved and independently AI-reviewed clauses
  (v),(vi) at b728bce, including n=2 and explicit representative alignment
  for the printed V domain. That checkpoint supplied 4/6 clauses, still partial;
  Section 6 remains 5/12 fully completed numbered items. These new proofs
  still need their own clean kit and CI, and do not imply human approval.
- Report 25 adds full (iii) and the n>=4 part of (iv) at 074f2cd. Reports
  26--30 construct the missing boundary candidate and independently prove that
  it is an actual nonmaximal 2-ADC lattice in `W_2^4(Delta)`. Report 31 records
  the formal negation of the printed n=2 implication and a concrete `Q_2`
  witness. Lemma 6.8(iv) is therefore a `STATEMENT_MISMATCH` at n=2, rather
  than a remaining formalization gap. Section 6 still has 5/12 fully matched
  numbered items; mismatch evidence does not count as a formalized proof of
  the paper's false clause.
- Lemma 6.12 is now locally complete at `cf9f83b`. The actual exceptional
  lattice in `W_1^4(Delta)` is proved 2-ADC, not 3-ADC, and nonmaximal. The
  proof exhausts the maximal binary catalogue and has a concrete `Q_2`
  nonvacuity check. Report 32 records the source-first audit, standard-only
  dependency sets, and the pending exact-revision clean-kit and human gates.
  At that checkpoint Section 6 reached 6/12 fully matched numbered items.
- Lemmas 6.9--6.11 are now locally kernel-complete at `382ef7a`. Lemma 6.9
  proves the exact terminal dichotomy from the two actual kappa tests;
  Lemma 6.10 checks all four Beli classification conditions and obtains
  actual exceptional-lattice isometry; Lemma 6.11 derives all four binary
  tests from 2-ADC-ness and proves the maximal-or-exceptional classification.
  Report 33 records source correspondence and trust checks. This raises
  Section 6 to 9/12 fully matched numbered items. Exact-revision package CI
  and human sign-off remain separate gates. Theorem 6.2 and Remark 6.3 remain
  pending, and the Lemma 6.8(iv) `n=2` mismatch remains unchanged.
- Global predicates and regularity are defined in an abstract system, and
  the logical reductions are proved with explicit arithmetic premises.

The remaining scope includes concrete localization and Lemma 2.2, unrestricted
local-field results, unary testing-set minimality, remaining Section 4 clauses,
Section 5, Theorem 6.2 and Remark 6.3, Section 7 ADC classification,
Section 8 global proofs, and the enumerative
main theorems. The `W/N` correspondence gap for Lemmas 4.11--4.12 is closed
in code; this does not fill the other boundary cases or provide human approval.

No completed-paper percentage is inferred from the number of declarations:
one numbered result can have many formal branches, and some current branches
only cover the dyadic specialization. The whole-paper verdict remains
`NOT_COMPLETE` and the overall coverage grade is D.
