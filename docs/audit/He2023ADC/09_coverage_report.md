# Coverage report

Coverage status:
`IN_PROGRESS_WITH_PUBLISHED_BOUNDARY_MISMATCHES_AND_EXTERNAL_CLASSIFICATION_INPUTS`.

The publisher inventory identifies all 78 directly numbered items. Counts
below refer to paper results, not Lean declarations; a result with several
formal branches is still one paper item, and a conditional proof is not
counted as a concrete arithmetic implementation.

## Current proved and audited scope

- The local dyadic ADC definition, maximal testing, maximal-implies-ADC,
  equal-rank equivalence, and stable-rank ADC/universality equivalence are
  proved. The global predicates and Theorems 1.3--1.4 are present as logical
  reductions with explicit arithmetic premises.
- Lemma 2.2 is fully formalized for every number field and finite-place
  completion. The proof includes density, open nonzero square classes, the
  all-dimensional algebraic induction, and the literal descended-subspace
  conclusion; reports 55--56. Human semantic review remains open.
- Section 3 has direct endpoints for all six numbered items.
- Section 4 contains the dyadic space and maximal tables, representation
  reductions, literal minimal testing sets in every rank `n>=1`, all thirteen
  published `W/N` branches of Lemmas 4.11--4.12, full Proposition 4.13, and
  the dyadic parts of Lemma 4.14 and Propositions 4.15--4.16. The unary table,
  exhaustion, exact excluding ternary witness, and count are closed in report
  50. Non-dyadic cases remain open.
- Every numbered Section 5 deduction, including all four clauses of Lemma
  5.3 and Theorem 5.1, is proved from the explicit non-dyadic
  `SectionFiveLaws` package. A concrete lattice/Jordan instance of that
  package remains open; report 47.
- Section 6 is completely triaged. Ten numbered items provisionally match.
  Lemma 6.8(iv) and Theorem 6.2 are formally refuted at `n=2`; all valid
  remaining clauses and the full `n>=4` Theorem 6.2 are proved. The corrected
  binary result classifies rank-four 2-ADC lattices as maximal or one of two
  realized nonmaximal classes; reports 23--35 and 48.
- Twenty of the 21 Section 7 items are fully formalized. Corollary 7.21 has
  a complete irredundant integral-isometry catalogue and unconditional
  counts both in terms of `|U|` and in the printed residue-norm form, using
  the repository proof of O'Meara 63:9. Lemma 7.13 has a
  source quantifier mismatch: the proof-supported simultaneous-failure
  disjunction is formalized and suffices downstream; reports 35--46.
- Every numbered Section 8 deduction, plus Theorems 1.5 and 1.7, is proved
  from `SectionEightLaws` and the existing Theorem 1.3 package. Concrete
  localization, class-number, Meyer--Xu--O'Meara, genus-transport, and
  scaling-stability instances remain open; report 47.
- The binary cases of Theorem 1.9(ii) and Theorem 1.10 are formally refuted
  and corrected. The exact catalogue has `4|U|+2` classes and unconditionally
  `8(N p)^e+2`, rather than the
  printed `+1`; report 48.
- Every dyadic branch of Theorem 1.10 is now proved through an exact finite
  integral-isometry catalogue. This includes both parities in equal rank and
  corank one, stable even corank two, Corollary 7.21's odd corank-two family,
  and the corrected binary corank-two family; report 51.
- The non-dyadic finite-catalogue deduction of Theorem 1.10 is proved for
  equal rank and both coranks. Its exact seven-/eight-row counts specialize
  the printed formula at `e=0`; concrete catalogue laws remain open; report
  52.
- Corollary 1.8's total 586 and every logical conclusion of Theorem 1.11 are
  proved from explicit external-enumeration laws. The Table 2 source-row
  selection, injectivity, and exact 21 count are closed; concrete Hanke--
  Kirschmer--Oh data and prime-by-prime local checks remain open; report 53.

## Published-source discrepancies

One omitted second-discriminant class causes four affected printed claims:

1. Lemma 6.8(iv), binary endpoint;
2. Theorem 6.2, binary biconditional;
3. Theorem 1.9(ii), binary classification; and
4. Theorem 1.10, binary count.

These are separately frozen and refuted; the source is never silently
rewritten. In addition, Lemma 7.13 has a stronger printed quantifier than its
published proof establishes, and the printed proof of Theorem 7.1 omits the
second binary boundary class. Theorem 7.1 itself is proved by a repaired
route that exhausts both exceptions.

## Remaining scope

The main unresolved mathematical work is:

- the non-dyadic Section 4 cases;
- concrete non-dyadic instances of `SectionFiveLaws` and `CatalogueLaws`,
  required to discharge the conditional Theorem 1.10 endpoint;
- concrete number-field instances of `SectionEightLaws` and the earlier
  global reduction packages;
- any publisher-corrected replacement for the four binary statements and a
  resolution of the printed-strength Lemma 7.13 claim;
- concrete Hanke--Kirschmer--Oh catalogue imports, matrix models, and local
  computations underlying Corollary 1.8 and Theorem 1.11;
- GitHub-hosted exact-revision CI, independent human semantic sign-off,
  merge, and release promotion. The current local clean Review Kit through
  Report 57 passes at `7d7a4d5`; see Report 58.

The whole-paper verdict remains `NOT_COMPLETE`, with grade D because the
published version contains substantive classification mismatches. That grade
does not assert that the unformalized remainder is false.
