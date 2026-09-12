# Formal declaration inventory

- `Bong.Lattice.IsClassicIntegral`: scale-integral lattice.
- `Bong.Lattice.IsClassicNUniversal`: representation of all classic integral
  rank-`n` lattices.
- `Bong.Lattice.IsClassicMaximal`: maximality among classic integral lattices.
- `exists_classicMaximal_superlattice`: proved extension theorem.
- `heClassicMaximalTestingReduction`: proved abstract testing equivalence.
- `HeClassicZeroOrOne`: the source alternative `R_i in {0,1}`.
- `heClassicAdjacentDefectAt`: adjacent binary defect with a zero-based index.
- `heClassicSignedPrefixDefect`: the signed prefix defect in Theorem 1.1.
- `HeClassicEvenConditions`: the complete even branch, Theorem 1.1(ii).
- `HeClassicOddConditions`: the complete odd branch, Theorem 1.1(iii).
- `HeClassicTheorem11Conditions`: the complete right-hand side of Theorem 1.1.
- `HeClassicTheorem11Statement`: the author-corrected-v5 theorem proposition, recorded
  as a definition and not asserted as a theorem.

The proposition-valued definition remains separate from its proof:

- `Bong.BONG.GoodBONG.he2022ClassicTheorem11`: proves the complete equivalence
  for n >= 2 and arbitrary source rank.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem41` and
  `he2022ClassicTheorem51`: even and odd local criteria used by that proof.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15_unary`: proves the fixed-field
  implication at n = 1 through the scalar-universal alpha criterion.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15`: proves the fixed-field
  implication for n >= 2 through the classic criterion.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks`: combines both branches
  over the complete published local range n >= 1. It has no global
  number-field conclusion.
- `Bong.BONG.GoodBONG.he2022ClassicCorollary63_even`: even branch only.
- `HeClassic2024LocalExtensionData.Lemma81Laws.he2022ClassicLemma81i`--`iii`:
  the three conditional finite-extension clauses of Lemma 8.1.
- `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicProposition82_positive`
  and `he2022ClassicProposition82`: the two statements of Proposition 8.2 over
  an explicit globalization/localization package.  The first is now derived
  by `HeClassic2024GlobalData.Proposition82Laws.he2022ClassicProposition82_positive`
  from four lower-level arithmetic laws; Report 27.
- `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem15_discriminantOdd`:
  the final global deduction of Theorem 1.5.
- `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem17_even` and
  `he2022ClassicTheorem19`, together with
  `HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even` and
  `he2022ClassicTheorem18_even`: conditional even-scope Section 8 and
  global-main-theorem endpoints.  Their arithmetic package is uninstantiated;
  Reports 23, 28, and 33.  No unrestricted odd endpoint remains.
- `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem17_of_localAdjacentDefectsLarge`:
  the parity-independent final contradiction in Theorem 1.7, with the omitted
  local coefficient/defect calculation exposed as a theorem premise rather
  than hidden in a source-facing endpoint; Report 33.
- `HeClassic2024GlobalData.SumOfSquaresLocalGlobalLaws.sumOfSquares_local_to_global`:
  derives the local-to-global step of Theorem 1.9 from localization and strong
  approximation; the compatibility endpoint in `SectionEightLaws` and the
  full biconditional use this proof; Report 29.
- `HeClassic2024GlobalData.DiscriminantRamificationLaws` and
  `exists_ramifiedDyadic_of_not_discriminantOdd`: the one-way discriminant
  criterion and its derived contrapositive witness used by Theorems 1.5, 1.7,
  and 1.9; Report 30.
- `HeClassic2024NumberField.discriminantOdd_iff_forall_ramificationIdx_eq_one`:
  the concrete number-field equivalence between odd discriminant and
  ramification index one at every dyadic prime ideal; its two directed
  consequences, ramified-prime witness, and positivity theorem are proved in
  the same module; Report 32.
- `HeClassic2024GlobalData.NumberFieldDiscriminantBridge` and its construction
  theorems: transport the concrete number-field result to the abstract place
  layer and fill both discriminant directions and ramification-index
  positivity; Report 32.
- `HeClassic2024GlobalData.HeightOneSpectrumIdentification` and
  `numberFieldDiscriminantBridge`: reduce the abstract-place bridge to an
  equivalence with the standard height-one spectrum and three compatibility
  statements; primality and dyadic-prime coverage are proved; Report 34.
- `HeClassic2024NumberFieldGlobalData`, `toGlobalData`, and
  `sectionEightLaws`: define the three arithmetic fields directly from the
  height-one spectrum and derive their compatibility plus the Section 8
  discriminant fields from a place equivalence; Report 36.
- `HeClassic2024NumberFieldLocalExtension.adicOrder_liesOver`,
  `relativeRamificationIndex_pos`, and `absoluteRamificationIndex_tower`:
  actual finite-prime arithmetic for nonzero underlying number-field
  coefficients; Report 38.
- `RemainingCoefficientInputs.toLocalExtensionData` and `lemma81Laws`:
  populate the order, positivity, and ramification-tower parts of Lemma 8.1
  while retaining only defect scaling and good-BONG transfer as inputs;
  Report 38. This is not yet the arbitrary-completion-element statement.
- `HeClassic2024NumberFieldLocalExtension.completionMap`,
  `completionMap_coe`, and `continuous_completionMap`: construct the actual
  map `K_p -> L_P`, prove its compatibility with the dense number-field
  subfield, and prove continuity; the scoped `CompletionLiesOver` instances
  give the completed algebra, scalar tower, continuous scalar multiplication,
  and finite-dimensional extension; Report 39. This does not yet prove
  valuation scaling for arbitrary elements of `K_p`.
- `HeClassic2024GlobalData.SumOfSquaresLocalUniversalityLaws` and
  `sumOfSquares_localUniversal_of_oddDiscriminant`: the non-dyadic, dyadic
  unary, and dyadic higher-rank inputs and their derived all-finite-place
  conclusion in Theorem 1.9; Report 31.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma74_even`: even-rank
  testing equivalence.
- `Bong.Lattice.isClassicMaximal_of_volumeOrder_le_one`: a generic proved
  maximality criterion for classic integral lattices of volume order at most
  one.
- `HeClassicPublishedEvenTestingIndex.model_isClassicMaximal` and
  `HeClassicPublishedOddTestingIndex.model_isClassicMaximal`: every literal
  published table row is classic-maximal in its own ambient space.
- `Bong.BONG.GoodBONG.he2022ClassicLemma77_boundary_conditions` and the two
  bundled representation endpoints: the published boundary and stable-range
  proof for `P2(Delta)` against both `C` columns.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma710_publishedEven_deletionWitness`:
  one classic integral deletion witness for every literal even table index,
  including all exceptional and `C` rows.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicTheorem13_even_literalMinimal`:
  the combined even testing and literal-minimality endpoint.
- `Bong.BONG.GoodBONG.he2022ClassicLemma71v5_ramificationOne_represents`,
  `he2022ClassicLemma71v5_lowDefect_represents`, and
  `he2022ClassicLemma71v5_C1OneModel_represents_evenHOneModel`: the three
  integral-representation branches in author-corrected v5 Lemma 7.1.
- `Bong.Lattice.QuadraticLatticeModel.all_publishedOdd_implies_all_publishedEven_v5`:
  the v5 bridge from the complete odd table to the complete even table one
  rank lower.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma74_odd_v5`: the
  unconditional odd-rank testing equivalence.
- `Bong.he2022ClassicTheorem13_odd_literalMinimal_v5`: the combined odd
  testing and literal-minimality endpoint.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma71ii_literal_disjunction_fails`:
  a retained regression refuting the obsolete broader publisher disjunction,
  not the corrected v5 statement.
- `Bong.BONG.GoodBONG.he2022ClassicLemma45_j2_of_terminalUpper` and
  `he2022ClassicLemma45_j2_of_j2Prime_of_ramification_gt_one`: checked
  lower-even reductions which do not use the false Lemma 7.1(ii).
- `Bong.Lattice.QuadraticLatticeModel.all_publishedOdd_implies_classicUniversal_of_lowerTerminalUpper`
  and `all_publishedOdd_implies_classicUniversal_of_lowerJ2Prime`: the odd
  testing implication conditional on the exact remaining terminal bound,
  respectively on lower `J2'_E` when `e > 1`.

`BongTest/He2022ClassicAudit.lean` exposes additional branch endpoints and
their transitive axiom reports. Both all-indices testing statements and both
literal-minimality conclusions are proved. Report 20 records the historical
terminal reduction; Report 22 records its v5 completion and Report 23 records
the conditional global layer.  The focused
`BongTest/He2022ClassicProposition82Audit.lean` checks the Report 27
globalization derivation and its compatibility endpoints.
`BongTest/He2022ClassicEvenExtensionAudit.lean` checks the Report 28 parity
restriction and the remaining even deduction.
`BongTest/He2022ClassicStrongApproximationAudit.lean` checks the Report 29
local-to-global derivation and Theorem 1.9.
`BongTest/He2022ClassicDiscriminantRamificationAudit.lean` checks the Reports
30 and 32 abstract criterion, concrete number-field theorem, bridge
constructions, and downstream consumers.
`BongTest/He2022ClassicNumberFieldGlobalDataAudit.lean` checks the canonical
arithmetic adapter and the derived Section 8 package from Report 36.
`BongTest/He2022ClassicNumberFieldLocalExtensionAudit.lean` checks the
finite-prime order and ramification theorems, their partial Lemma 8.1 adapter,
the finite-completion map, and finite-dimensionality from Reports 38--39.
`BongTest/He2022ClassicLocalUniversalityAudit.lean` checks the Report 31
finite-place case split and the full conditional Theorem 1.9 endpoint.
