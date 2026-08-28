# Beli 2009/2010 coverage and trust-boundary audit

This document maps the results in Constantin N. Beli, *A new approach to
classification of integral quadratic forms over dyadic local fields*
(published online in 2009 and in print in 2010) to the Lean declarations in
this project.

The map distinguishes three kinds of formalization:

- **direct**: Lean derives the result from concrete definitions and earlier
  proved declarations;
- **reduction**: Lean proves the logical or arithmetic step from a checked
  structure containing the geometric local data used in the paper;
- **interface-backed**: a named typeclass isolates one mathematical input in
  the modular source declaration.  This label describes the decomposition of
  the original declaration.  In the completed root import graph, concrete
  proof modules construct these interfaces on the public proof paths; they
  are no longer assumptions of the public main theorem.

## Definitions and the main statement

Definition 1 is `BONG.GoodBONG.alpha` and its finite candidate set
`BONG.GoodBONG.alphaCandidates`.  The four conditions in Theorem 3.1 are
`SameOrders`, `SameAlphas`, `PrefixDefectBounds`, and
`InternalRepresentationConditions`, bundled by `ClassificationConditions`.
All are concrete definitions.

## Numbered results

| Paper result | Lean declaration(s) | Proof boundary |
| --- | --- | --- |
| Lemma 2.1 | `beli2009Lemma21`, `beli2009Lemma21_le_segmentAlpha` | Exact finite-minimum replacement is supplied by `Beli2009AlphaLocalizationLaws`; the inequality is direct. |
| Lemma 2.2 | `alphaLeftEndpoint_monotone`, `alphaRightEndpoint_antitone` | Direct from the already isolated Beli 2006 alpha laws. |
| Corollary 2.3 | `beli2009Corollary23` | Direct order and monotonicity argument. |
| Lemma 2.4 | `beli2009Lemma24_left`, `beli2009Lemma24_right` | Direct finite-minimum compression using Lemma 2.1. |
| Corollary 2.5 | `beli2009Corollary25_i`, `beli2009Corollary25_ii` | Direct from Lemma 2.4. |
| Remark 2.6 | `beli2009Remark26_scaling`, `beli2009Remark26_duality` | Direct scaling and duality rewrites. |
| Lemma 2.7 | `beli2009Lemma27_i` through `beli2009Lemma27_iv` | Parts (i)--(iii) reuse Beli 2006 P2--P4; the parity input in (iv) is `Beli2009AlphaParityLaws`. |
| Corollary 2.8 | `beli2009Corollary28_i` through `beli2009Corollary28_iii` | Direct parity and rational arithmetic. |
| Corollary 2.9 | `beli2009Corollary29_i`, `beli2009Corollary29_ii` | Direct case analysis and arithmetic. |
| Lemma 2.10 | `Lattice.beli2009Lemma210` | Interface-backed by `Beli2009WeightIdealData`, which isolates O'Meara 93A. |
| Lemma 2.11 | `Lattice.OrthogonalDecomposition.beli2009Lemma211` | Interface-backed by `Beli2009OrthogonalIdealLaws`. |
| Lemma 2.12 | `Lattice.StableJordanBoundaryData.beli2009Lemma212` | Interface-backed by `Beli2009FundamentalIdealLaws`, including O'Meara 93:26. |
| Lemma 2.13 | `beli2009Lemma213_i`, `beli2009Lemma213_ii`, `beli2009Lemma213_iii` | Alternating order identities are direct; the norm-generator bridge is `Beli2009JordanBlockLaws`. |
| Lemma 2.14 | `beli2009Lemma214_unary`, `beli2009Lemma214`, `beli2009Lemma214_of_firstBlock_not_unary` | The weight-order formula is `Beli2009JordanWeightOrderLaws`; its final minimum reduction is direct. |
| Lemma 2.15 | `Lattice.UnaryJordanIdealData.beli2009Lemma215` | Interface-backed by `Beli2009UnaryJordanIdealLaws`; endpoint conventions use `Option`. |
| Lemma 2.16 | `beli2009Lemma216_i`, `beli2009Lemma216_ii` | Jordan-to-alpha inputs are `Beli2009JordanAlphaLaws`; the dual and exceptional-branch calculations are direct. |
| Corollary 2.17 | `beli2009Corollary217_i`, `Lattice.beli2009Corollary217_ii` | Direct from Lemmas 2.15--2.16, including endpoint-aware minima. |
| Lemma 3.2 | `beli2009Lemma32` | Direct prefix-product and defect propagation; full determinant square class is `Beli2009AmbientDeterminantLaws`. |
| Lemma 3.3 | `JordanClassificationReduction.beli2009Lemma33` | Reduction proof; local Jordan identifications are `Beli2009JordanReductionLaws`. |
| Lemma 3.4 | `beli2009Lemma34` | Direct from alpha property P6. |
| Lemma 3.5 | `QuadraticSpace.beli2009Lemma35_i` through `beli2009Lemma35_iii` | O'Meara 63:21 is `Beli2009QuadraticRepresentationLaws`; the stated defect consequence is derived. |
| Lemma 3.6 | `Beli2009RepresentationSwitchData.beli2009Lemma36_i`, `beli2009Lemma36_ii` | Direct Hilbert-symbol and representation switch from the preceding representation laws. |
| Lemma 3.7 | `Beli2009PrefixRepresentationBridge.beli2009Lemma37_i`, `beli2009Lemma37_ii` | Prefix identifications and cancellation are `Beli2009PrefixRepresentationBridgeLaws`. |
| Lemma 3.8 | `beli2009Lemma38_i` through `beli2009Lemma38_iii` | Direct rational threshold calculation from checked boundary data. |
| Lemma 3.9 | `Beli2009RepresentationReduction.beli2009Lemma39` | Direct finite incidence argument from checked local sites and O'Meara clauses. |
| Theorem 3.1 | `Beli2009ClassificationReduction.beli2009Theorem31` | Derived from Lemmas 3.3 and 3.9; O'Meara 93:28 is isolated in `Beli2009Omeara9328Laws`. |
| Lemma 4.1 | `beli2009Lemma41` | Direct specialization of Corollary 2.9 to `e = 1`. |
| Theorem 4.2 | `Beli2009ClassificationReduction.beli2009Theorem42` | Direct rewriting of Theorem 3.1; the endpoint defect class is `Beli2009TwoAdicDefectClassLaws`. |
| Lemma 5.1 | `beli2009Lemma51` | Numeric branches and subgroup algebra are direct; the cited Beli 2003 paragraph 3.16 containment is `Beli2009BinaryNormContainmentLaws`. |
| Remark 5.2 | `BONG.GoodBONG.beli2009Remark52` | Direct binary alpha, square-class, and determinant rewrites. |

## Unnumbered Section 5 conclusions

- `beli2009Section5_recursiveAlphaFormula` is the exact recursive formula
  identified with Corollary 2.5(ii).
- `beli2009BinaryTransformAt`, `IsBeli2009BinaryTransformation`, and
  `Beli2009BinaryReachable` define one binary move and a finite succession.
- `beli2009Section5_binaryTransformations_necessary` states that reachability
  implies all four conditions of Theorem 3.1.
- `beli2009Section5_binaryTransformationDichotomy` records the positive
  answer for residue fields with more than two elements and an obstruction
  for a two-element residue field.
- `beli2009Section5_residueTwoParametricCounterexample` records the displayed
  rank-four sequences with `R = 2e - 2d`.
- `beli2009Section5_q2Counterexample` records the explicit
  `(1,1,1,1)` versus `(7,7,7,7)` example.

The original modular declarations package the last assertions in
`Beli2009BinaryTransformationLaws`.  That boundary is now discharged by
`Beli2009FinalRemarksProof.LargeResidueConnectivity.beli2009BinaryTransformationLawsProved`.
The proof supplies the missing path-refined Lemmas 9.2 and 9.3, proves
all-rank connectivity by induction, and combines it with the constructed
residue-two counterexamples.  The unconditional public endpoints are:

- `beli2009Section5_largeResidueConnectivity_proved`;
- `Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved`;
- `Beli2009FinalRemarksProof.beli2009Section5_residueTwoCounterexample_proved`;
- `Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved`;
- `beli2009Section5_binaryTransformationDichotomy_proved`.

## Kernel and source audit

`BongTest.Beli2009Audit` invokes `#print axioms` for every numbered result and
the formalized final remarks.  Its 65 reports use exactly the permitted
kernel dependency set `propext`, `Classical.choice`, and `Quot.sound`.
`BongTest.FinalPublicTheoremAudit` additionally prints the elaborated
unconditional signatures.  No project-specific law/data parameter occurs in
Theorem 3.1 or the completed Section 5 endpoints.  Source scans also reject
`sorry`, `admit`, `sorryAx`, and explicit project `axiom` commands.
