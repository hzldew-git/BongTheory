# Public theorem index

The table lists stable public entry points. Internal proof modules may expose
additional paper lemmas; the audit packages give the fuller maps.

| Source result | Lean endpoint | Source file | Status |
| --- | --- | --- | --- |
| Beli 2003, Theorem 1 | `Bong.BONG.beliTheoremOne_proved` | `Bong/Bong/BeliTheoremOneProof.lean` | `PROVISIONAL_MATCH` |
| Beli 2003, Theorem 1 as a set equality | `Bong.BONG.beliTheoremOne_set_proved` | `Bong/Bong/BeliTheoremOneProof.lean` | `PROVISIONAL_MATCH` |
| Beli 2003, Theorem 2 | `Bong.Lattice.beliTheoremTwo_proved` | `Bong/Bong/BeliTheoremTwoProof.lean` | `PROVISIONAL_MATCH` |
| Beli 2003, Theorem 3 | `Bong.BONG.beliTheoremThree_proved` | `Bong/Bong/BeliTheoremThreeUnconditional.lean` | `PROVISIONAL_MATCH` |
| Beli 2006, Theorem 3.2 | `Bong.beli2006Theorem32_proved` | `Bong/Bong/Beli2006MainTheorems.lean` | `PROVISIONAL_MATCH` |
| Beli 2006, Theorem 4.5 | `Bong.beli2006Theorem45_proved` | `Bong/Bong/Beli2006MainTheorems.lean` | `PROVISIONAL_MATCH` |
| Beli 2009/2010, Theorem 3.1 | `Bong.BONG.GoodBONG.beli2009Theorem31_concrete` | `Bong/Bong/Beli2009ClassificationProof.lean` | `PROVISIONAL_MATCH` |
| Beli 2009/2010, Section 5 positive conclusion | `Bong.beli2009Section5_largeResidueConnectivity_proved` | `Bong/Bong/Beli2009BinaryConnectivityComplete.lean` | `PROVISIONAL_MATCH` |
| Beli 2009/2010, Section 5 dichotomy | `Bong.beli2009Section5_binaryTransformationDichotomy_proved` | `Bong/Bong/Beli2009BinaryConnectivityComplete.lean` | `PROVISIONAL_MATCH` |
| Beli 2019 v2, Theorem 2.1 | `Bong.beli2019Theorem21` | `Bong/Bong/Beli2019MainTheorem.lean` | `PROVISIONAL_MATCH` |
| Beli 2019 v2, Theorem 2.1 with `(iii')` | `Bong.beli2019Theorem21_prime` | `Bong/Bong/Beli2019MainTheorem.lean` | `PROVISIONAL_MATCH` |
| Beli 2020, Theorem 2.1 | `Bong.BONG.GoodBONG.isUniversal_iff_universalTheorem21Conditions` | `Bong/Bong/BeliUniversalTheorem21.lean` | `PROVISIONAL_MATCH` |
| Beli 2020, Theorem 3.1, direct derivation | `Bong.Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31DirectConditions` | `Bong/Bong/BeliUniversalTheorem31Proof.lean` | `PROVISIONAL_MATCH` |
| Beli 2020, Theorem 3.1, literal text at first scale zero | `Bong.Lattice.JordanDecomposition.isUniversal_iff_universalTheorem31Conditions_of_firstScaleOrder_eq_zero` | `Bong/Bong/BeliUniversalTheorem31Proof.lean` | `PROVISIONAL_MATCH` |
| Beli 2020, Lemma 4.9 | `Bong.BONG.GoodBONG.beliUniversalLemma49` | `Bong/Bong/BeliUniversalLemma49.lean` | `PROVISIONAL_MATCH` |
| Beli 2020, Corollary 4.10 | `Bong.BONG.GoodBONG.beliUniversalCorollary410` | `Bong/Bong/BeliUniversalCorollary410.lean` | `PROVISIONAL_MATCH` |
| He--Hu, Theorem 1.1 | `Bong.BONG.GoodBONG.heHu2022Theorem11` | `Bong/Bong/HeHu2022Theorem11.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He--Hu, Theorem 1.2 literal finite testing family | `Bong.Lattice.QuadraticLatticeModel.heHu2022Theorem12PublishedEvenLiteral`, `Bong.Lattice.QuadraticLatticeModel.heHu2022Theorem12PublishedOddLiteral` | `Bong/Bong/HeHu2022PublishedTestingSet.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Definition 1.1(ii), local dyadic specialization | `Bong.Lattice.IsNADC` | `Bong/Lattice/NADC.lean` | `DEFINITION_PENDING_SEMANTIC_SIGNOFF` |
| He ADC, Lemma 2.1, local dyadic specialization | `Bong.Lattice.heADCLemma21LocalDyadic` | `Bong/Papers/He2023ADC.lean` | `PROVED_SPECIALIZATION_ONLY` |
| He ADC, Lemma 6.12 | `Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC`, `heADCExceptionalQuaternaryCandidate_not_is3ADC`, `heADCExceptionalQuaternaryCandidate_not_isOMaximal` | `Bong/Bong/He2023ADCExceptionalQuaternaryNonThree.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Lemma 7.15 | `Bong.BONG.GoodBONG.heADC2025Lemma715` | `Bong/Bong/He2023ADCLemma715.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Definition 7.16 and Remark 7.17 | `Bong.BONG.GoodBONG.HeADC2025Definition716`, `heADC2025Remark717_unique`, `heADC2025Remark717_exhaustion` | `Bong/Bong/He2023ADCDefinition716.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Lemma 7.18 | `Bong.BONG.GoodBONG.heADC2025Lemma718` | `Bong/Bong/He2023ADCLemma718.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Lemma 7.19 | `Bong.BONG.GoodBONG.heADC2025Lemma719FirstNamedPublished`, `heADC2025Lemma719SecondNamedPublished` | `Bong/Bong/He2023ADCLemma719Models.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Lemma 7.20 | `Bong.BONG.GoodBONG.heADC2025Lemma720_defined_iff`, `heADC2025Lemma720iii`, `heADC2025Lemma720iiiFirst_isometricNamed`, `heADC2025Lemma720iiiSecond_isometricNamed` | `Bong/Bong/He2023ADCLemma720.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Theorem 7.2 | `Bong.BONG.GoodBONG.heADC2025Theorem72Published`, `heADC2025Theorem72Published_overlap` | `Bong/Bong/He2023ADCTheorem72Published.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Remark 7.3 | `Bong.BONG.GoodBONG.heADC2025Remark73_firstPublished`, `heADC2025Remark73_secondPublished`, `heADC2025Remark73_thirdPublishedRepresentative` | `Bong/Bong/He2023ADCRemark73.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, O'Meara 63:9 unit square-class count | `Bong.Dyadic.card_valuationUnitClass`, `Bong.HeADC2025Corollary721CountingLaw.card_unit_representatives` | `Bong/Dyadic/UnitSquareClassCount.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Corollary 7.21 | `Bong.HeADC2025Corollary721Index.isExactNADCIsometryCatalogue`, `model_isOMaximal_iff`, `heADC2025Corollary721` | `Bong/Bong/He2023ADCCorollary721.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |
| He ADC, Theorem 5.1 and Lemmas 5.2--5.4 | `Bong.HeADC2025NonDyadicSystem.SectionFiveLaws.heADC2025Theorem51`, `heADC2025Lemma52`, `heADC2025Lemma53i`, `heADC2025Lemma53ii`, `heADC2025Lemma53iii`, `heADC2025Lemma53iv`, `heADC2025Lemma54` | `Bong/Bong/He2023ADCSectionFive.lean` | `CONDITIONAL_FORMALIZATION` |
| He ADC, Theorems 1.5, 1.7 and Section 8 | `Bong.HeADC2025GlobalData.LocalMaximalityLaws.local_theorem15`, `DistinguishingSublatticeLaws.distinguishing_rank_sublattice`, `ScalingStabilityLaws.locallyTwoADC_scaleTwo_stable`, `ScalingRegularityLaws.nRegular_scaleTwo`, `GlobalMaximalityLaws.globalMaximal_iff_localMaximal`, `GenusTransportLaws.rank_eq_of_inGenus`, `SectionEightLaws.heADC2025Theorem15ii`, `heADC2025Theorem17`, `heADC2025Theorem82`, `heADC2025Corollary85` | `Bong/Lattice/He2023ADCSectionEight.lean` | `CONDITIONAL_FORMALIZATION` |
| He ADC, Corollary 1.8 | `Bong.HeADC2025Corollary18EnumerationData.heADC2025Corollary18` | `Bong/Lattice/He2023ADCEnumerativeMain.lean` | `FORMALIZED_RELATIVE_TO_EXTERNAL_ENUMERATIONS` |
| He ADC, Theorem 1.11 | `Bong.HeADC2025Theorem111Laws.heADC2025Theorem111` | `Bong/Lattice/He2023ADCEnumerativeMain.lean` | `CONDITIONAL_FORMALIZATION` |
| He ADC, Theorem 1.9(ii), Theorem 1.10 and Theorem 6.2, binary boundary | `Bong.HeADC2025QuaternaryCatalogue.not_heADC2025Theorem19iiBinaryStatement`, `not_heADC2025Theorem110BinaryCountStatement`, `heADC2025Theorems19iiAnd110BinaryCorrected` | `Bong/Bong/He2023ADCQuaternaryCatalogue.lean` | `PUBLISHED_STATEMENTS_REFUTED_AND_CORRECTED` |

Except for rows explicitly marked `CONDITIONAL_FORMALIZATION`, promoted concrete endpoints have
zero project-specific law/data parameters in their public signatures. The
conditional rows expose their exact undischarged inputs; the audit packages
record the separate independent semantic-sign-off status.

For Beli 2020, `PROVISIONAL_MATCH` also records the frozen source
discrepancy in Theorem 3.1(3.2.1--2): direct substitution gives coefficient
`2r_1`, whereas the paper prints `r_1`.  No inferred correction is presented
as author-confirmed text.
