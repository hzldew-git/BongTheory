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
| He--Hu, Theorem 1.1 | `Bong.BONG.GoodBONG.HeHuTheorem11Statement` | `Bong/Bong/HeHu2022Conditions.lean` | `STATEMENT_ONLY_UNPROVED` |
| He--Hu, Theorem 1.2 maximal-testing core | `Bong.Lattice.heHuMaximalTestingReduction` | `Bong/Papers/HeHu2022.lean` | `PROVED_ABSTRACT_CORE_ONLY` |
| He classic, Theorem 1.1 | `Bong.BONG.GoodBONG.HeClassicTheorem11Statement` | `Bong/Bong/He2022ClassicConditions.lean` | `STATEMENT_ONLY_UNPROVED` |
| He classic, abstract maximal-testing reduction | `Bong.Lattice.heClassicMaximalTestingReduction` | `Bong/Papers/He2022Classic.lean` | `PROVED_FOUNDATION_ONLY` |
| He ADC, Definition 1.1(ii), local dyadic specialization | `Bong.Lattice.IsNADC` | `Bong/Lattice/NADC.lean` | `DEFINITION_PENDING_SEMANTIC_SIGNOFF` |
| He ADC, Lemma 2.1, local dyadic specialization | `Bong.Lattice.heADCLemma21LocalDyadic` | `Bong/Papers/He2023ADC.lean` | `PROVED_SPECIALIZATION_ONLY` |
| He ADC, Lemma 6.12 | `Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC`, `heADCExceptionalQuaternaryCandidate_not_is3ADC`, `heADCExceptionalQuaternaryCandidate_not_isOMaximal` | `Bong/Bong/He2023ADCExceptionalQuaternaryNonThree.lean` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` |

All listed endpoints have zero project-specific law/data parameters in their
public signatures. The theorem-level status is provisional solely because the
required independent semantic sign-offs have not yet been recorded.

For Beli 2020, `PROVISIONAL_MATCH` also records the frozen source
discrepancy in Theorem 3.1(3.2.1--2): direct substitution gives coefficient
`2r_1`, whereas the paper prints `r_1`.  No inferred correction is presented
as author-confirmed text.
