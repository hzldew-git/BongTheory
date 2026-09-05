/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Papers.He2023ADC

/-! Kernel and trust-boundary audit for He's n-ADC paper entry. -/

#check Bong.Lattice.IsNADC
#check Bong.Lattice.IsNUniversal.isNADC
#check Bong.Lattice.RepresentsAllRelevantOMaximalOfRank
#check Bong.Lattice.heADCLemma21LocalDyadic
#check Bong.Lattice.IsOMaximal.isNADC
#check Bong.Lattice.IsNADC.isOMaximal_of_finrank_eq
#check Bong.Lattice.isNADC_iff_isOMaximal_of_finrank_eq
#check Bong.Lattice.IsNADC.isNUniversal_of_ambientlyNUniversal
#check Bong.Lattice.isNADC_iff_isNUniversal_of_rank_add_three_le
#check Bong.GlobalLocalLatticeSystem.IsGloballyNADC
#check Bong.GlobalLocalLatticeSystem.IsGloballyNUniversal
#check Bong.GlobalLocalLatticeSystem.IsNRegular
#check Bong.GlobalLocalLatticeSystem.Theorem13Laws
#check Bong.GlobalLocalLatticeSystem.heADCTheorem13
#check Bong.GlobalLocalLatticeSystem.heADCTheorem14i
#check Bong.GlobalLocalLatticeSystem.heADCTheorem14ii
#check Bong.GlobalLocalLatticeSystem.heADCTheorem14iii

#check Bong.BONG.OrthogonalBasisData.heADC2025Lemma31
#check Bong.BONG.GoodBONG.heADC2025Corollary32i
#check Bong.BONG.GoodBONG.heADC2025Corollary32ii
#check Bong.BONG.GoodBONG.heADC2025Proposition33
#check Bong.BONG.GoodBONG.heADC2025Proposition34
#check Bong.BONG.GoodBONG.heADC2025Proposition35
#check Bong.BONG.GoodBONG.heADC2025Theorem36

#check Bong.heADC2025Proposition42iOdd
#check Bong.heADC2025Proposition42iEven
#check Bong.heADC2025Proposition42iiOdd
#check Bong.heADC2025Proposition42iiEven
#check Bong.heADC2025Proposition42iiiOddFirst
#check Bong.heADC2025Proposition42iiiOddSecond
#check Bong.heADC2025Proposition42iiiEvenFirst
#check Bong.heADC2025Proposition42iiiEvenSecond
#check Bong.heADC2025Remark43OddCard
#check Bong.heADC2025Remark43EvenCardOfPos
#check Bong.heADC2025Remark43EvenCardZero
#check Bong.heADC2025Remark43OddMaximal
#check Bong.heADC2025Remark43EvenMaximal
#check Bong.heADC2025Lemma44iOdd
#check Bong.heADC2025Lemma44iEven
#check Bong.heADC2025Lemma44ii
#check Bong.heADC2025Lemma44iii
#check Bong.heADC2025Lemma45iCodimensionOne
#check Bong.heADC2025Lemma45iCodimensionTwo
#check Bong.HeADCIsRepresentedByExactlyOne
#check Bong.heADC2025Lemma45iiCodimensionOne
#check Bong.heADC2025Lemma45iiCodimensionTwo
#check Bong.heADC2025Lemma49EvenFirstOne
#check Bong.heADC2025Lemma49EvenFirstDelta
#check Bong.heADC2025Lemma49EvenSecondOne
#check Bong.heADC2025Lemma49EvenSecondDelta
#check Bong.heADC2025Lemma49EvenGeneric
#check Bong.heADC2025Lemma49EvenUnitUniformizer
#check Bong.heADC2025Lemma49OddFirstUnit
#check Bong.heADC2025Lemma49OddFirstUnitUniformizer
#check Bong.heADC2025Lemma49OddSecondUnit
#check Bong.heADC2025Lemma49OddSecondUnitUniformizer
#check Bong.heADC2025Lemma49iiEven
#check Bong.heADC2025Lemma49iiOdd
#check Bong.Lattice.isOMaximal_iff_volumeOrder_eq_of_ambientlyIsometric
#check Bong.BONG.GoodBONG.HeADCMaximalProfileCriterion
#check Bong.BONG.GoodBONG.heADC2025Remark410
#check Bong.BONG.GoodBONG.heADC2025Lemma411iOne
#check Bong.BONG.GoodBONG.heADC2025Lemma411iDelta
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiOne
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiDelta
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnit
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitUniformizer
#check Bong.BONG.GoodBONG.heADC2025Lemma412i
#check Bong.BONG.GoodBONG.heADC2025Lemma412ii
#check Bong.BONG.GoodBONG.heADC2025Lemma412iiiFirst
#check Bong.BONG.GoodBONG.heADC2025Lemma412iiiSecond
#check Bong.heADCW1Unary
#check Bong.heADCN1Unary
#check Bong.BONG.GoodBONG.ambientIsometric_of_diagonalRepresents
#check Bong.BONG.GoodBONG.isIsometric_publishedModel_iff_orderProfile
#check Bong.BONG.GoodBONG.heADC2025Lemma411iOnePublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iDeltaPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiOnePublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiDeltaPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitFirstPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitSecondPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUniformizerFirstPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma411iiiUniformizerSecondPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma412iPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma412iiPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma412iiiFirstPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma412iiiSecondPublished
#check Bong.BONG.GoodBONG.heADC2025Lemma412UnaryPublished
#check Bong.Lattice.QuadraticLatticeModel.IsNADC.representsExactlyOne_of_ambient
#check Bong.Lattice.QuadraticLatticeModel.IsNADC.represents_every_of_ambient
#check Bong.Lattice.heADCLemma414LocalDyadic
#check Bong.Lattice.heADCProposition415LocalDyadic
#check Bong.Lattice.heADCTheorem14iLocalDyadic

#print axioms Bong.Lattice.heADCLemma21LocalDyadic
#print axioms Bong.Lattice.heADCLemma414LocalDyadic
#print axioms Bong.Lattice.heADCProposition415LocalDyadic
#print axioms Bong.Lattice.heADCTheorem14iLocalDyadic
#print axioms Bong.GlobalLocalLatticeSystem.heADCTheorem13
#print axioms Bong.BONG.GoodBONG.heADC2025Theorem36
#print axioms Bong.heADC2025Proposition42iiiEvenFirst
#print axioms Bong.heADC2025Lemma44iii
#print axioms Bong.heADC2025Lemma45iCodimensionTwo
#print axioms Bong.heADC2025Lemma45iiCodimensionTwo
#print axioms Bong.heADC2025Lemma49EvenFirstOne
#print axioms Bong.heADC2025Lemma49OddSecondUnit
#print axioms Bong.heADC2025Lemma49OddSecondUnitUniformizer
#print axioms Bong.heADC2025Lemma49iiEven
#print axioms Bong.heADC2025Lemma49iiOdd
#print axioms Bong.Lattice.isOMaximal_iff_volumeOrder_eq_of_ambientlyIsometric
#print axioms Bong.BONG.GoodBONG.heADC2025Remark410
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iOne
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iDelta
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiOne
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiDelta
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnit
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412i
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412ii
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iiiFirst
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iiiSecond
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iOnePublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iDeltaPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiOnePublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiDeltaPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitFirstPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUnitSecondPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUniformizerFirstPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma411iiiUniformizerSecondPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iiPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iiiFirstPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412iiiSecondPublished
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma412UnaryPublished
#print axioms Bong.Lattice.QuadraticLatticeModel.IsNADC.representsExactlyOne_of_ambient

#check @Bong.BONG.GoodBONG.exists_heADCOddNormalizedAmbient
#check @Bong.BONG.GoodBONG.heADCOddMaximal_orders
#check @Bong.BONG.GoodBONG.heADC2025Proposition413
#print Bong.BONG.GoodBONG.HeADCProposition413Conclusions
#print axioms Bong.BONG.GoodBONG.exists_heADCOddNormalizedAmbient
#print axioms Bong.BONG.GoodBONG.heADCOddMaximal_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Proposition413

#check @Bong.Lattice.IsOMaximal.represents_halfHyperbolic_iff
#check @Bong.heADCAForm_bilin_apply
#check @Bong.heADCN2QuaternaryOne_isIsometric_A_product_scaledA
#check @Bong.Lattice.heADC2025Proposition416Dyadic
#print axioms Bong.Lattice.IsOMaximal.represents_halfHyperbolic_iff
#print axioms Bong.heADCAForm_bilin_apply
#print axioms Bong.heADCDiscriminantEndpoint_isIsometric_scaledA
#print axioms Bong.heADCN2QuaternaryOne_isIsometric_A_product_scaledA
#print axioms Bong.Lattice.IsOMaximal.isAnisotropic_iff_heADCN2QuaternaryOne
#print axioms Bong.Lattice.heADC2025Proposition416Dyadic

#check @Bong.BONG.GoodBONG.heADCAlternatingPrefix_of_represented_endpoint
#check @Bong.BONG.GoodBONG.heADCComparisonPrefix_isSquare_of_strict_crossGap
#check @Bong.BONG.GoodBONG.heADCBoundaryOrder_zero_of_two_represented_classes
#print axioms Bong.BONG.GoodBONG.heADCAlternatingPrefix_of_represented_endpoint
#print axioms Bong.BONG.GoodBONG.heADCComparisonPrefix_isSquare_of_strict_crossGap
#print axioms Bong.BONG.GoodBONG.heADCBoundaryOrder_zero_of_two_represented_classes

#check @Bong.heADCEvenFirstTest_orders
#check @Bong.heADCEvenFirstTests_prefixProduct_not_square
#check @Bong.BONG.GoodBONG.heADCEvenFirstTests_rank_gt
#check @Bong.BONG.GoodBONG.heADC2025Lemma64ii
#print axioms Bong.heADCMaximalGoodBONG_prefixProduct_det_square
#print axioms Bong.heADCEvenFirstTest_orders
#print axioms Bong.heADCEvenFirstTests_det_not_square
#print axioms Bong.heADCEvenFirstTests_prefixProduct_not_square
#print axioms Bong.BONG.GoodBONG.heADCEvenFirstTests_rank_gt
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma64ii

#check @Bong.BONG.GoodBONG.heADCEvenFirstTest_alternatingOrders
#check @Bong.BONG.GoodBONG.heADCEvenFirstTest_signedPrefixDefect
#check @Bong.BONG.GoodBONG.heADC2025Lemma64i
#print axioms Bong.heADCEvenFirstTest_parameterDefect
#print axioms Bong.BONG.GoodBONG.heADCEvenFirstTest_alternatingOrders
#print axioms Bong.BONG.GoodBONG.heADCEvenFirstTest_signedPrefixDefect
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma64i

#check @Bong.heADCEvenSecondTest_orders
#check @Bong.BONG.GoodBONG.heADC2025Lemma64iii
#print axioms Bong.heADCMaximalOrderProfile_raisedFour
#print axioms Bong.heADCEvenSecondTest_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma64iii

#check @Bong.heADCKappaSharpDomain
#check @Bong.heADCKappaTest_lastOrders
#check @Bong.BONG.GoodBONG.heADCEvenMixedTest_bound
#check @Bong.BONG.GoodBONG.heADC2025Lemma64iv
#print axioms Bong.heADCKappaSharpDomain
#print axioms Bong.heADCKappaTest_lastOrders
#print axioms Bong.heADCEvenFirst_determinantClass
#print axioms Bong.heADCEvenSecond_determinantClass
#print axioms Bong.heADCEvenTests_determinants_not_square
#print axioms Bong.BONG.GoodBONG.heADCEvenMixedTest_bound
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma64iv

#check @Bong.BONG.GoodBONG.heADCTerminalDefectCondition_fails
#check @Bong.BONG.GoodBONG.heADCUniformizerTest_orders
#check @Bong.BONG.GoodBONG.heADC2025Lemma65i
#print axioms Bong.BONG.GoodBONG.heADCTerminalDefectCondition_fails
#print axioms Bong.BONG.GoodBONG.heADCUniformizerTest_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma65i_of_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma65i

#check @Bong.BONG.GoodBONG.heADCExtremalPairs_prefixDefect
#check @Bong.BONG.GoodBONG.heADCEvenPenultimate_mixedDefect
#check @Bong.BONG.GoodBONG.heADC2025Lemma65ii
#print axioms Bong.BONG.GoodBONG.heADCExtremalPairs_prefixDefect
#print axioms Bong.BONG.GoodBONG.heADCEvenPenultimate_mixedDefect
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma65ii_of_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma65ii

#check @Bong.BONG.GoodBONG.heADCMaximal_represents_iff_diagonalRepresents
#check @Bong.BONG.GoodBONG.heADC2025Lemma46iEvenCorankOne
#check @Bong.BONG.GoodBONG.heADCCorankOne_uniformizerTest
#check @Bong.BONG.GoodBONG.heADCEvenCorankOne_orders
#print axioms Bong.BONG.GoodBONG.heADCMaximal_represents_iff_diagonalRepresents
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma46iEvenCorankOne
#print axioms Bong.BONG.GoodBONG.heADCCorankOne_uniformizerTest
#print axioms Bong.BONG.GoodBONG.heADCEvenCorankOne_orders

#check @Bong.heADCIsOMaximal_of_volumeOrder_le_add_one
#check @Bong.BONG.GoodBONG.heADCCorankOne_standardTail_isOMaximal
#check @Bong.heADCEvenFirstOne_represents_oddFirst
#check @Bong.heADCEvenFirstDelta_represents_oddSecondUniformizer
#check @Bong.BONG.GoodBONG.heADCCorankOne_raisedTail_ambient
#check @Bong.BONG.GoodBONG.heADC2025Theorem61_of_goodBONG
#check @Bong.Lattice.heADC2025Theorem61
#print axioms Bong.heADCIsOMaximal_of_volumeOrder_le_add_one
#print axioms Bong.BONG.GoodBONG.heADCOdd_volumeOrder_split
#print axioms Bong.BONG.GoodBONG.heADCOdd_profile_volumeOrder
#print axioms Bong.BONG.GoodBONG.heADCOdd_prefixSum_eq_of_head_profile
#print axioms Bong.BONG.GoodBONG.heADCCorankOne_standardTail_isOMaximal
#print axioms Bong.heADCEvenFirstOne_represents_oddFirst
#print axioms Bong.heADCEvenFirstDelta_represents_oddSecondUniformizer
#print axioms Bong.BONG.GoodBONG.heADCRaisedTail_not_represents_first
#print axioms Bong.BONG.GoodBONG.heADCCorankOne_raisedTail_ambient
#print axioms Bong.BONG.GoodBONG.heADCCorankOne_raisedTail_isOMaximal
#print axioms Bong.BONG.GoodBONG.heADC2025Theorem61_of_goodBONG
#print axioms Bong.Lattice.heADC2025Theorem61

#check @Bong.BONG.GoodBONG.heADC2025Theorem36Published
#check @Bong.BONG.GoodBONG.heADC2025Theorem36PublishedFull
#print axioms Bong.BONG.GoodBONG.heADC2025Theorem36Published
#print axioms Bong.BONG.GoodBONG.heADC2025Theorem36PublishedFull

#check @Bong.BONG.GoodBONG.heADCEvenCentral_fullMixedDefect
#check @Bong.BONG.GoodBONG.heADCEvenCentral_currentDefect_gt
#check @Bong.BONG.GoodBONG.heADCEvenCentral_defectTrigger
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_fullMixedDefect
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_currentDefect_gt
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_defectTrigger

#check @Bong.BONG.GoodBONG.heADCEvenCentral_prefix_oddFirst
#check @Bong.BONG.GoodBONG.heADCEvenCentral_signedClass
#check @Bong.BONG.GoodBONG.heADCEvenCentral_prefix_evenFirst
#check @Bong.BONG.GoodBONG.heADCEvenCentral_prefix_represents_first
#check @Bong.BONG.GoodBONG.heADCEvenCentral_prefix_not_represents_second
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_prefix_oddFirst
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_signedClass
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_prefix_evenFirst
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_prefix_represents_first
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_prefix_not_represents_second

#check @Bong.BONG.GoodBONG.heADCEvenSecondTest_isometric_orders
#check @Bong.BONG.GoodBONG.heADC2025Lemma66_endpoint
#check @Bong.BONG.GoodBONG.heADC2025Lemma66i
#check @Bong.BONG.GoodBONG.heADC2025Lemma66ii
#print axioms Bong.BONG.GoodBONG.heADCEvenSecondTest_isometric_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma66_endpoint
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma66i
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma66ii

#check @Bong.BONG.GoodBONG.heADCEvenCentral_capped_le_of_represents
#check @Bong.BONG.GoodBONG.heADCEvenCentral_alphaAlternatives_of_capped_le
#check @Bong.BONG.GoodBONG.heADC2025Lemma67_endpoint
#check @Bong.BONG.GoodBONG.heADC2025Lemma67i
#check @Bong.BONG.GoodBONG.heADC2025Lemma67ii
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_capped_le_of_represents
#print axioms Bong.BONG.GoodBONG.heADCEvenCentral_alphaAlternatives_of_capped_le
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma67_endpoint
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma67i
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma67ii

#check @Bong.Lattice.heADC2025Lemma68i
#check @Bong.Lattice.heADC2025Lemma68ii
#print axioms Bong.heADCEvenCodimensionTwo_represents_of_parameter_not_square
#print axioms Bong.heADCEvenFirst_represents_previous
#print axioms Bong.Lattice.heADCMaximal_represents_of_ambient_model
#print axioms Bong.Lattice.heADCEvenCorankTwoFirst_same
#print axioms Bong.Lattice.heADCEvenCorankTwoFirst_of_not_square
#print axioms Bong.Lattice.heADCEvenCorankTwoSecond_of_not_square
#print axioms Bong.BONG.GoodBONG.heADC_prefixProduct_det_square_of_ambient
#print axioms Bong.BONG.GoodBONG.heADC_signedFullDefect_of_ambient
#print axioms Bong.BONG.GoodBONG.heADC_signedFullDefectOrder_of_ambient
#print axioms Bong.BONG.GoodBONG.heADCEvenEndpoint_signedPrefix_defect
#print axioms Bong.BONG.GoodBONG.heADCEvenCorankTwo_endpoint_orders
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma68i_of_goodBONG
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma68ii_of_goodBONG
#print axioms Bong.Lattice.heADC2025Lemma68i
#print axioms Bong.Lattice.heADC2025Lemma68ii

#check @Bong.Lattice.heADC2025Lemma68v
#check @Bong.Lattice.heADC2025Lemma68vi
#check @Bong.heADCSharpDomain_publishedParameter_iff
#check @Bong.Lattice.heADC2025Lemma68vPublished
#check @Bong.Lattice.heADC2025Lemma68viPublished
#print axioms Bong.BONG.GoodBONG.heADCSharpDefectData
#print axioms Bong.BONG.GoodBONG.heADCEvenCorankTwo_orders_of_finite_full_defect
#print axioms Bong.heADCSharp_mul_discriminant_not_square
#print axioms Bong.Lattice.heADCEvenCorankTwo_tests_of_sharp_ambient
#print axioms Bong.BONG.GoodBONG.heADCEvenCorankTwo_sharp_orders
#print axioms Bong.heADCEvenSharpSpace_determinantClass
#print axioms Bong.heADCSharpDomain_of_mul_square
#print axioms Bong.heADCEvenSharpSpace_represents_of_mul_square
#print axioms Bong.Lattice.heADCEvenCorankTwoSharp_normalized
#print axioms Bong.Lattice.heADCEvenCorankTwoSharp_isOMaximal
#print axioms Bong.Lattice.heADC2025Lemma68v
#print axioms Bong.Lattice.heADC2025Lemma68vi
#print axioms Bong.heADCNormalizedRepresentative_eq_one_of_isSquare
#print axioms Bong.heADCSharpDomain_publishedParameter_iff
#print axioms Bong.Lattice.heADC2025Lemma68vPublished
#print axioms Bong.Lattice.heADC2025Lemma68viPublished

#check @Bong.Lattice.heADC2025Lemma68iii
#check @Bong.Lattice.heADC2025Lemma68iv_of_pos
#print axioms Bong.AlternatingEndpointTower.exists_unitScale_of_even_leadingOrders
#print axioms Bong.AlternatingEndpointTower.equalDeterminantRepresentation_of_even_leadingOrders
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_not_evenTower
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_last_ne_neg_twoE
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_terminal_lt
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_terminal_pair
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_orders
#print axioms Bong.BONG.GoodBONG.heADCSecondEndpoint_full_profile
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma68iii_of_goodBONG
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma68iv_of_goodBONG_of_pos
#print axioms Bong.Lattice.heADC2025Lemma68iii
#print axioms Bong.Lattice.heADC2025Lemma68iv_of_pos

#check @Bong.BONG.GoodBONG.exists_heADCQuaternaryBoundaryCandidate
#print axioms Bong.BONG.GoodBONG.heADCBoundaryTail_admissible
#print axioms Bong.BONG.GoodBONG.heADCBoundaryTail_orders
#print axioms Bong.BONG.GoodBONG.heADCBoundaryTail_integral
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_orders
#print axioms Bong.BONG.GoodBONG.heADCBoundaryTail_represents_endpoint
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_second
#print axioms Bong.BONG.GoodBONG.exists_heADCQuaternaryBoundaryCandidate

#check @Bong.BONG.GoodBONG.heADCBoundary_represents_finite
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_hasOrders
#print axioms Bong.BONG.GoodBONG.heADCBoundary_orderCondition
#print axioms Bong.BONG.GoodBONG.heADCBoundary_longConditions
#print axioms Bong.BONG.GoodBONG.heADCBoundary_firstDefect
#print axioms Bong.BONG.GoodBONG.heADCBoundary_middleAlpha
#print axioms Bong.BONG.GoodBONG.heADCBoundary_oddMixedPrefix
#print axioms Bong.BONG.GoodBONG.heADCBoundary_secondComparisonDefect
#print axioms Bong.BONG.GoodBONG.heADCBoundary_secondDefect_of_finite
#print axioms Bong.BONG.GoodBONG.heADCBoundary_terminalMixedDefect
#print axioms Bong.BONG.GoodBONG.heADCBoundary_terminalTrigger_not_of_finite
#print axioms Bong.BONG.GoodBONG.heADCBoundary_firstCentralRepresentation
#print axioms Bong.BONG.GoodBONG.heADCBoundary_represents_finite

#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_N2Delta
#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_N1One
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_splitHead
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_fullDefect
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_finite
#print axioms Bong.BONG.GoodBONG.heADCBoundary_represents_endpoint
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_thirdValue
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_firstTwoIsotropic
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_firstThree_represents
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_endpointTarget
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_N2Delta
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_halfHyperbolic
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_N1One

#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_unitFirst
#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_uniformizerSecond
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_profiledMaximal
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_unitFirst
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_unitSecond
#print axioms Bong.BONG.GoodBONG.heADCBoundary_unitUniformizer_defect_zero
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_uniformizerFirst
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_uniformizerSecond

#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_is2ADC
#check @Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isOMaximal
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_sharp_normalized
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_sharp
#print axioms Bong.BONG.GoodBONG.heADCBoundary_represents_of_diagonalRepresents
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_misses_N1Delta
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_represents_evenTest
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_representsAllRelevantOMaximal
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_is2ADC
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isOMaximal
#check @Bong.BONG.GoodBONG.HeADC2025Lemma68ivBinaryStatement
#print axioms Bong.BONG.GoodBONG.heADCQuaternaryBoundaryCandidate_not_isIsometric_N2Delta
#print axioms Bong.BONG.GoodBONG.not_heADC2025Lemma68ivBinaryStatement

#check @Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC
#check @Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_is3ADC
#check @Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_isOMaximal
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_orders
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_represents_first
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_fullDefect
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_isOMaximal
#print axioms Bong.BONG.GoodBONG.heADCExceptional_represents_finite
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_represents_N1Delta
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_represents_sharp
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_misses_N2Delta
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_representsAllRelevantOMaximal
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_is2ADC
#print axioms Bong.BONG.GoodBONG.heADCExceptional_ternaryTerminalDefect_zero
#print axioms Bong.BONG.GoodBONG.heADCExceptional_ternaryTerminalAlpha_ge_half
#print axioms Bong.BONG.GoodBONG.heADCExceptionalQuaternaryCandidate_not_is3ADC

#check @Bong.BONG.GoodBONG.heADC2025Lemma69
#check @Bong.BONG.GoodBONG.heADC2025Lemma610
#check @Bong.BONG.GoodBONG.heADC2025Lemma611_of_goodBONG
#check @Bong.Lattice.heADC2025Lemma611
#print axioms Bong.BONG.GoodBONG.heADCLemma69_previousDefect
#print axioms Bong.BONG.GoodBONG.heADCLemma69_terminalTrigger
#print axioms Bong.BONG.GoodBONG.heADCLemma69_fullTargetPrefix_representation
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma69
#print axioms Bong.BONG.GoodBONG.heADCLemma610_alphaProfile
#print axioms Bong.BONG.GoodBONG.heADCLemma610_prefixDefectBounds
#print axioms Bong.BONG.GoodBONG.heADCLemma610_internalRepresentations
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma610
#print axioms Bong.BONG.GoodBONG.heADC2025Lemma611_of_goodBONG
#print axioms Bong.Lattice.heADC2025Lemma611
