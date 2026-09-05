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
