/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryConnectivityComplete

/-!
# Beli 2009/2010 public-theorem axiom audit

This file lists every numbered result of the paper, together with the
unnumbered conclusions formalized in Section 5.  A build prints the kernel
kernel dependencies of each public declaration.
-/

-- Section 2
#print axioms Bong.BONG.GoodBONG.beli2009Lemma21
#print axioms Bong.BONG.GoodBONG.beli2009Lemma21_le_segmentAlpha
#print axioms Bong.BONG.GoodBONG.alphaLeftEndpoint_monotone
#print axioms Bong.BONG.GoodBONG.alphaRightEndpoint_antitone
#print axioms Bong.BONG.GoodBONG.beli2009Corollary23
#print axioms Bong.BONG.GoodBONG.beli2009Lemma24_left
#print axioms Bong.BONG.GoodBONG.beli2009Lemma24_right
#print axioms Bong.BONG.GoodBONG.beli2009Corollary25_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary25_ii
#print axioms Bong.BONG.GoodBONG.beli2009Remark26_scaling
#print axioms Bong.BONG.GoodBONG.beli2009Remark26_duality
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_i
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_ii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_iii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma27_iv
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_ii
#print axioms Bong.BONG.GoodBONG.beli2009Corollary28_iii
#print axioms Bong.BONG.GoodBONG.beli2009Corollary29_i
#print axioms Bong.BONG.GoodBONG.beli2009Corollary29_ii
#print axioms Bong.Lattice.beli2009Lemma210
#print axioms Bong.Lattice.OrthogonalDecomposition.beli2009Lemma211
#print axioms Bong.Lattice.StableJordanBoundaryData.beli2009Lemma212
#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.beli2009Lemma213_i
#print axioms Bong.BONG.GoodBONG.JordanBlockCoordinates.beli2009Lemma213_ii
#print axioms Bong.BONG.GoodBONG.JordanBlockLatticeData.beli2009Lemma213_iii
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214_unary
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214
#print axioms Bong.BONG.GoodBONG.beli2009Lemma214_of_firstBlock_not_unary
#print axioms Bong.Lattice.UnaryJordanIdealData.beli2009Lemma215
#print axioms Bong.BONG.GoodBONG.InternalJordanAlphaData.beli2009Lemma216_i
#print axioms Bong.BONG.GoodBONG.BoundaryJordanAlphaData.beli2009Lemma216_ii
#print axioms Bong.BONG.GoodBONG.InternalJordanAlphaData.beli2009Corollary217_i
#print axioms Bong.Lattice.beli2009Corollary217_ii

-- Section 3
#print axioms Bong.BONG.GoodBONG.beli2009Lemma32
#print axioms Bong.BONG.GoodBONG.JordanClassificationReduction.beli2009Lemma33
#print axioms Bong.BONG.GoodBONG.beli2009Lemma34
#print axioms Bong.QuadraticSpace.beli2009Lemma35_i
#print axioms Bong.QuadraticSpace.beli2009Lemma35_ii
#print axioms Bong.QuadraticSpace.beli2009Lemma35_iii
#print axioms Bong.Beli2009RepresentationSwitchData.beli2009Lemma36_i
#print axioms Bong.Beli2009RepresentationSwitchData.beli2009Lemma36_ii
#print axioms Bong.Beli2009PrefixRepresentationBridge.beli2009Lemma37_i
#print axioms Bong.Beli2009PrefixRepresentationBridge.beli2009Lemma37_ii
#print axioms Bong.Beli2009RegularBoundaryThresholdData.beli2009Lemma38_i
#print axioms Bong.Beli2009RegularBoundaryThresholdData.beli2009Lemma38_ii
#print axioms Bong.Beli2009UnaryBoundaryThresholdData.beli2009Lemma38_iii
#print axioms Bong.Beli2009RepresentationReduction.beli2009Lemma39
#print axioms Bong.Beli2009ClassificationReduction.beli2009Theorem31

-- Section 4
#print axioms Bong.BONG.GoodBONG.beli2009Lemma41
#print axioms Bong.Beli2009ClassificationReduction.beli2009Theorem42

-- Section 5
#print axioms Bong.beli2009Lemma51
#print axioms Bong.BONG.GoodBONG.beli2009Remark52
#print axioms Bong.BONG.GoodBONG.beli2009Section5_recursiveAlphaFormula
#print axioms Bong.beli2009Section5_binaryTransformations_necessary
#print axioms Bong.beli2009Section5_residueTwoParametricCounterexample
#print axioms Bong.beli2009Section5_binaryTransformationDichotomy
#print axioms Bong.beli2009Section5_q2Counterexample
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoCounterexample_proved
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved
#check @Bong.beli2009Section5_largeResidueConnectivity_proved
#check @Bong.beli2009Section5_binaryTransformationDichotomy_proved
#print axioms Bong.Beli2009FinalRemarksProof.LargeResidueConnectivity.reachable_of_largeResidue_unconditional
#print axioms Bong.Beli2009FinalRemarksProof.LargeResidueConnectivity.beli2009BinaryTransformationLawsProved
#print axioms Bong.beli2009Section5_largeResidueConnectivity_proved
#print axioms Bong.beli2009Section5_binaryTransformationDichotomy_proved
