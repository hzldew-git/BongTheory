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
#print axioms Bong.heADC2025Lemma49OddSecondUnitUniformizer
#print axioms Bong.heADC2025Lemma49iiEven
#print axioms Bong.heADC2025Lemma49iiOdd
#print axioms Bong.Lattice.QuadraticLatticeModel.IsNADC.representsExactlyOne_of_ambient
