/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Papers.HeHu2022

/-! Kernel and trust-boundary audit for the He--Hu paper entry. -/

#check Bong.BONG.GoodBONG.HeHuAlternatingInitialOrders
#check Bong.BONG.GoodBONG.HeHuEvenConditions
#check Bong.BONG.GoodBONG.HeHuOddConditions
#check Bong.BONG.GoodBONG.HeHuExceptionalQuaternaryConditions
#check Bong.BONG.GoodBONG.HeHuTheorem11Conditions
#check Bong.BONG.GoodBONG.HeHuTheorem11Statement
#check Bong.BONG.OrthogonalBasisData.heHu2022Lemma22
#check Bong.BONG.GoodBONG.heHuAlpha
#check Bong.BONG.GoodBONG.heHuTruncatedSegmentDefect
#check Bong.BONG.GoodBONG.heHuAdjacentCappedDefect
#check Bong.BONG.GoodBONG.heHu2022Corollary23i
#check Bong.BONG.GoodBONG.heHu2022Corollary23ii
#check Bong.BONG.GoodBONG.heHu2022Proposition25
#check Bong.BONG.GoodBONG.heHu2022Proposition26
#check Bong.BONG.GoodBONG.heHu2022Proposition27i
#check Bong.BONG.GoodBONG.heHu2022Proposition27ii
#check Bong.BONG.GoodBONG.heHu2022Proposition27iiiiv
#check Bong.BONG.GoodBONG.heHu2022Proposition27v
#check Bong.BONG.GoodBONG.heHu2022Theorem28
#check Bong.BONG.GoodBONG.heHu2022Lemma29
#check Bong.BONG.GoodBONG.heHu2022Lemma210i
#check Bong.BONG.GoodBONG.heHu2022Lemma210ii
#check Bong.BONG.GoodBONG.heHu2022Lemma210iii
#check @Bong.BONG.GoodBONG.heHu2022Lemma211
#check Bong.HeHuSharpDomain
#check Bong.HeHuSharpData
#check Bong.heHuSharp
#check Bong.heHu2022Proposition32
#check Bong.heHu2022Proposition33
#check Bong.heHu2022Definition34Proposition35Odd
#check Bong.heHu2022Definition34Proposition35Even
#check Bong.heHu2022Proposition35iiOdd
#check Bong.heHu2022Proposition35iiEven
#check Bong.heHu2022Proposition35iiiOddFirst
#check Bong.heHu2022Proposition35iiiOddSecond
#check Bong.heHu2022Proposition35iiiEvenFirst
#check Bong.heHu2022Proposition35iiiEvenSecond
#check Bong.Lattice.heHuMaximalTestingReduction

#print Bong.BONG.GoodBONG.HeHuTheorem11Statement
#print axioms Bong.BONG.OrthogonalBasisData.heHu2022Lemma22
#print axioms Bong.BONG.GoodBONG.heHu2022Corollary23i
#print axioms Bong.BONG.GoodBONG.heHu2022Corollary23ii
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition25
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition26
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition27i
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition27ii
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition27iiiiv
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition27v
#print axioms Bong.BONG.GoodBONG.heHu2022Theorem28
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma29
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma210i
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma210ii
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma210iii
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma211ExceptionalTail
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma211BetaClaim
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma211
#print axioms Bong.heHuSharpData_sourceDefect_integer
#print axioms Bong.heHu2022Proposition32
#print axioms Bong.heHu2022Proposition33
#print axioms Bong.heHu2022Definition34Proposition35Odd
#print axioms Bong.heHu2022Definition34Proposition35Even
#print axioms Bong.heHu2022Proposition35iiOdd
#print axioms Bong.heHu2022Proposition35iiEven
#print axioms Bong.heHu2022Proposition35iiiOddFirst
#print axioms Bong.heHu2022Proposition35iiiOddSecond
#print axioms Bong.heHu2022Proposition35iiiEvenFirst
#print axioms Bong.heHu2022Proposition35iiiEvenSecond
#print axioms Bong.Lattice.heHuMaximalTestingReduction
