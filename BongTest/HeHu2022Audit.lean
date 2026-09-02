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
#check Bong.heHuHyperbolicHeadIsometry
#check Bong.heHuHyperbolicHeadGoodBONG
#check Bong.BONG.GoodBONG.heHu2022Lemma39i
#check Bong.BONG.GoodBONG.heHu2022Lemma39ii
#check Bong.BONG.GoodBONG.heHu2022Lemma39iii
#check Bong.heHu2022Lemma310BONG
#check Bong.heHu2022Lemma310HyperbolicValues
#check Bong.heHu2022Lemma310TailValues
#check Bong.heHu2022Lemma310_fullPrefixProduct
#check Bong.heHu2022Lemma310_hyperbolicPrefix_eq
#check Bong.heHu2022Lemma310
#check Bong.BONG.GoodBONG.heHu2022Lemma311iFirstOne
#check Bong.BONG.GoodBONG.heHu2022Lemma311iFirstDelta
#check Bong.BONG.GoodBONG.heHu2022Lemma311iSecondOne
#check Bong.BONG.GoodBONG.heHu2022Lemma311iSecondDelta
#check Bong.BONG.GoodBONG.heHu2022Lemma311iGeneric
#check Bong.BONG.GoodBONG.heHu2022Lemma311iUnitUniformizer
#check Bong.BONG.GoodBONG.heHu2022Lemma311iiFirstUnit
#check Bong.BONG.GoodBONG.heHu2022Lemma311iiFirstUnitUniformizer
#check Bong.BONG.GoodBONG.heHu2022Lemma311iiSecondUnit
#check Bong.BONG.GoodBONG.heHu2022Lemma311iiSecondUnitUniformizer
#check Bong.BONG.GoodBONG.heHuLemma311EvenFirst_prefixProducts_not_isSquare
#check Bong.HeHuRepresentsExactlyOne
#check Bong.heHu2022Lemma313CodimensionOne
#check Bong.heHu2022Lemma313CodimensionTwo
#check Bong.heHu2022Lemma314iRepresents
#check Bong.heHu2022Lemma314i
#check Bong.heHu2022Lemma314ii
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenFirstOne
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenFirstDelta
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenSecondOne
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenSecondDelta
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenGeneric
#check Bong.BONG.GoodBONG.heHu2022Proposition37EvenUnitUniformizer
#check Bong.BONG.GoodBONG.heHu2022Proposition37OddFirstUnit
#check Bong.BONG.GoodBONG.heHu2022Proposition37OddFirstUnitUniformizer
#check Bong.BONG.GoodBONG.heHu2022Proposition37OddSecondUnit
#check Bong.BONG.GoodBONG.heHu2022Proposition37OddSecondUnitUniformizer
#check Bong.Lattice.AmbientlyNUniversal
#check Bong.BONG.GoodBONG.HeHuI1E
#check Bong.BONG.GoodBONG.HeHuI2E
#check Bong.BONG.GoodBONG.HeHuI3E
#check Bong.BONG.GoodBONG.heHuNUniversality_factorization
#check Bong.BONG.GoodBONG.heHuAllRepresentationConditions_iff_components
#check Bong.BONG.GoodBONG.heHuI1E_iff_alternatingInitialOrders_and_boundary
#check Bong.BONG.GoodBONG.heHuI2E_iff_theorem47BoundaryCondition
#check Bong.BONG.GoodBONG.heHuEvenSectionConditions_iff_theorem47StableConditions
#check Bong.BONG.GoodBONG.heHu2022Lemma42
#check Bong.BONG.GoodBONG.heHu2022Lemma43_defectTrigger
#check Bong.BONG.GoodBONG.heHu2022Lemma43_not_represents
#check Bong.BONG.GoodBONG.heHu2022Lemma43
#check Bong.BONG.GoodBONG.heHuTheorem41_of_component_equivalences
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
#print axioms Bong.heHu2022Definition36EvenFirst
#print axioms Bong.heHu2022Definition36EvenSecond
#print axioms Bong.heHu2022Definition36OddFirst
#print axioms Bong.heHu2022Definition36OddSecond
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma39i
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma39ii
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma39iii
#print axioms Bong.heHuHyperbolicHeadIsometry
#print axioms Bong.heHu2022Lemma310HyperbolicValues
#print axioms Bong.heHu2022Lemma310TailValues
#print axioms Bong.heHu2022Lemma310_fullPrefixProduct
#print axioms Bong.heHu2022Lemma310_hyperbolicPrefix_eq
#print axioms Bong.heHu2022Lemma310
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iFirstOne
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iFirstDelta
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iSecondOne
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iSecondDelta
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iGeneric
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iiFirstUnit
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iiFirstUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iiSecondUnit
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma311iiSecondUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHuLemma311EvenFirst_prefixProducts_not_isSquare
#print axioms Bong.heHu2022Lemma313CodimensionOne
#print axioms Bong.heHu2022Lemma313CodimensionTwo
#print axioms Bong.heHu2022Lemma314iRepresents
#print axioms Bong.heHu2022Lemma314i
#print axioms Bong.heHu2022Lemma314ii
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenFirstOne
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenFirstDelta
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenSecondOne
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenSecondDelta
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenGeneric
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37EvenUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37OddFirstUnit
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37OddFirstUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37OddSecondUnit
#print axioms Bong.BONG.GoodBONG.heHu2022Proposition37OddSecondUnitUniformizer
#print axioms Bong.BONG.GoodBONG.heHuNUniversality_factorization
#print axioms Bong.BONG.GoodBONG.heHuAllRepresentationConditions_iff_components
#print axioms Bong.BONG.GoodBONG.heHuI1E_iff_alternatingInitialOrders_and_boundary
#print axioms Bong.BONG.GoodBONG.heHuI2E_iff_theorem47BoundaryCondition
#print axioms Bong.BONG.GoodBONG.heHuEvenSectionConditions_iff_theorem47StableConditions
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma42
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma43_defectTrigger
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma43_not_represents
#print axioms Bong.BONG.GoodBONG.heHu2022Lemma43
#print axioms Bong.BONG.GoodBONG.heHuTheorem41_of_component_equivalences
#print axioms Bong.Lattice.heHuMaximalTestingReduction
