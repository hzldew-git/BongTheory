/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicNumberFieldBONGBridge

/-! Focused audit for the number-field coefficient extension in Lemma 8.1. -/

open Bong
open Bong.HeClassic2024NumberFieldLocalExtension
open Bong.HeClassic2024NumberFieldBONGBridge
open scoped NumberField

#check adicOrder
#check adicOrder_liesOver
#check relativeRamificationIndex_pos
#check absoluteRamificationIndex_tower
#check RemainingCoefficientInputs
#check RemainingCoefficientInputs.toLocalExtensionData
#check RemainingCoefficientInputs.lemma81Laws
#check completionMap
#check completionMap_coe
#check continuous_completionMap
#check completionMap_valuation
#check completionAdicOrder
#check completionAdicOrder_liesOver
#check CompletionIsQuadraticApproximation
#check completionQuadraticDefect
#check natCast_le_completionQuadraticDefect
#check completionIsQuadraticApproximation_map
#check completionQuadraticDefect_scale
#check completionQuadraticDefectQ
#check completionQuadraticDefectQ_scale
#check CompletionBONGConditions
#check CompletionGoodBONGCoefficients
#check completionGoodBONGCoefficients_map
#check completionLocalExtensionData
#check completionLemma81Laws
#check NumberFieldCompletion.residueMap_surjective
#check NumberFieldCompletion.finiteResidueField
#check NumberFieldCompletion.isNonarchimedeanLocalField
#check NumberFieldCompletion.adicOrder
#check NumberFieldCompletion.dyadicContext
#check ordUnit_eq_completionAdicOrder
#check isQuadraticApproximation_iff_completion
#check quadraticDefect_eq_completionQuadraticDefect
#check defectOrder_eq_completionQuadraticDefectQ
#check ramificationIndex_eq_idealRamificationIdx
#check completionGoodBONGCoefficients_weakTwoStep
#check completionGoodBONGCoefficients_adjacentAdmissible
#check goodBONG_completionGoodBONGCoefficients
#check completionGoodBONGCoefficients_hasGoodBONG
#check isDyadic_of_liesOver
#check completionGoodBONGCoefficients_map_hasGoodBONG
#check goodBONG_mappedValues_haveRealization

#print axioms adicOrder_liesOver
#print axioms relativeRamificationIndex_pos
#print axioms absoluteRamificationIndex_tower
#print axioms RemainingCoefficientInputs.toLocalExtensionData
#print axioms RemainingCoefficientInputs.lemma81Laws
#print axioms completionMap_coe
#print axioms continuous_completionMap
#print axioms completionMap_valuation
#print axioms completionAdicOrder_liesOver
#print axioms natCast_le_completionQuadraticDefect
#print axioms completionIsQuadraticApproximation_map
#print axioms completionQuadraticDefect_scale
#print axioms completionQuadraticDefectQ_scale
#print axioms completionGoodBONGCoefficients_map
#print axioms completionLocalExtensionData
#print axioms completionLemma81Laws
#print axioms NumberFieldCompletion.residueMap_surjective
#print axioms NumberFieldCompletion.finiteResidueField
#print axioms NumberFieldCompletion.adicOrder
#print axioms NumberFieldCompletion.dyadicContext
#print axioms ordUnit_eq_completionAdicOrder
#print axioms isQuadraticApproximation_iff_completion
#print axioms quadraticDefect_eq_completionQuadraticDefect
#print axioms defectOrder_eq_completionQuadraticDefectQ
#print axioms ramificationIndex_eq_idealRamificationIdx
#print axioms completionGoodBONGCoefficients_weakTwoStep
#print axioms completionGoodBONGCoefficients_adjacentAdmissible
#print axioms goodBONG_completionGoodBONGCoefficients
#print axioms completionGoodBONGCoefficients_hasGoodBONG
#print axioms isDyadic_of_liesOver
#print axioms completionGoodBONGCoefficients_map_hasGoodBONG
#print axioms goodBONG_mappedValues_haveRealization

open scoped CompletionLiesOver in
example
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal] :
    Module.Finite (p.adicCompletion K) (P.adicCompletion L) := by
  infer_instance

open scoped CompletionLiesOver in
example
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal] :
    FiniteDimensional (p.adicCompletion K) (P.adicCompletion L) := by
  infer_instance
