/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicNumberFieldLocalExtension

/-! Focused audit for the number-field coefficient extension in Lemma 8.1. -/

open Bong
open Bong.HeClassic2024NumberFieldLocalExtension
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

#print axioms adicOrder_liesOver
#print axioms relativeRamificationIndex_pos
#print axioms absoluteRamificationIndex_tower
#print axioms RemainingCoefficientInputs.toLocalExtensionData
#print axioms RemainingCoefficientInputs.lemma81Laws
#print axioms completionMap_coe
#print axioms continuous_completionMap

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
