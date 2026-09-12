/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicNumberFieldLocalExtension

/-! Focused audit for the number-field coefficient extension in Lemma 8.1. -/

open Bong
open Bong.HeClassic2024NumberFieldLocalExtension

#check adicOrder
#check adicOrder_liesOver
#check relativeRamificationIndex_pos
#check absoluteRamificationIndex_tower
#check RemainingCoefficientInputs
#check RemainingCoefficientInputs.toLocalExtensionData
#check RemainingCoefficientInputs.lemma81Laws

#print axioms adicOrder_liesOver
#print axioms relativeRamificationIndex_pos
#print axioms absoluteRamificationIndex_tower
#print axioms RemainingCoefficientInputs.toLocalExtensionData
#print axioms RemainingCoefficientInputs.lemma81Laws
