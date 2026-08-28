/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.BeliGroups

/-!
# M62 Beli norm-generator group smoke tests
-/

namespace BongTest.M62

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (a : Kˣ) :
    IsValuationUnit K (normalizedUnitPart K a : K) :=
  normalizedUnitPart_isValuationUnit K a

example (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorGroup K a = ⊥ :=
  beliNormGeneratorGroup_of_two_e_lt K a hR

#print axioms Bong.Dyadic.normalizedUnitPart_isValuationUnit
#print axioms Bong.Dyadic.uniformizerPower_mul_normalizedUnitPart
#print axioms Bong.Dyadic.beliNormGeneratorGroup
#print axioms Bong.Dyadic.beliNormGeneratorGroup_of_low_defect

end

end BongTest.M62
