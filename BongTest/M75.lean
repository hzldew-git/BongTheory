/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorSquareClass

/-!
# M75 Definition 6 source correction and quotient-embedding smoke tests
-/

namespace BongTest.M75

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : Function.Injective (valuationUnitClassToSquareClass K) :=
  valuationUnitClassToSquareClass_injective K

example (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorGroup K a = ⊥ ∧
      beliNormGeneratorSquareClassGroup K a = ⊥ :=
  ⟨beliNormGeneratorGroup_of_two_e_lt K a hR,
    beliNormGeneratorSquareClassGroup_of_two_e_lt K a hR⟩

#print axioms Bong.Dyadic.valuationUnitClassToSquareClass_injective
#print axioms
  Bong.Dyadic.valuationUnitClassSubgroupSquareImage_principalUnit_inf_norm
#print axioms Bong.beliNormGeneratorSquareClassGroup_of_two_e_lt

end

end BongTest.M75
