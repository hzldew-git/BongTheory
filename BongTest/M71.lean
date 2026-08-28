/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorSquareClass

/-!
# M71 unit-to-field square-class map smoke tests
-/

namespace BongTest.M71

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (u : valuationUnitSubgroup K) :
    valuationUnitClassToSquareClass K (valuationUnitClassHom K u) =
      squareClass K (u : Kˣ) :=
  valuationUnitClassToSquareClass_apply K u

example (a : Kˣ) {c : ValuationUnitClass K}
    (hc : c ∈ beliNormGeneratorGroup K a) :
    valuationUnitClassToSquareClass K c ∈
      beliNormGeneratorSquareClassGroup K a :=
  valuationUnitClassToSquareClass_mem_beliNormGeneratorGroup K hc

#print axioms Bong.Dyadic.valuationUnitClassToSquareClass_apply
#print axioms Bong.valuationUnitClassToSquareClass_mem_beliNormGeneratorGroup

end

end BongTest.M71
