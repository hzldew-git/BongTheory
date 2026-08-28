/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma313

/-!
# M76 Beli 2003, Lemma 3.13(i) smoke tests
-/

namespace BongTest.M76

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hR : 2 * (ramificationIndex K : Int) < R) :
    beliAuxiliarySpinorGroup K
        (uniformizerPowerUnit K R * ε)
        (by
          rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
          exact hR) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) * ε) :=
  beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
    (K := K) R ε hε hR

#print axioms
  Bong.Dyadic.beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup

end

end BongTest.M76
