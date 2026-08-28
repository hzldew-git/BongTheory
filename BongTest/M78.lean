/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma313II

/-!
# M78 Beli 2003, Lemma 3.13(ii) smoke test
-/

namespace BongTest.M78

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [UnitQuadraticDefectParityLaws K]
  [PrincipalUnitSquareClassFiltrationLaws K]

example (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * ε) :=
  beliSpinorGroupRepresentative_eq_evenShift_normGenerator
    R ε hε ha hRupper hEven hdLower

#print axioms
  Bong.Dyadic.beliSpinorGroupRepresentative_eq_evenShift_normGenerator

end

end BongTest.M78
