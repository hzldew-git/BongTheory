/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary315

/-!
# M81 Beli 2003, Corollary 3.15 smoke tests
-/

namespace BongTest.M81

open Bong Bong.Dyadic

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K]
  [BeliHilbertCongruenceLaws K]

example (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRlow : 2 * (ramificationIndex K : Int) < R)
    (hRhigh : R ≤ 4 * (ramificationIndex K : Int)) :
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      cyclicSquareClassSubgroup K (ε * η) ⊔
        beliLemma314CongruenceFactor (K := K)
          (R - 2 * (ramificationIndex K : Int))
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) :=
  beliSpinorGroupRepresentative_sup_of_two_e_lt
    R ε η hε hη ha hb hRlow hRhigh

variable [UnitQuadraticDefectParityLaws K]
  [PrincipalUnitSquareClassFiltrationLaws K]

example (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdε : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hdη : ¬2 * quadraticDefect K (-η) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) :=
  beliSpinorGroupRepresentative_sup_of_even_order
    R ε η hε hη ha hb hRupper hEven hdε hdη

#print axioms Bong.Dyadic.beliSpinorGroupRepresentative_sup_of_two_e_lt
#print axioms Bong.Dyadic.beliSpinorGroupRepresentative_sup_of_even_order

end

end BongTest.M81
