/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma72Proof

/-!
# M103 Beli 2003, Lemma 7.2 smoke tests
-/

namespace BongTest.M103

open Bong Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example {k : Nat} (a : Fin k → Kˣ) (R : Int) :
    ordUnit K (lemma72CombinedParameter (K := K) a R) = R :=
  ordUnit_lemma72CombinedParameter a R

example (a : Kˣ)
    (hclass : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)) :
    beliParameterDefectOrderQ (K := K) a = ⊤ :=
  beliParameterDefectOrderQ_eq_top_of_negativeQuarter a hclass

example (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliSpinorGroupRepresentative K a ≤
        valuationUnitSquareClassSubgroup K ↔
      SatisfiesLemma72UnitCriterion (K := K) a :=
  beliLemma72_i a ha

example {k : Nat} (a : Fin k → Kˣ) (R : Int) (hk : 0 < k)
    (ha : ∀ i, IsLemma72UnitParameter (K := K) (a i))
    (hR : Even R) (horder : ∀ i, ordUnit K (a i) ≤ R) :
    IsLemma72UnitParameter (K := K)
      (lemma72CombinedParameter (K := K) a R) :=
  beliLemma72_ii a R hk ha hR horder

#print axioms Bong.Dyadic.ordUnit_lemma72CombinedParameter
#print axioms Bong.Dyadic.beliParameterDefectOrderQ_eq_top_of_negativeQuarter
#print axioms Bong.Dyadic.beliLemma72_i
#print axioms Bong.Dyadic.beliLemma72_i_defect_lower_bound
#print axioms Bong.Dyadic.beliLemma72_ii
#print axioms Bong.Dyadic.beliLemma72_i_proved
#print axioms Bong.Dyadic.beliLemma72_ii_proved
#print axioms Bong.beliLemma72LawsProved

end BongTest.M103
