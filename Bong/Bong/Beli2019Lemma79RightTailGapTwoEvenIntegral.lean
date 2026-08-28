/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoLowWitnessOrders

/-!
# Beli (2019), Lemma 7.9(ii), case 8: even integral branch

For a low domination witness, strictness of the final coefficient gives a
strict inequality one unit above `beta_i`.  If the final comparison alpha is
integral, then the primary coefficient and `beta_i` are both integral, so
the strict inequality rounds to the desired weak beta bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The strict low-witness branch with integral `gamma_(i-1)` proves
`B_i <= beta_i` by discrete rounding. -/
theorem caseEight_gapTwo_even_beta_bound_of_strict_lowWitness_integral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hiTwo : 2 <= i.val) (j : Fin (n + 1))
    (hsource : b.order first.castSucc = c.order j.castSucc + 1)
    (hstrict :
      ((((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
            WithTop Rat) <
        ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first : Rat) : WithTop Rat))
    (hintegral : IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  apply WithTop.coe_le_coe.mpr
  have hprimaryTop :=
    lemma79_even_representationAlphaValue_le_primaryCoefficient
      b c i hiTwo
  have hprimary : b.representationAlphaValue c i <=
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) := by
    exact_mod_cast hprimaryTop
  have hstrictQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) <
        ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first := by
    exact_mod_cast hstrict
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hprimaryLt :
      ((b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) <
        b.alphaValue (caseEightLastAlphaIndex i) + 1 := by
    have hsourceQ : (b.order first.castSucc : Rat) =
        (c.order j.castSucc : Rat) + 1 := by
      exact_mod_cast hsource
    push_cast at hstrictQ hcentral hsourceQ ⊢
    linarith
  rcases hintegral with ⟨z, hz⟩
  rcases H.alpha_odd (caseEightLastAlphaIndex i) hfirstLast le_rfl with
    ⟨w, hwOdd, hw⟩
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) + z <= w := by
    have hcast :
        ((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) + z : Int) : Rat) <
          ((w + 1 : Int) : Rat) := by
      rw [hz, hw] at hprimaryLt
      push_cast at hprimaryLt ⊢
      linarith
    have hint : b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) + z < w + 1 := by
      exact_mod_cast hcast
    omega
  calc
    b.representationAlphaValue c i <=
        ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) := hprimary
    _ <= b.alphaValue (caseEightLastAlphaIndex i) := by
      rw [hz, hw]
      push_cast
      exact_mod_cast hcoefficientInt

end BONG.GoodBONG

end Bong
