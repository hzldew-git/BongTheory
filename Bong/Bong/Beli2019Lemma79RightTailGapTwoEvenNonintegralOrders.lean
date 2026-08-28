/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoNonintegralHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: exceptional even orders

Assume the nonintegral branch and, toward the paper's contradiction, that
`B_i > beta_i`.  The strict primary estimate forces the comparison order
at `i - 1` below `S_(u+1) - beta_u`.  If the boundary gap were even, the
odd integral value `beta_u` would exceed it by at least one, contradicting
same-parity monotonicity.  Hence the gap is odd, `beta_u` equals the gap,
and the comparison order at `i - 1` is exactly the norm-floor order `T`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Failure of the beta bound in the nonintegral even branch forces the
odd boundary-gap alternative and pins `T_(i-1)` to `T_1`. -/
theorem caseEight_gapTwo_even_nonintegral_failure_orders
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hfloor : b.order first.castSucc = c.order (0 : Fin (n + 2)) + 1)
    (hfailure : b.alphaValue (caseEightLastAlphaIndex i) <
      b.representationAlphaValue c i)
    (hnot : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    Odd (b.orderGap first) ∧
      b.alphaValue first = (b.orderGap first : Rat) ∧
      c.order (evenTargetPreviousAlphaIndex i).castSucc =
        c.order (0 : Fin (n + 2)) := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpEven : Even p.val := by
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [p, evenTargetPreviousAlphaIndex]
    omega
  have hzeroPreviousEntry := c.orderSequence.entryOrZero_le_of_evenGap
    0 p.val (Nat.zero_le _) (by omega) hpEven
  have hzeroPrevious : c.order (0 : Fin (n + 2)) <=
      c.order p.castSucc := by
    have hzeroEntry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    have hpEntry : c.orderSequence.entryOrZero p.val =
        c.order p.castSucc := by
      simpa using c.orderSequence_entryOrZero_eq_order p.castSucc
    rw [hzeroEntry, hpEntry] at hzeroPreviousEntry
    exact hzeroPreviousEntry
  have halphaLt :=
    representationAlphaValue_lt_order_sub_previous_of_not_integral
      b c i hiTwo hnot
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hpreviousLtQ : (c.order p.castSucc : Rat) <
      (b.order first.succ : Rat) - b.alphaValue first := by
    change b.representationAlphaValue c i <
      ((b.order ⟨i.val, i.lt_large⟩ - c.order p.castSucc : Int) : Rat)
      at halphaLt
    push_cast at halphaLt hcentral ⊢
    linarith
  have hgapLe := H.gap_le first le_rfl hfirstLast
  have hgapAlpha := (b.beli2009Lemma27_iii first hgapLe).1
  rcases H.alpha_odd first le_rfl hfirstLast with
    ⟨z, hzOdd, hz⟩
  rcases Int.even_or_odd (b.orderGap first) with hgapEven | hgapOdd
  · have hgapZ : b.orderGap first <= z := by
      rw [hz] at hgapAlpha
      exact_mod_cast hgapAlpha
    have hgapNe : b.orderGap first ≠ z := by
      intro heq
      rw [<- heq] at hzOdd
      exact Int.not_odd_iff_even.mpr hgapEven hzOdd
    have hgapPlus : b.orderGap first + 1 <= z := by omega
    have hnextMinus : b.order first.succ - z <=
        b.order first.castSucc - 1 := by
      unfold orderGap at hgapPlus
      omega
    have hnextMinusQ : (b.order first.succ : Rat) - (z : Rat) <=
        (b.order first.castSucc : Rat) - 1 := by
      exact_mod_cast hnextMinus
    have hfloorQ : (b.order first.castSucc : Rat) =
        (c.order (0 : Fin (n + 2)) : Rat) + 1 := by
      exact_mod_cast hfloor
    have hzeroPreviousQ : (c.order (0 : Fin (n + 2)) : Rat) <=
        (c.order p.castSucc : Rat) := by
      exact_mod_cast hzeroPrevious
    rw [hz] at hpreviousLtQ
    linarith
  · have halphaEq : b.alphaValue first = (b.orderGap first : Rat) :=
      (b.beli2009Lemma27_iii first hgapLe).2.mpr (Or.inr hgapOdd)
    have hpreviousUpperQ : (c.order p.castSucc : Rat) <
        (c.order (0 : Fin (n + 2)) : Rat) + 1 := by
      rw [halphaEq] at hpreviousLtQ
      unfold orderGap at hpreviousLtQ
      have hfloorQ : (b.order first.castSucc : Rat) =
          (c.order (0 : Fin (n + 2)) : Rat) + 1 := by
        exact_mod_cast hfloor
      push_cast at hpreviousLtQ hfloorQ ⊢
      linarith
    have hpreviousUpper : c.order p.castSucc <
        c.order (0 : Fin (n + 2)) + 1 := by
      exact_mod_cast hpreviousUpperQ
    have hpreviousEq : c.order p.castSucc =
        c.order (0 : Fin (n + 2)) := by omega
    exact ⟨hgapOdd, halphaEq, by simpa only [p] using hpreviousEq⟩

end BONG.GoodBONG

end Bong
