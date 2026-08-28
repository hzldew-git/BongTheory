/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark616

/-!
# Beli (2019), Lemma 6.9(i): local left-alpha propagation

The source-alpha propagation on a no-gap-two left outer interval only uses
parity relative to the first unequal order.  In particular, the first
unequal order need not be the first coordinate of the whole BONG.  This
local form is the input needed after reverse duality when the original pair
has a proper common suffix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every source alpha immediately before an even boundary of the left
outer interval is one.  Parity is measured from the actual first unequal
order, so the theorem applies to a proper subinterval of the BONG. -/
theorem lemma69_sourcePreviousAlpha_eq_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hcenter : a.alphaValue
      ⟨O.transition.lastZero, by
        have hbound := O.transition.firstTwo_le_rank
        have hseparated := O.transition.separated
        omega⟩ = 1)
    (i : Nat) (hiFirst : O.first + 2 ≤ i)
    (hiLeft : i ≤ O.transition.lastZero)
    (hiEven : Even (i - O.first)) :
    a.alphaValue ⟨i - 2, by
      have hbound := O.transition.firstTwo_le_rank
      have hseparated := O.transition.separated
      omega⟩ = 1 := by
  have htransitionBound := O.transition.firstTwo_le_rank
  have hseparated := O.transition.separated
  let left := O.transition.lastZero
  let center : Fin (n + 1) := ⟨left, by
    dsimp only [left]
    omega⟩
  let previous : Fin (n + 1) := ⟨i - 2, by
    omega⟩
  have hfirstLtLeft : O.first < left := by
    dsimp only [left]
    omega
  have hprofile := O.leftProfile hfirstLtLeft
  have hpreviousEven : Even ((i - 2) - O.first) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourcePrevious : a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero left := by
    have hsame := hprofile.2.2 (i - 2) (by omega) (by omega)
      hpreviousEven
    have hleftSame := hprofile.2.2 left O.first_le_left le_rfl
      hprofile.1
    exact hsame.trans hleftSame.symm
  have hsourceCenter : a.order previous.castSucc =
      a.order center.castSucc := by
    rw [← a.orderSequence_entryOrZero_eq_order previous.castSucc,
      ← a.orderSequence_entryOrZero_eq_order center.castSucc]
    change a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero left
    exact hsourcePrevious
  have hcentralOne : a.alphaValue center = 1 := by
    simpa only [center, left] using hcenter
  have halphaLe : a.alphaValue previous ≤ 1 := by
    have hmono := a.alphaLeftEndpoint_monotone
      (show previous ≤ center by
        change i - 2 ≤ left
        omega)
    unfold alphaLeftEndpoint at hmono
    rw [hsourceCenter, hcentralOne] at hmono
    linarith
  have htargetFirst : b.orderSequence.entryOrZero O.first =
      b.orderSequence.entryOrZero left := by
    have hsourceFirst := hprofile.2.2 left O.first_le_left le_rfl
      hprofile.1
    have hfirstStrict := hprofile.2.1
    have hfirstUpper := hnoTwo O.first O.firstDifference.bound
    have hboundary := O.transition.leftBoundary
    have hleftGap : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    omega
  have htargetPrevious : b.orderSequence.entryOrZero (i - 2) =
      b.orderSequence.entryOrZero left := by
    have hpreviousBound : i - 2 < n + 2 := by
      omega
    have hleftBound : left < n + 2 := by
      dsimp only [left]
      omega
    have hfirstPrevious := b.orderSequence.entryOrZero_le_of_evenGap
      O.first (i - 2) (by omega) hpreviousBound hpreviousEven
    have hpreviousLeftEven : Even (left - (i - 2)) := by
      rcases hprofile.1 with ⟨d, hd⟩
      rcases hpreviousEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hpreviousLeft := b.orderSequence.entryOrZero_le_of_evenGap
      (i - 2) left (by omega) hleftBound hpreviousLeftEven
    exact le_antisymm hpreviousLeft
      (htargetFirst.symm.trans_le hfirstPrevious)
  have hleftGap : b.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero (i - 2) + 1 := by
    have hboundary := O.transition.leftBoundary
    have hboundary' : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hboundary
    omega
  have hpair := O.leftPairEq (i - 2) (by omega) (by
    rcases hprofile.1 with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    exact ⟨d - e + 1, by omega⟩)
  have hrightGap : b.orderSequence.entryOrZero (i - 1) =
      a.orderSequence.entryOrZero (i - 1) - 1 := by
    have hnext : i - 2 + 1 = i - 1 := by omega
    rw [hnext] at hpair
    omega
  have htargetLower := b.orderGap_ge_neg_two_mul_e previous
  have hpreviousSuccVal : previous.succ.val = i - 1 := by
    dsimp only [previous]
    change i - 2 + 1 = i - 1
    omega
  have hpreviousCastVal : previous.castSucc.val = i - 2 := by
    rfl
  have hsourceGapStrict : -(2 * (ramificationIndex K : Int)) <
      a.orderGap previous := by
    unfold orderGap at htargetLower ⊢
    rw [← b.orderSequence_entryOrZero_eq_order previous.succ,
      ← b.orderSequence_entryOrZero_eq_order previous.castSucc]
      at htargetLower
    rw [← a.orderSequence_entryOrZero_eq_order previous.succ,
      ← a.orderSequence_entryOrZero_eq_order previous.castSucc]
    rw [hpreviousSuccVal, hpreviousCastVal] at htargetLower ⊢
    change -(2 * (ramificationIndex K : Int)) ≤
      b.orderSequence.entryOrZero (i - 1) -
        b.orderSequence.entryOrZero (i - 2) at htargetLower
    omega
  have halphaNe : a.alphaValue previous ≠ 0 := by
    intro hzero
    exact (ne_of_gt hsourceGapStrict) ((a.alpha_p2 previous).2.mp hzero)
  have halphaIntegral : IsRationalInteger (a.alphaValue previous) := by
    rcases a.beli2009Corollary28_iii previous with hsmall | hlarge
    · exact hsmall.2.2
    · have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        have hePos := ramificationIndex_pos (K := K)
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      exact (not_lt_of_ge (halphaLe.trans honeTwoE) hlarge.1).elim
  rcases halphaIntegral with ⟨z, hz⟩
  have hzNonnegative : (0 : Int) ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
      simpa only [← hz] using (a.alpha_p2 previous).1)
  have hzLe : z ≤ (1 : Int) := by
    exact_mod_cast (show (z : ℚ) ≤ 1 by
      simpa only [← hz] using halphaLe)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply halphaNe
    rw [hz, hzZero]
    norm_num
  have hzOne : z = 1 := by omega
  simpa only [previous] using (show a.alphaValue previous = 1 by
    rw [hz, hzOne]
    norm_num)

end BONG.GoodBONG

end Bong
