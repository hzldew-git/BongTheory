/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.Beli2019Lemma69TypeIBoundary
import Bong.Bong.Beli2019Lemma76TypeI

/-!
# Beli (2019), Lemma 6.9(v): the left neighboring coordinate

For a positive canonical type-I switch, the order immediately before the
switch drops by one from source to target.  Corollary 2.3 identifies the
preceding source `W`-coordinate with that target order once the previous
source alpha equals one.  The odd target gap is at most `2e + 1`, so the
arithmetic of Corollary 2.9 bounds the target coordinate by one half more.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

/-- An odd adjacent gap no larger than `2e + 1` makes its odd `W`-coordinate
at most one half larger than the current order. -/
theorem oddWeightCoordinate_le_currentOrder_add_half
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hodd : Odd (b.orderGap i))
    (hupper : b.orderGap i ≤ 2 * (ramificationIndex K : Int) + 1) :
    (b.order i.succ : ℚ) - b.alphaValue i ≤
      (b.order i.castSucc : ℚ) + 1 / 2 := by
  have hgapCast : (b.orderGap i : ℚ) =
      (b.order i.succ : ℚ) - b.order i.castSucc := by
    unfold orderGap
    push_cast
    rfl
  by_cases hle : b.orderGap i ≤ 2 * (ramificationIndex K : Int)
  · have halpha := (b.beli2009Lemma27_iii i hle).2.mpr (Or.inr hodd)
    rw [halpha]
    linarith
  · have hgt : 2 * (ramificationIndex K : Int) < b.orderGap i :=
      lt_of_not_ge hle
    have hgapEq : b.orderGap i =
        2 * (ramificationIndex K : Int) + 1 := by
      omega
    have hgapEqQ : (b.orderGap i : ℚ) =
        2 * (ramificationIndex K : ℚ) + 1 := by
      exact_mod_cast hgapEq
    rw [b.beli2009Lemma27_ii i hgt.le]
    unfold halfGapValue
    linarith

/-- Immediately before a positive canonical type-I switch, the target order
is the source order minus one. -/
theorem lemma69_v_typeI_previous_target_order
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch) :
    b.order ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ =
      a.order ⟨C.leftSwitch - 1, by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega⟩ - 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hpreviousEven : Even (C.leftSwitch - 2) := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hsourcePrevious := C.source_to_anchor
    (C.leftSwitch - 2)
      ((Nat.sub_le C.leftSwitch 2).trans C.left_le_anchor) hpreviousEven
  have htargetPrevious := C.target_before_left
    (C.leftSwitch - 2) (by omega) hpreviousEven
  have hpairParity : Even (D.anchor - (C.leftSwitch - 2)) := by
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    rcases hanchorEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    exact ⟨d - e + 1, by
      have hleftAnchor := C.left_le_anchor
      omega⟩
  have hpair := D.profile.leftPairEq (C.leftSwitch - 2) (by
      simpa only [Nat.sub_add_cancel hleftTwo] using C.left_le_anchor)
    hpairParity
  rw [show C.leftSwitch - 2 + 1 = C.leftSwitch - 1 by omega] at hpair
  have hentry : b.orderSequence.entryOrZero (C.leftSwitch - 1) =
      a.orderSequence.entryOrZero (C.leftSwitch - 1) - 1 := by
    omega
  rw [← b.orderSequence_entryOrZero_eq_order
      ⟨C.leftSwitch - 1, by omega⟩,
    ← a.orderSequence_entryOrZero_eq_order
      ⟨C.leftSwitch - 1, by omega⟩]
  exact hentry

/-- The previous source alpha is exactly one once the `alpha ≤ 1` part of
Lemma 6.9(i) is available. -/
theorem lemma69_v_typeI_previousAlpha_eq_one_of_le_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (halphaLe : a.alphaValue ⟨C.leftSwitch - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1) :
    a.alphaValue ⟨C.leftSwitch - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ = 1 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by
    have hbound := C.left_le_anchor.trans_lt D.anchor_bound
    omega⟩
  have hpreviousSucc : previous.succ =
      (⟨C.leftSwitch - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨C.leftSwitch - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htargetOrder := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have htargetLower := b.orderGap_ge_neg_two_mul_e previous
  have hsourceGapStrict :
      -(2 * (ramificationIndex K : Int)) < a.orderGap previous := by
    unfold orderGap at htargetLower ⊢
    rw [hpreviousSucc, hpreviousCast] at htargetLower ⊢
    have hsourcePrevious := C.source_to_anchor
      (C.leftSwitch - 2)
        ((Nat.sub_le C.leftSwitch 2).trans C.left_le_anchor) (by
        rcases C.left_even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩)
    have htargetPrevious := C.target_before_left
      (C.leftSwitch - 2) (by omega) (by
        rcases C.left_even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩)
    have htargetOrder' : b.order ⟨C.leftSwitch - 1, by omega⟩ =
        a.order ⟨C.leftSwitch - 1, by omega⟩ - 1 := by
      simpa only using htargetOrder
    rw [← b.orderSequence_entryOrZero_eq_order
      ⟨C.leftSwitch - 2, by omega⟩] at htargetLower
    rw [← a.orderSequence_entryOrZero_eq_order
      ⟨C.leftSwitch - 2, by omega⟩]
    change -(2 * (ramificationIndex K : Int)) ≤
      b.order ⟨C.leftSwitch - 1, by omega⟩ -
        b.orderSequence.entryOrZero (C.leftSwitch - 2) at htargetLower
    change -(2 * (ramificationIndex K : Int)) <
      a.order ⟨C.leftSwitch - 1, by omega⟩ -
        a.orderSequence.entryOrZero (C.leftSwitch - 2)
    omega
  have halphaNe : a.alphaValue previous ≠ 0 := by
    intro hzero
    have hgap := (a.alpha_p2 previous).2.mp hzero
    exact (ne_of_gt hsourceGapStrict) hgap
  have halphaNonnegative := (a.alpha_p2 previous).1
  have halphaIntegral : IsRationalInteger (a.alphaValue previous) := by
    rcases a.beli2009Corollary28_iii previous with hsmall | hlarge
    · exact hsmall.2.2
    · have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        have hePos := ramificationIndex_pos (K := K)
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      have hleTwoE : a.alphaValue previous ≤
          2 * (ramificationIndex K : ℚ) := by
        have halphaLe' : a.alphaValue previous ≤ 1 := by
          simpa only [previous] using halphaLe
        exact halphaLe'.trans honeTwoE
      exact (not_lt_of_ge hleTwoE hlarge.1).elim
  rcases halphaIntegral with ⟨z, hz⟩
  have hzNonnegative : (0 : Int) ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
      simpa only [← hz] using halphaNonnegative)
  have hzLe : z ≤ (1 : Int) := by
    exact_mod_cast (show (z : ℚ) ≤ 1 by
      simpa only [previous, ← hz] using halphaLe)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply halphaNe
    rw [hz, hzZero]
    norm_num
  have hzOne : z = 1 := by omega
  rw [hz, hzOne]
  norm_num

/-- The left neighboring-coordinate estimate in Lemma 6.9(v), reduced only
to the already isolated `alpha ≤ 1` conclusion of Lemma 6.9(i). -/
theorem lemma69_v_typeI_leftNeighbor_of_previousAlpha_le_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (halphaLe : a.alphaValue ⟨C.leftSwitch - 2, by
      have hbound := C.left_le_anchor.trans_lt D.anchor_bound
      omega⟩ ≤ 1) :
    b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
      a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let previous : Fin (n + 1) := ⟨C.leftSwitch - 2, by omega⟩
  let middle : Fin (n + 1) := ⟨C.leftSwitch - 1, by omega⟩
  have hpreviousSucc : previous.succ =
      (⟨C.leftSwitch - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨C.leftSwitch - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hmiddleSucc : middle.succ =
      (⟨C.leftSwitch, hleftBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [middle, Fin.val_succ]
    omega
  have hmiddleCast : middle.castSucc =
      (⟨C.leftSwitch - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have halphaOne := lemma69_v_typeI_previousAlpha_eq_one_of_le_one
    a b D C hfirst hleftPos halphaLe
  have hsourceLeft := C.source_to_anchor C.leftSwitch
    C.left_le_anchor C.left_even
  have hsourcePrevious := C.source_to_anchor (C.leftSwitch - 2)
    ((Nat.sub_le C.leftSwitch 2).trans C.left_le_anchor) (by
      rcases C.left_even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩)
  have hsourceSum : a.adjacentOrderSum previous =
      a.adjacentOrderSum middle := by
    have hbridge : previous.succ = middle.castSucc := by
      rw [hpreviousSucc, hmiddleCast]
    have hendpoints : a.order previous.castSucc = a.order middle.succ := by
      rw [hpreviousCast, hmiddleSucc,
        ← a.orderSequence_entryOrZero_eq_order
          ⟨C.leftSwitch - 2, by omega⟩,
        ← a.orderSequence_entryOrZero_eq_order
          ⟨C.leftSwitch, hleftBound⟩]
      exact hsourcePrevious.trans hsourceLeft.symm
    unfold adjacentOrderSum
    rw [hbridge, hendpoints]
    exact add_comm _ _
  have hconstant := a.beli2009Corollary23 previous middle (by
      change C.leftSwitch - 2 ≤ C.leftSwitch - 1
      omega) hsourceSum
  have hrightEndpoint := hconstant.rightEndpoint_eq middle (by
      change C.leftSwitch - 2 ≤ C.leftSwitch - 1
      omega) le_rfl
  have hsourceWeight :
      (a.order middle.succ : ℚ) - a.alphaValue middle =
        (a.order previous.succ : ℚ) - 1 := by
    unfold alphaRightEndpoint at hrightEndpoint
    have halphaOne' : a.alphaValue previous = 1 := by
      simpa only [previous] using halphaOne
    rw [halphaOne'] at hrightEndpoint
    linarith
  have htargetOrder := lemma69_v_typeI_previous_target_order
    a b D C hfirst hleftPos
  have hsourceCoordinate :
      a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) =
        (b.order middle.castSucc : ℚ) := by
    have hcoordBound : 2 * C.leftSwitch - 1 < 2 * (n + 1) := by omega
    rw [BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound]
    change a.weightSequence.value ⟨2 * C.leftSwitch - 1, hcoordBound⟩ = _
    have hvalue := a.weightSequence_odd middle
    rw [show (⟨2 * C.leftSwitch - 1, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * middle.1 + 1, by
          have hmiddleBound := middle.isLt
          omega⟩ by
          apply Fin.ext
          simp only [middle]
          omega, hvalue]
    have htargetOrderQ : (b.order middle.castSucc : ℚ) =
        (a.order previous.succ : ℚ) - 1 := by
      have htargetOrder' : b.order middle.castSucc =
          a.order previous.succ - 1 := by
        rw [hmiddleCast, hpreviousSucc]
        exact htargetOrder
      exact_mod_cast htargetOrder'
    linarith
  have hgapOdd : Odd (b.orderGap middle) := by
    simpa only [middle] using
      lemma76_leftSwitch_gap_odd a b D C hfirst hleftPos
  have hskip := lemma76_leftSwitch_skip a b D C hleftPos
  have hgapLower := b.orderGap_ge_neg_two_mul_e previous
  have hgapUpper : b.orderGap middle ≤
      2 * (ramificationIndex K : Int) + 1 := by
    unfold orderGap at hgapLower ⊢
    rw [hpreviousSucc, hpreviousCast] at hgapLower
    rw [hmiddleSucc, hmiddleCast]
    have hskip' : b.order ⟨C.leftSwitch, by omega⟩ =
        b.order ⟨C.leftSwitch - 2, by omega⟩ + 1 := by
      simpa only using hskip
    omega
  have htargetCoordinate :=
    oddWeightCoordinate_le_currentOrder_add_half b middle hgapOdd hgapUpper
  have hcoordBound : 2 * C.leftSwitch - 1 < 2 * (n + 1) := by omega
  rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound]
  change b.weightSequence.value ⟨2 * C.leftSwitch - 1, hcoordBound⟩ ≤ _
  have hvalue := b.weightSequence_odd middle
  rw [show (⟨2 * C.leftSwitch - 1, hcoordBound⟩ : Fin (2 * (n + 1))) =
      ⟨2 * middle.1 + 1, by
        have hmiddleBound := middle.isLt
        omega⟩ by
        apply Fin.ext
        simp only [middle]
        omega, hvalue]
  rw [hsourceCoordinate]
  exact htargetCoordinate

end BONG.GoodBONG

end Bong
