/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeINeighbor

/-!
# Beli (2019), Lemma 6.9(v): the right neighboring coordinate

This is the right-hand counterpart of the preceding module.  When the
canonical right switch precedes the last unequal order, the target alpha one
place after the switch is one.  Corollary 2.3 then identifies the following
target `W`-coordinate with the intervening source order, and Corollary 2.9
bounds that order by the source coordinate plus one half.
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

/-- A gap no larger than `2e + 1` puts the next order at most one half
above the corresponding even `W`-coordinate. -/
theorem nextOrder_le_evenWeightCoordinate_add_half
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hupper : b.orderGap i ≤ 2 * (ramificationIndex K : Int) + 1) :
    (b.order i.succ : ℚ) ≤
      (b.order i.castSucc : ℚ) + b.alphaValue i + 1 / 2 := by
  have hgapCast : (b.orderGap i : ℚ) =
      (b.order i.succ : ℚ) - b.order i.castSucc := by
    unfold orderGap
    push_cast
    rfl
  by_cases hle : b.orderGap i ≤ 2 * (ramificationIndex K : Int)
  · have halphaLower := (b.beli2009Lemma27_iii i hle).1
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

/-- A strict right tail in the canonical type-I profile contains at least
two further indices, because both endpoints have the anchor parity. -/
theorem lemma69_typeI_rightSwitch_add_two_le_last
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last) :
    C.rightSwitch + 2 ≤ D.profile.last := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    have hanchorLast : D.anchor < D.profile.last :=
      C.anchor_le_right.trans_lt hrightLast
    exact (D.profile.rightProfile hanchorLast).1
  have hrightLastEven : Even (D.profile.last - C.rightSwitch) := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hrightDistance with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  rcases hrightLastEven with ⟨d, hd⟩
  omega

/-- At a nonterminal canonical right switch, the source order two places
later is the source order at the switch plus one. -/
theorem lemma69_v_typeI_rightSwitch_skip
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last) :
    a.orderSequence.entryOrZero (C.rightSwitch + 2) =
      a.orderSequence.entryOrZero C.rightSwitch + 1 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hnextDistance : Even (C.rightSwitch + 2 - D.anchor) := by
    rcases hrightDistance with ⟨d, hd⟩
    exact ⟨d + 1, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hcurrent := C.source_to_right C.rightSwitch C.anchor_le_right
    le_rfl hrightDistance
  have hnext := C.source_after_right (C.rightSwitch + 2) (by omega)
    hrightTwo hnextDistance
  omega

/-- One place after the canonical right switch, the source order is the
target order plus one. -/
theorem lemma69_v_typeI_next_source_target_order
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last) :
    a.orderSequence.entryOrZero (C.rightSwitch + 1) =
      b.orderSequence.entryOrZero (C.rightSwitch + 1) + 1 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hnextDistance : Even (C.rightSwitch + 2 - D.anchor) := by
    rcases hrightDistance with ⟨d, hd⟩
    exact ⟨d + 1, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hpair := D.profile.rightPairEq (C.rightSwitch + 1) (by
      have hanchorRight := C.anchor_le_right
      omega)
    (by
      have hlastBound := D.profile.lastDifference.bound
      omega) (by
        simpa only [Nat.add_sub_add_right] using hrightDistance)
  have haNext := C.source_after_right (C.rightSwitch + 2) (by omega)
    hrightTwo hnextDistance
  have hbNext := C.target_from_anchor (C.rightSwitch + 2) (by
      have hanchorRight := C.anchor_le_right
      omega)
    hrightTwo hnextDistance
  have hgapAnchor := D.anchor_gap
  rw [show C.rightSwitch + 1 + 1 = C.rightSwitch + 2 by omega] at hpair
  omega

/-- The target alpha immediately after the right switch is exactly one once
the corresponding `alpha ≤ 1` part of Lemma 6.9(i) is supplied. -/
theorem lemma69_v_typeI_nextTargetAlpha_eq_one_of_le_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (halphaLe : b.alphaValue ⟨C.rightSwitch + 1, by
      have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
        a b D C hfirst hrightLast
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1) :
    b.alphaValue ⟨C.rightSwitch + 1, by
      have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
        a b D C hfirst hrightLast
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ = 1 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    have hanchorLast : D.anchor < D.profile.last :=
      C.anchor_le_right.trans_lt hrightLast
    exact (D.profile.rightProfile hanchorLast).1
  have hrightLastEven : Even (D.profile.last - C.rightSwitch) := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hrightDistance with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hnextDistance : Even (C.rightSwitch + 2 - D.anchor) := by
    rcases hrightDistance with ⟨d, hd⟩
    exact ⟨d + 1, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  let next : Fin (n + 1) := ⟨C.rightSwitch + 1, by
    have hlastBound := D.profile.lastDifference.bound
    omega⟩
  have hsourceTarget := lemma69_v_typeI_next_source_target_order
    a b D C hfirst hrightLast
  have haAfter := C.source_after_right (C.rightSwitch + 2) (by omega)
    hrightTwo hnextDistance
  have hbAfter := C.target_from_anchor (C.rightSwitch + 2) (by
      have hanchorRight := C.anchor_le_right
      omega)
    hrightTwo hnextDistance
  have hgapAnchor := D.anchor_gap
  have hsourceLower := a.orderGap_ge_neg_two_mul_e next
  have htargetGapStrict :
      -(2 * (ramificationIndex K : Int)) < b.orderGap next := by
    unfold orderGap at hsourceLower ⊢
    have hsourceTarget' :
        a.order next.castSucc = b.order next.castSucc + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order next.castSucc,
        ← b.orderSequence_entryOrZero_eq_order next.castSucc]
      change a.orderSequence.entryOrZero (C.rightSwitch + 1) =
        b.orderSequence.entryOrZero (C.rightSwitch + 1) + 1
      exact hsourceTarget
    have haAfter' : a.order next.succ =
        a.orderSequence.entryOrZero D.anchor + 1 := by
      rw [show next.succ =
        (⟨C.rightSwitch + 2, by
          have hlastBound := D.profile.lastDifference.bound
          omega⟩ : Fin (n + 2)) by
            apply Fin.ext
            simp only [next, Fin.val_succ],
        ← a.orderSequence_entryOrZero_eq_order]
      exact haAfter
    have hbAfter' : b.order next.succ =
        a.orderSequence.entryOrZero D.anchor + 2 := by
      rw [show next.succ =
        (⟨C.rightSwitch + 2, by
          have hlastBound := D.profile.lastDifference.bound
          omega⟩ : Fin (n + 2)) by
            apply Fin.ext
            simp only [next, Fin.val_succ],
        ← b.orderSequence_entryOrZero_eq_order]
      exact hbAfter.trans hgapAnchor
    omega
  have halphaNe : b.alphaValue next ≠ 0 := by
    intro hzero
    have hgap := (b.alpha_p2 next).2.mp hzero
    exact (ne_of_gt htargetGapStrict) hgap
  have halphaNonnegative := (b.alpha_p2 next).1
  have halphaIntegral : IsRationalInteger (b.alphaValue next) := by
    rcases b.beli2009Corollary28_iii next with hsmall | hlarge
    · exact hsmall.2.2
    · have honeTwoE : (1 : ℚ) ≤ 2 * (ramificationIndex K : ℚ) := by
        have hePos := ramificationIndex_pos (K := K)
        exact_mod_cast (show (1 : Int) ≤
          2 * (ramificationIndex K : Int) by omega)
      have hleTwoE : b.alphaValue next ≤
          2 * (ramificationIndex K : ℚ) := by
        have halphaLe' : b.alphaValue next ≤ 1 := by
          simpa only [next] using halphaLe
        exact halphaLe'.trans honeTwoE
      exact (not_lt_of_ge hleTwoE hlarge.1).elim
  rcases halphaIntegral with ⟨z, hz⟩
  have hzNonnegative : (0 : Int) ≤ z := by
    exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
      simpa only [← hz] using halphaNonnegative)
  have hzLe : z ≤ (1 : Int) := by
    exact_mod_cast (show (z : ℚ) ≤ 1 by
      simpa only [next, ← hz] using halphaLe)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply halphaNe
    rw [hz, hzZero]
    norm_num
  have hzOne : z = 1 := by omega
  rw [hz, hzOne]
  norm_num

/-- The right neighboring-coordinate estimate in Lemma 6.9(v), reduced to
the right-tail `alpha ≤ 1` assertion from Lemma 6.9(i). -/
theorem lemma69_v_typeI_rightNeighbor_of_nextAlpha_le_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (halphaLe : b.alphaValue ⟨C.rightSwitch + 1, by
      have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
        a b D C hfirst hrightLast
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1) :
    b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
      a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    have hanchorLast : D.anchor < D.profile.last :=
      C.anchor_le_right.trans_lt hrightLast
    exact (D.profile.rightProfile hanchorLast).1
  have hrightLastEven : Even (D.profile.last - C.rightSwitch) := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hrightDistance with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightTwo := lemma69_typeI_rightSwitch_add_two_le_last
    a b D C hfirst hrightLast
  have hrightBound : C.rightSwitch < n + 1 := by
    have hlastBound := D.profile.lastDifference.bound
    omega
  let current : Fin (n + 1) := ⟨C.rightSwitch, hrightBound⟩
  let next : Fin (n + 1) := ⟨C.rightSwitch + 1, by
    have hlastBound := D.profile.lastDifference.bound
    omega⟩
  have hcurrentSucc : current.succ =
      (⟨C.rightSwitch + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
  have hcurrentCast : current.castSucc =
      (⟨C.rightSwitch, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnextSucc : next.succ =
      (⟨C.rightSwitch + 2, by
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [next, Fin.val_succ]
  have hnextCast : next.castSucc =
      (⟨C.rightSwitch + 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have halphaOne := lemma69_v_typeI_nextTargetAlpha_eq_one_of_le_one
    a b D C hfirst hrightLast halphaLe
  have hbCurrent := C.target_from_anchor C.rightSwitch C.anchor_le_right
    C.right_le_last hrightDistance
  have hnextDistance : Even (C.rightSwitch + 2 - D.anchor) := by
    rcases hrightDistance with ⟨d, hd⟩
    exact ⟨d + 1, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hbAfter := C.target_from_anchor (C.rightSwitch + 2) (by
      have hanchorRight := C.anchor_le_right
      omega)
    hrightTwo hnextDistance
  have htargetSum : b.adjacentOrderSum current =
      b.adjacentOrderSum next := by
    unfold adjacentOrderSum
    rw [hcurrentSucc, hcurrentCast, hnextSucc, hnextCast,
      ← b.orderSequence_entryOrZero_eq_order
        ⟨C.rightSwitch, by omega⟩,
      ← b.orderSequence_entryOrZero_eq_order
        ⟨C.rightSwitch + 2, by
          have hlastBound := D.profile.lastDifference.bound
          omega⟩]
    rw [hbCurrent, hbAfter]
    omega
  have hconstant := b.beli2009Corollary23 current next (by
      change C.rightSwitch ≤ C.rightSwitch + 1
      omega) htargetSum
  have hleftEndpoint := hconstant.leftEndpoint_eq next (by
      change C.rightSwitch ≤ C.rightSwitch + 1
      omega) le_rfl
  have hsourceTarget := lemma69_v_typeI_next_source_target_order
    a b D C hfirst hrightLast
  have htargetCoordinate :
      b.weightSequence.entryOrZero (2 * C.rightSwitch) =
        (a.order next.castSucc : ℚ) := by
    have hcoordBound : 2 * C.rightSwitch < 2 * (n + 1) := by omega
    rw [BeliOrderSequence.entryOrZero_of_lt b.weightSequence hcoordBound]
    change b.weightSequence.value ⟨2 * C.rightSwitch, hcoordBound⟩ = _
    have hvalue := b.weightSequence_even current
    rw [show (⟨2 * C.rightSwitch, hcoordBound⟩ : Fin (2 * (n + 1))) =
        ⟨2 * current.1, by omega⟩ by
          apply Fin.ext
          rfl, hvalue]
    unfold alphaLeftEndpoint at hleftEndpoint
    have halphaOne' : b.alphaValue next = 1 := by
      simpa only [next] using halphaOne
    rw [halphaOne'] at hleftEndpoint
    have hsourceTargetQ : (a.order next.castSucc : ℚ) =
        (b.order next.castSucc : ℚ) + 1 := by
      exact_mod_cast (show a.order next.castSucc =
        b.order next.castSucc + 1 by
          rw [← a.orderSequence_entryOrZero_eq_order next.castSucc,
            ← b.orderSequence_entryOrZero_eq_order next.castSucc]
          change a.orderSequence.entryOrZero (C.rightSwitch + 1) =
            b.orderSequence.entryOrZero (C.rightSwitch + 1) + 1
          exact hsourceTarget)
    linarith
  have hskip := lemma69_v_typeI_rightSwitch_skip
    a b D C hfirst hrightLast
  have hnextLower := a.orderGap_ge_neg_two_mul_e next
  have hgapUpper : a.orderGap current ≤
      2 * (ramificationIndex K : Int) + 1 := by
    unfold orderGap at hnextLower ⊢
    rw [hnextSucc, hnextCast] at hnextLower
    rw [hcurrentSucc, hcurrentCast]
    have hskip' : a.order ⟨C.rightSwitch + 2, by
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ =
      a.order ⟨C.rightSwitch, by omega⟩ + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order]
      exact hskip
    omega
  have hsourceBound :=
    nextOrder_le_evenWeightCoordinate_add_half a current hgapUpper
  have hcoordBound : 2 * C.rightSwitch < 2 * (n + 1) := by omega
  rw [htargetCoordinate]
  rw [BeliOrderSequence.entryOrZero_of_lt a.weightSequence hcoordBound]
  change (a.order next.castSucc : ℚ) ≤
    a.weightSequence.value ⟨2 * C.rightSwitch, hcoordBound⟩ + 1 / 2
  have hvalue := a.weightSequence_even current
  rw [show (⟨2 * C.rightSwitch, hcoordBound⟩ : Fin (2 * (n + 1))) =
      ⟨2 * current.1, by omega⟩ by
        apply Fin.ext
        rfl, hvalue]
  exact hsourceBound

end BONG.GoodBONG

end Bong
