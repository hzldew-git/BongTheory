/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIFirstBoundary
import Bong.Bong.Beli2019Lemma69TypeIFromConditions

/-!
# Beli (2019), Lemma 6.9(v): the terminal type-I boundary

The missing terminal branch is obtained exactly as in the paper.  Reverse
duality turns the last unequal type-I coordinate into a first gap-two
coordinate for the swapped pair.  The local first-boundary theorem then
reflects to the required right-end comparison of the original `W`-block.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- After the first unequal coordinate is normalized to zero, the type-I
anchor has even parity. -/
theorem lemma69_v_typeI_anchor_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0) :
    Even D.anchor := by
  by_cases heq : D.profile.first = D.anchor
  · rw [← heq, hfirst]
    exact ⟨0, by omega⟩
  · have hlt : D.profile.first < D.anchor :=
      lt_of_le_of_ne D.profile.first_le_anchor heq
    simpa only [hfirst, Nat.sub_zero] using
      (D.profile.leftProfile hlt).1

set_option maxHeartbeats 5000000 in
-- Reverse-dual transport unfolds two dependent endpoint comparisons.
/-- When the right switch is the last unequal nonfinal coordinate, reverse
duality supplies the missing comparison of the right alpha endpoints. -/
theorem lemma69_v_typeI_terminal_rightEndpoint
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (hrightNonfinal : C.rightSwitch < n + 1)
    (hdefect : a.RepresentationDefectCondition b) :
    b.alphaRightEndpoint ⟨C.rightSwitch - 1, by omega⟩ ≤
      a.alphaRightEndpoint ⟨C.rightSwitch - 1, by omega⟩ := by
  have hanchorEven := lemma69_v_typeI_anchor_even a b D hfirst
  have hrightTwo : 2 ≤ C.rightSwitch := by
    rcases C.left_even with ⟨dl, hdl⟩
    rcases C.right_even with ⟨dr, hdr⟩
    omega
  have hrightBound : C.rightSwitch < n + 2 :=
    hrightNonfinal.trans (by omega)
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨dr, hdr⟩
    rcases hanchorEven with ⟨da, hda⟩
    exact ⟨dr - da, by omega⟩
  have hsourceRight := C.source_to_right C.rightSwitch
    C.anchor_le_right le_rfl hrightDistance
  have htargetRight := C.target_from_anchor C.rightSwitch
    C.anchor_le_right (by rw [hrightLast]) hrightDistance
  have hrightEntryGap :
      b.orderSequence.entryOrZero C.rightSwitch =
        a.orderSequence.entryOrZero C.rightSwitch + 2 := by
    have hanchorGap := D.anchor_gap
    omega
  have hpreviousEven : Even (C.rightSwitch - 2) := by
    rcases C.right_even with ⟨dr, hdr⟩
    exact ⟨dr - 1, by omega⟩
  have hleftPrevious : C.leftSwitch ≤ C.rightSwitch - 2 := by
    rcases C.left_even with ⟨dl, hdl⟩
    rcases C.right_even with ⟨dr, hdr⟩
    omega
  have htargetPrevious :
      b.orderSequence.entryOrZero (C.rightSwitch - 2) =
        a.orderSequence.entryOrZero D.anchor + 2 := by
    by_cases hbefore : C.rightSwitch - 2 ≤ D.anchor
    · exact C.target_from_left (C.rightSwitch - 2)
        hleftPrevious hbefore hpreviousEven
    · have hanchorPrevious : D.anchor ≤ C.rightSwitch - 2 := by
        omega
      have hpreviousDistance :
          Even (C.rightSwitch - 2 - D.anchor) := by
        rcases hpreviousEven with ⟨dp, hdp⟩
        rcases hanchorEven with ⟨da, hda⟩
        exact ⟨dp - da, by omega⟩
      have htarget := C.target_from_anchor (C.rightSwitch - 2)
        hanchorPrevious (by rw [← hrightLast]; omega)
        hpreviousDistance
      have hanchorGap := D.anchor_gap
      omega
  have hrightOrderGap :
      b.order ⟨C.rightSwitch, hrightBound⟩ =
        a.order ⟨C.rightSwitch, hrightBound⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hrightEntryGap
  have hfarOriginal :
      a.order ⟨C.rightSwitch, hrightBound⟩ <
        b.order ⟨C.rightSwitch - 2, by omega⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change a.orderSequence.entryOrZero C.rightSwitch <
      b.orderSequence.entryOrZero (C.rightSwitch - 2)
    omega
  rcases a.exists_reverseDualPair_with_representationDefectCondition b
      hdefect with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, _, hdefectDual⟩
  let originalIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.rightSwitch, by omega, hrightBound, by omega⟩
  let dualIdx : RepresentationIndex (n + 2) (n + 2) :=
    originalIdx.reverse
  have hdualInterior :
      1 < dualIdx.val ∧ dualIdx.val + 1 < n + 2 := by
    simp only [dualIdx, RepresentationIndex.reverse_val, originalIdx]
    omega
  have hdualPrefix : ∀ k, k < dualIdx.val - 1 →
      bDual.orderSequence.entryOrZero k =
        aDual.orderSequence.entryOrZero k := by
    intro k hk
    have hkBound : k < n + 2 := by
      have hdualBound := dualIdx.lt_large
      omega
    let kd : Fin (n + 2) := ⟨k, hkBound⟩
    have hafter : C.rightSwitch < (Fin.rev kd).val := by
      simp only [kd, Fin.rev, dualIdx, originalIdx,
        RepresentationIndex.reverse_val] at hk ⊢
      omega
    have horiginal := D.profile.lastDifference.after
      (Fin.rev kd).val (by
        rw [← hrightLast]
        exact hafter) (Fin.rev kd).isLt
    rw [a.orderSequence_entryOrZero_eq_order (Fin.rev kd),
      b.orderSequence_entryOrZero_eq_order (Fin.rev kd)] at horiginal
    rw [bDual.orderSequence_entryOrZero_eq_order kd,
      aDual.orderSequence_entryOrZero_eq_order kd,
      hbOrders kd, haOrders kd]
    exact congrArg Neg.neg horiginal.symm
  let dualGap : Fin (n + 2) :=
    ⟨dualIdx.val - 1, by omega⟩
  let dualFar : Fin (n + 2) :=
    ⟨dualIdx.val + 1, hdualInterior.2⟩
  let originalRight : Fin (n + 2) :=
    ⟨C.rightSwitch, hrightBound⟩
  let originalEarlier : Fin (n + 2) :=
    ⟨C.rightSwitch - 2, by omega⟩
  have hreverseGap : Fin.rev dualGap = originalRight := by
    apply Fin.ext
    simp only [dualGap, originalRight, Fin.rev, dualIdx, originalIdx,
      RepresentationIndex.reverse_val]
    omega
  have hreverseFar : Fin.rev dualFar = originalEarlier := by
    apply Fin.ext
    simp only [dualFar, originalEarlier, Fin.rev, dualIdx, originalIdx,
      RepresentationIndex.reverse_val]
    omega
  have hdualGap : aDual.order dualGap = bDual.order dualGap + 2 := by
    rw [haOrders dualGap, hbOrders dualGap, hreverseGap]
    simpa only [originalRight] using (show
      -a.order ⟨C.rightSwitch, hrightBound⟩ =
        -b.order ⟨C.rightSwitch, hrightBound⟩ + 2 by omega)
  have hdualFar : bDual.order dualFar < aDual.order dualGap := by
    rw [hbOrders dualFar, haOrders dualGap, hreverseFar, hreverseGap]
    simpa only [originalEarlier, originalRight] using (show
      -b.order ⟨C.rightSwitch - 2, by omega⟩ <
        -a.order ⟨C.rightSwitch, hrightBound⟩ by omega)
  have hdualWeight := bDual.lemma69_v_firstGapTwo_weight
    aDual hdefectDual dualIdx hdualInterior hdualPrefix (by
      simpa only [dualGap] using hdualGap) (by
        simpa only [dualFar, dualGap] using hdualFar)
  let dualAlpha : Fin (n + 1) :=
    ⟨dualIdx.val - 1, by omega⟩
  let originalPrevious : Fin (n + 1) :=
    ⟨C.rightSwitch - 1, by omega⟩
  have hdualEndpoint :
      bDual.alphaLeftEndpoint dualAlpha ≤
        aDual.alphaLeftEndpoint dualAlpha := by
    simpa only [dualAlpha] using hdualWeight
  have hreverseOrder : Fin.rev dualAlpha.castSucc = originalRight := by
    apply Fin.ext
    simp only [dualAlpha, originalRight, Fin.rev, Fin.val_castSucc,
      dualIdx, originalIdx, RepresentationIndex.reverse_val]
    omega
  have hreverseAlpha : Fin.rev dualAlpha = originalPrevious := by
    apply Fin.ext
    simp only [dualAlpha, originalPrevious, Fin.rev, dualIdx,
      originalIdx, RepresentationIndex.reverse_val]
    omega
  unfold alphaLeftEndpoint at hdualEndpoint
  rw [hbOrders dualAlpha.castSucc, haOrders dualAlpha.castSucc,
    hbAlpha dualAlpha, haAlpha dualAlpha,
    hreverseOrder, hreverseAlpha] at hdualEndpoint
  push_cast at hdualEndpoint
  have hpreviousSucc : originalPrevious.succ = originalRight := by
    apply Fin.ext
    simp only [originalPrevious, originalRight, Fin.val_succ]
    omega
  change b.alphaRightEndpoint originalPrevious ≤
    a.alphaRightEndpoint originalPrevious
  unfold alphaRightEndpoint
  rw [hpreviousSucc]
  simpa only [originalRight, originalPrevious] using hdualEndpoint

/-- The reflected endpoint inequality is the right boundary comparison for
the terminal type-I `W`-block. -/
theorem lemma69_v_typeI_terminal_rightBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hstrict : C.leftSwitch < C.rightSwitch)
    (hrightNonfinal : C.rightSwitch < n + 1)
    (hdefect : a.RepresentationDefectCondition b) :
    a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
      b.weightSequence.entryOrZero (2 * C.rightSwitch - 1) := by
  have hendpoint := a.lemma69_v_typeI_terminal_rightEndpoint
    b D C hfirst hrightLast hstrict hrightNonfinal hdefect
  let previous : Fin (n + 1) :=
    ⟨C.rightSwitch - 1, by omega⟩
  have hcoordBound : 2 * C.rightSwitch - 1 < 2 * (n + 1) := by
    omega
  rw [a.weightSequence.entryOrZero_of_lt hcoordBound,
    b.weightSequence.entryOrZero_of_lt hcoordBound]
  change a.weightSequence.value ⟨2 * C.rightSwitch - 1, hcoordBound⟩ ≤
    b.weightSequence.value ⟨2 * C.rightSwitch - 1, hcoordBound⟩
  have hcoord : (⟨2 * C.rightSwitch - 1, hcoordBound⟩ :
      Fin (2 * (n + 1))) = ⟨2 * previous.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only [previous]
    omega
  rw [hcoord, a.weightSequence_odd previous,
    b.weightSequence_odd previous]
  change b.alphaRightEndpoint previous ≤
    a.alphaRightEndpoint previous at hendpoint
  unfold alphaRightEndpoint at hendpoint
  linarith

/-- Lemma 6.9(v) for a terminal type-I interval.  The final-coordinate case
comes directly from the last-coordinate clause of `W(a) ≤ W(b)`; every
other terminal case uses the reflected boundary theorem above. -/
theorem beli2019Lemma69_v_typeI_of_rightSwitch_eq_last
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    a.alphaLeftEndpoint ⟨k, by
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ =
      b.alphaLeftEndpoint ⟨k, by
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ := by
  have hW := a.weightSequence_le_of_representationConditions
    b horder hdefect
  have hstrict : C.leftSwitch < C.rightSwitch :=
    hleft.trans_lt hright
  have hleftNeighbor : 0 < C.leftSwitch →
      b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
        a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
    intro hleftPos
    exact beli2019Lemma69_v_typeI_leftNeighbor
      a b D C hfirst hleftPos hdefect
  have hleftBoundary := lemma69_v_typeI_leftBoundary_of_previous
    a b D C hfirst hstrict hW hleftNeighbor
  have hrightBoundary :
      a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
        b.weightSequence.entryOrZero (2 * C.rightSwitch - 1) := by
    by_cases hfinal : C.rightSwitch = n + 1
    · exact lemma69_v_typeI_rightBoundary_of_next
        a b D C hfirst hstrict hW (by
          intro hnonfinal
          omega)
    · exact a.lemma69_v_typeI_terminal_rightBoundary
        b D C hfirst hrightLast hstrict (by
          have hrightBound :=
            C.right_le_last.trans_lt D.profile.lastDifference.bound
          omega) hdefect
  have hsum := lemma69_v_typeI_weightSegmentSum_eq a b D C hfirst
  exact beli2019Lemma69_v_typeI_of_interval a b D C hW
    hleftBoundary hrightBoundary hsum k hleft hright

/-- Complete type-I form of Lemma 6.9(v), dispatching automatically between
the nonterminal and terminal right boundaries. -/
theorem beli2019Lemma69_v_typeI_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    a.alphaLeftEndpoint ⟨k, by
        have hrightBound := C.right_le_last
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ =
      b.alphaLeftEndpoint ⟨k, by
        have hrightBound := C.right_le_last
        have hlastBound := D.profile.lastDifference.bound
        omega⟩ := by
  rcases C.right_le_last.lt_or_eq with hrightLast | hrightLast
  · exact a.beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
      b D C hfirst hrightLast horder hdefect k hleft hright
  · exact a.beli2019Lemma69_v_typeI_of_rightSwitch_eq_last
      b D C hfirst hrightLast horder hdefect k hleft hright

end BONG.GoodBONG

end Bong
