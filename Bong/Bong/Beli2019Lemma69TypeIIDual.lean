/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderConditionDual
import Bong.Bong.Beli2019Lemma67Classification

/-!
# Beli (2019): reverse duality for a type-II pair

The complementary prefix-gap transition is again type II after
reverse-dualizing and swapping the two lattices.  The construction keeps
the reflected transition coordinates explicit for later use in Lemma 6.9.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- Constructing the reflected profile transports several dependent indices.
/-- A type-II pair remains type II after reverse-dualizing and swapping its
source and target.  The first unequal order of the dual pair is the
reflection of the last unequal order of the original pair. -/
theorem exists_reverseDual_typeII_local
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1)) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
      (Ddual : Lemma67TypeII bDual aDual),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      bDual.RepresentationDefectCondition aDual ∧
      Ddual.outer.first = n - D.outer.last ∧
      Ddual.outer.transition.lastZero =
        n + 1 - D.outer.transition.firstTwo ∧
      Ddual.outer.transition.firstTwo =
        n + 1 - D.outer.transition.lastZero := by
  rcases a.exists_reverseDualPair_with_representationDefectCondition
      b hdefect with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha,
      hDefectDual, hconditionDual⟩
  have horderDual := a.representationOrderCondition_reverseDual_swap
    b aDual bDual haOrders hbOrders horder
  have htotalDual := a.totalOrderSum_reverseDual_swap
    b aDual bDual haOrders hbOrders htotal
  have hleDual :=
    (bDual.representationOrderCondition_iff aDual le_rfl).mp horderDual
  let leftDual := n + 1 - D.outer.transition.firstTwo
  let firstDual := n + 1 - D.outer.transition.lastZero
  have hfirstBound := D.outer.transition.firstTwo_le_rank
  have hleftLtFirst : leftDual < firstDual := by
    dsimp only [leftDual, firstDual]
    have hlt := D.outer.transition.lastZero_lt_firstTwo
    omega
  have hfirstDualBound : firstDual ≤ n + 1 := Nat.sub_le _ _
  have hleftGap : bDual.orderSequence.prefixGap
      aDual.orderSequence leftDual = 0 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal leftDual (Nat.sub_le _ _)
    have hcomplement : n + 1 - leftDual =
        D.outer.transition.firstTwo := by
      dsimp only [leftDual]
      omega
    rw [hcomplement, D.outer.transition.gap_firstTwo] at htransport
    omega
  have hfirstGap : bDual.orderSequence.prefixGap
      aDual.orderSequence firstDual = 2 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal firstDual hfirstDualBound
    have hcomplement : n + 1 - firstDual =
        D.outer.transition.lastZero := by
      dsimp only [firstDual]
      omega
    rw [hcomplement, D.outer.transition.gap_lastZero] at htransport
    omega
  have hbetween (k : Nat) (hleft : leftDual < k)
      (hfirst : k < firstDual) :
      bDual.orderSequence.prefixGap aDual.orderSequence k = 1 := by
    have htransport := a.orderPrefixGap_reverseDual_swap
      b aDual bDual haOrders hbOrders htotal k (by omega)
    have hcomplementLeft : D.outer.transition.lastZero < n + 1 - k := by
      dsimp only [leftDual, firstDual] at hleft hfirst
      omega
    have hcomplementRight : n + 1 - k <
        D.outer.transition.firstTwo := by
      dsimp only [leftDual, firstDual] at hleft hfirst
      omega
    rw [D.outer.transition.gap_between (n + 1 - k)
      hcomplementLeft hcomplementRight] at htransport
    omega
  have hseparated : leftDual + 1 < firstDual := by
    dsimp only [leftDual, firstDual]
    have hlong := D.long
    omega
  have hleftBoundary : aDual.orderSequence.entryOrZero leftDual =
      bDual.orderSequence.entryOrZero leftDual + 1 := by
    have hstep := bDual.orderSequence.prefixGap_succ
      aDual.orderSequence leftDual
    have hnext := hbetween (leftDual + 1) (by omega) hseparated
    rw [hnext, hleftGap] at hstep
    omega
  have hrightBoundary :
      aDual.orderSequence.entryOrZero (firstDual - 1) =
        bDual.orderSequence.entryOrZero (firstDual - 1) + 1 := by
    have hprevious : bDual.orderSequence.prefixGap
        aDual.orderSequence (firstDual - 1) = 1 := by
      apply hbetween (firstDual - 1)
      · omega
      · omega
    have hstep := bDual.orderSequence.prefixGap_succ
      aDual.orderSequence (firstDual - 1)
    have hindex : firstDual - 1 + 1 = firstDual := by omega
    rw [hindex, hfirstGap, hprevious] at hstep
    omega
  have hmiddle (k : Nat) (hleft : leftDual < k)
      (hfirst : k + 1 < firstDual) :
      bDual.orderSequence.entryOrZero k =
        aDual.orderSequence.entryOrZero k := by
    have hgap := hbetween k hleft (by omega)
    have hgapNext := hbetween (k + 1) (by omega) hfirst
    have hstep := bDual.orderSequence.prefixGap_succ
      aDual.orderSequence k
    rw [hgapNext, hgap] at hstep
    omega
  let Tdual : BeliOrderLE.PrefixGapTransitionConsequences
      bDual.orderSequence aDual.orderSequence := {
    lastZero := leftDual
    firstTwo := firstDual
    firstTwo_le_rank := hfirstDualBound
    lastZero_lt_firstTwo := hleftLtFirst
    gap_lastZero := hleftGap
    gap_firstTwo := hfirstGap
    gap_between := hbetween
    separated := hseparated
    leftBoundary := hleftBoundary
    rightBoundary := hrightBoundary
    middle := hmiddle }
  rcases hleDual.exists_noGapTwoOuterConsequences_of_transition
      htotalDual Tdual with ⟨Odual, htransition⟩
  have hnoTwoDual (k : Nat) (hk : k < n + 1) :
      aDual.orderSequence.entryOrZero k <
        bDual.orderSequence.entryOrZero k + 2 := by
    rw [BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence hk,
      BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence hk]
    have horiginal := D.no_gap_two
      (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).val
      (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (Fin.rev (⟨k, hk⟩ : Fin (n + 1))).isLt] at horiginal
    change b.order (Fin.rev ⟨k, hk⟩) <
      a.order (Fin.rev ⟨k, hk⟩) + 2 at horiginal
    change aDual.order ⟨k, hk⟩ < bDual.order ⟨k, hk⟩ + 2
    rw [haOrders, hbOrders]
    omega
  have hleftDualBound : leftDual < n + 1 := by
    dsimp only [leftDual]
    have hseparatedOriginal := D.outer.transition.separated
    omega
  have hrightDualBound : firstDual - 1 < n + 1 := by
    dsimp only [firstDual]
    omega
  let dualLeft : Fin (n + 1) := ⟨leftDual, hleftDualBound⟩
  let dualRight : Fin (n + 1) := ⟨firstDual - 1, hrightDualBound⟩
  have horiginalLeftBound : D.outer.transition.lastZero < n + 1 := by
    exact D.outer.transition.lastZero_lt_firstTwo.trans_le hfirstBound
  have horiginalRightBound :
      D.outer.transition.firstTwo - 1 < n + 1 := by omega
  let originalLeft : Fin (n + 1) :=
    ⟨D.outer.transition.lastZero, horiginalLeftBound⟩
  let originalRight : Fin (n + 1) :=
    ⟨D.outer.transition.firstTwo - 1, horiginalRightBound⟩
  have hreverseLeft : Fin.rev dualLeft = originalRight := by
    apply Fin.ext
    simp only [dualLeft, originalRight, Fin.rev, leftDual]
    omega
  have hreverseRight : Fin.rev dualRight = originalLeft := by
    apply Fin.ext
    simp only [dualRight, originalLeft, Fin.rev, firstDual]
    omega
  have horiginalSource : a.order originalRight = b.order originalLeft := by
    have h := D.right_source
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        originalRight.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        originalLeft.isLt] at h
    change a.order originalRight = b.order originalLeft at h
    exact h
  have horiginalBoundary : b.order originalLeft =
      a.order originalLeft + 1 := by
    have h := D.outer.transition.leftBoundary
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        originalLeft.isLt,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        originalLeft.isLt] at h
    change b.order originalLeft = a.order originalLeft + 1 at h
    exact h
  have hrightSourceDual :
      bDual.orderSequence.entryOrZero (firstDual - 1) =
        aDual.orderSequence.entryOrZero leftDual := by
    rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
        dualRight.isLt,
      BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
        dualLeft.isLt]
    change bDual.order dualRight = aDual.order dualLeft
    rw [hbOrders dualRight, haOrders dualLeft,
      hreverseRight, hreverseLeft]
    omega
  have hrightTargetDual :
      aDual.orderSequence.entryOrZero (firstDual - 1) =
        aDual.orderSequence.entryOrZero leftDual + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
        dualRight.isLt,
      BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
        dualLeft.isLt]
    change aDual.order dualRight = aDual.order dualLeft + 1
    rw [haOrders dualRight, haOrders dualLeft,
      hreverseRight, hreverseLeft]
    omega
  have hmiddleDual (k : Nat) (hleft : leftDual < k)
      (hfirst : k + 1 < firstDual) :
      bDual.orderSequence.entryOrZero k =
        aDual.orderSequence.entryOrZero leftDual := by
    have hkBound : k < n + 1 := by
      dsimp only [firstDual] at hfirst
      omega
    let dualCurrent : Fin (n + 1) := ⟨k, hkBound⟩
    let originalCurrent : Fin (n + 1) := Fin.rev dualCurrent
    have hcurrentLeft : D.outer.transition.lastZero <
        originalCurrent.val := by
      simp only [originalCurrent, dualCurrent, Fin.rev]
      dsimp only [firstDual] at hfirst
      omega
    have hcurrentRight : originalCurrent.val + 1 <
        D.outer.transition.firstTwo := by
      simp only [originalCurrent, dualCurrent, Fin.rev]
      dsimp only [leftDual] at hleft
      omega
    have hsourceMiddle := D.middle originalCurrent.val
      hcurrentLeft hcurrentRight
    have hcommonMiddle := D.outer.transition.middle originalCurrent.val
      hcurrentLeft hcurrentRight
    have htargetCurrent : b.order originalCurrent =
        b.order originalLeft := by
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          originalCurrent.isLt,
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          originalLeft.isLt] at hsourceMiddle
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          originalCurrent.isLt,
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          originalCurrent.isLt] at hcommonMiddle
      change a.order originalCurrent = b.order originalLeft at hsourceMiddle
      change a.order originalCurrent = b.order originalCurrent at hcommonMiddle
      omega
    rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
        dualCurrent.isLt,
      BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
        dualLeft.isLt]
    change bDual.order dualCurrent = aDual.order dualLeft
    rw [hbOrders dualCurrent, haOrders dualLeft, hreverseLeft]
    change -b.order originalCurrent = -a.order originalRight
    omega
  let Ddual : Lemma67TypeII bDual aDual := {
    outer := Odual
    no_gap_two := hnoTwoDual
    long := by
      rw [htransition]
      dsimp only [Tdual, leftDual, firstDual]
      have hlong := D.long
      omega
    middle := by
      intro k hleft hfirst
      rw [htransition] at hleft hfirst ⊢
      exact hmiddleDual k hleft hfirst
    right_source := by
      rw [htransition]
      exact hrightSourceDual
    right_target := by
      rw [htransition]
      exact hrightTargetDual }
  have hdualFirst : Ddual.outer.first = n - D.outer.last := by
    let reflectedLast := n - D.outer.last
    have hlastBound := D.outer.lastDifference.bound
    have hreflectedBound : reflectedLast < n + 1 := by
      simp only [reflectedLast]
      omega
    let reflected : Fin (n + 1) := ⟨reflectedLast, hreflectedBound⟩
    let originalLast : Fin (n + 1) := ⟨D.outer.last, hlastBound⟩
    have hreverseReflected : Fin.rev reflected = originalLast := by
      apply Fin.ext
      simp only [reflected, reflectedLast, originalLast, Fin.rev]
      omega
    have hreflectedNe :
        bDual.orderSequence.entryOrZero reflectedLast ≠
          aDual.orderSequence.entryOrZero reflectedLast := by
      rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
          hreflectedBound,
        BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
          hreflectedBound]
      change bDual.order reflected ≠ aDual.order reflected
      rw [hbOrders reflected, haOrders reflected, hreverseReflected]
      intro heq
      apply D.outer.lastDifference.ne
      rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hlastBound,
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence hlastBound]
      change a.order originalLast = b.order originalLast
      exact neg_injective heq.symm
    have hfirstLe : Ddual.outer.first ≤ reflectedLast := by
      by_contra hnot
      have hreflectedBefore : reflectedLast < Ddual.outer.first := by omega
      exact hreflectedNe
        (Ddual.outer.firstDifference.before reflectedLast hreflectedBefore)
    have hreflectedLe : reflectedLast ≤ Ddual.outer.first := by
      by_contra hnot
      have hfirstBefore : Ddual.outer.first < reflectedLast := by omega
      have hfirstBound := Ddual.outer.firstDifference.bound
      let dualFirst : Fin (n + 1) :=
        ⟨Ddual.outer.first, hfirstBound⟩
      have horiginalAfter : D.outer.last < (Fin.rev dualFirst).val := by
        simp only [dualFirst, Fin.rev, reflectedLast] at hfirstBefore ⊢
        omega
      have horiginalEq := D.outer.lastDifference.after
        (Fin.rev dualFirst).val horiginalAfter (Fin.rev dualFirst).isLt
      have hdualEq :
          bDual.orderSequence.entryOrZero Ddual.outer.first =
            aDual.orderSequence.entryOrZero Ddual.outer.first := by
        rw [BeliOrderSequence.entryOrZero_of_lt bDual.orderSequence
            hfirstBound,
          BeliOrderSequence.entryOrZero_of_lt aDual.orderSequence
            hfirstBound]
        change bDual.order dualFirst = aDual.order dualFirst
        rw [hbOrders dualFirst, haOrders dualFirst]
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (Fin.rev dualFirst).isLt,
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (Fin.rev dualFirst).isLt] at horiginalEq
        change a.order (Fin.rev dualFirst) =
          b.order (Fin.rev dualFirst) at horiginalEq
        rw [horiginalEq]
      exact Ddual.outer.firstDifference.ne hdualEq
    exact le_antisymm hfirstLe hreflectedLe
  have hdualLeft : Ddual.outer.transition.lastZero = leftDual := by
    change Odual.transition.lastZero = leftDual
    rw [htransition]
  have hdualRight : Ddual.outer.transition.firstTwo = firstDual := by
    change Odual.transition.firstTwo = firstDual
    rw [htransition]
  exact ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
    hDefectDual, hconditionDual, hdualFirst, by
      simpa only [leftDual] using hdualLeft, by
      simpa only [firstDual] using hdualRight⟩

/-- Compatibility wrapper for the Section 7 normalization in which the
last unequal order is the last coordinate. -/
theorem exists_reverseDual_typeII
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hlast : D.outer.last = n) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
      (Ddual : Lemma67TypeII bDual aDual),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      bDual.RepresentationDefectCondition aDual ∧
      Ddual.outer.first = 0 ∧
      Ddual.outer.transition.lastZero =
        n + 1 - D.outer.transition.firstTwo ∧
      Ddual.outer.transition.firstTwo =
        n + 1 - D.outer.transition.lastZero := by
  rcases a.exists_reverseDual_typeII_local b D horder hdefect htotal with
    ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
      hDefectDual, hconditionDual, hdualFirst, hdualLeft, hdualRight⟩
  have hdualFirstZero : Ddual.outer.first = 0 := by
    rw [hdualFirst, hlast]
    omega
  exact ⟨aDual, bDual, Ddual, haOrders, hbOrders, haAlpha, hbAlpha,
    hDefectDual, hconditionDual, hdualFirstZero, hdualLeft, hdualRight⟩

end BONG.GoodBONG

end Bong
