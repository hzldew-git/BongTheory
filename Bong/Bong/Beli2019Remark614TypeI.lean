/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeIII
import Bong.Bong.Beli2019Lemma69TypeIRightComplete

/-!
# Beli (2019), Remark 6.14: orders on the type-I right tail

The target orders from the canonical right switch through the last unequal
order are bounded below by their common even value.  At an odd position the
next target alpha is at most one.  Hence that order can be at most one below
its two equal even neighbors; the remaining one-unit drop would be an odd
negative good-BONG gap and is impossible by Lemma 2.7(iii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Remark 6.14 on the type-I target: every order on the canonical right
tail is at least the common even order at the anchor. -/
theorem beli2019Remark614_typeI_target_ge_anchor
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hright : C.rightSwitch ≤ k)
    (hlast : k ≤ D.profile.last) :
    b.orderSequence.entryOrZero D.anchor ≤
      b.orderSequence.entryOrZero k := by
  have hlastBound := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · have hkDistance : Even (k - D.anchor) := by
      rcases hkEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        omega⟩
    rw [C.target_from_anchor k
      (C.anchor_le_right.trans hright) hlast hkDistance]
  · have hrightLt : C.rightSwitch < k := by
      rcases C.right_even with ⟨d, hd⟩
      rcases hkOdd with ⟨e, he⟩
      omega
    have hkLast : k < D.profile.last := by
      have hlastDistance : Even (D.profile.last - D.anchor) :=
        (D.profile.rightProfile
          (C.anchor_le_right.trans_lt hrightLast)).1
      have hlastEven : Even D.profile.last := by
        rcases hlastDistance with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨e + d, by
          have hanchorLast := C.anchor_le_right.trans_lt hrightLast
          omega⟩
      rcases hlastEven with ⟨d, hd⟩
      rcases hkOdd with ⟨f, hf⟩
      omega
    have hpreviousDistance : Even (k - 1 - D.anchor) := by
      rcases hkOdd with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        omega⟩
    have hnextDistance : Even (k + 1 - D.anchor) := by
      rcases hkOdd with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e + 1, by
        have hanchorRight := C.anchor_le_right
        omega⟩
    have htargetPrevious := C.target_from_anchor (k - 1) (by
        have hanchorRight := C.anchor_le_right
        omega)
      (by omega) hpreviousDistance
    have htargetNext := C.target_from_anchor (k + 1) (by
        have hanchorRight := C.anchor_le_right
        omega)
      (by omega) hnextDistance
    let current : Fin (n + 1) := ⟨k, by omega⟩
    have halphaLe : b.alphaValue current ≤ 1 := by
      simpa only [current] using
        beli2019Lemma69_i_typeI_targetRightTail
          a b D C hfirst hrightLast hdefect k hrightLt hkLast hkOdd
    have hgapLe := b.orderGap_le_one_of_alphaValue_le_one current halphaLe
    have hcurrentCast : current.castSucc =
        (⟨k, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hcurrentSucc : current.succ =
        (⟨k + 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [current, Fin.val_succ]
    unfold orderGap at hgapLe
    rw [hcurrentCast, hcurrentSucc,
      ← b.orderSequence_entryOrZero_eq_order ⟨k, by omega⟩,
      ← b.orderSequence_entryOrZero_eq_order ⟨k + 1, by omega⟩]
      at hgapLe
    change b.orderSequence.entryOrZero (k + 1) -
      b.orderSequence.entryOrZero k ≤ 1 at hgapLe
    have hcurrentLower : b.orderSequence.entryOrZero D.anchor - 1 ≤
        b.orderSequence.entryOrZero k := by
      omega
    by_contra hnot
    have hcurrentEq : b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero D.anchor - 1 := by
      omega
    let previous : Fin (n + 1) := ⟨k - 1, by omega⟩
    have hpreviousCast : previous.castSucc =
        (⟨k - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hpreviousSucc : previous.succ =
        (⟨k, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [previous, Fin.val_succ]
      omega
    have hpreviousGap : b.orderGap previous = -1 := by
      unfold orderGap
      rw [hpreviousCast, hpreviousSucc,
        ← b.orderSequence_entryOrZero_eq_order ⟨k - 1, by omega⟩,
        ← b.orderSequence_entryOrZero_eq_order ⟨k, by omega⟩,
        htargetPrevious, hcurrentEq]
      omega
    have hpreviousGapOdd : Odd (b.orderGap previous) := by
      rw [hpreviousGap]
      exact ⟨-1, by omega⟩
    have hpreviousGapLe : b.orderGap previous ≤
        2 * (ramificationIndex K : Int) := by
      rw [hpreviousGap]
      have hePos := ramificationIndex_pos (K := K)
      omega
    have halphaEq :=
      (b.beli2009Lemma27_iii previous hpreviousGapLe).2.mpr
        (Or.inr hpreviousGapOdd)
    have halphaNonnegative := (b.alpha_p2 previous).1
    rw [halphaEq, hpreviousGap] at halphaNonnegative
    norm_num at halphaNonnegative

/-- On an odd coordinate immediately following an even right-tail position,
the source order is at least three above the first source order. -/
theorem beli2019Remark614_typeI_source_odd_ge_first_add_three
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hkEven : Even k) (hright : C.rightSwitch ≤ k)
    (hlast : k < D.profile.last) :
    a.orderSequence.entryOrZero 0 + 3 ≤
      a.orderSequence.entryOrZero (k + 1) := by
  have hnextOdd : Odd (k + 1) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnextLast : k + 1 < D.profile.last := by
    have hlastDistance : Even (D.profile.last - D.anchor) :=
      (D.profile.rightProfile
        (C.anchor_le_right.trans_lt hrightLast)).1
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hlastEven : Even D.profile.last := by
      rcases hlastDistance with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨e + d, by
        have hanchorLast := C.anchor_le_right.trans_lt hrightLast
        omega⟩
    rcases hlastEven with ⟨d, hd⟩
    rcases hkEven with ⟨f, hf⟩
    omega
  have htargetLower := beli2019Remark614_typeI_target_ge_anchor
    a b D C hfirst hrightLast hdefect (k + 1) (by omega) hnextLast.le
  have hsourceTarget := lemma69_typeI_rightOdd_orders
    a b D C hfirst (k + 1) (by omega) hnextLast hnextOdd
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hanchorGap := D.anchor_gap
  omega

end BONG.GoodBONG

end Bong
