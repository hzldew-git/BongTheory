/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIRightBoundary
import Bong.Bong.Beli2019Lemma79TypeIRightProfileAlpha

/-!
# Beli (2019), Lemma 7.9(iii): exclusions on the type-I right tail

The target alphas alternate between `1` and a value at most `2e - 1` on
the right tail.  Hence every adjacent alpha sum after the distinguished
right boundary is at most `2e`.  This localizes the first alternative of
Lemma 2.18 to case 3.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At every even target-alpha coordinate from the canonical right switch
through the difference tail, the target alpha is at most `2e - 1`.

At the switch the source two-step order rises by one and the two
source-target shifts total three.  Strictly after the switch the source
two-step orders agree and the shifts total two.  In either case the target
gap is at most `2e - 2`; the following odd target alpha is one. -/
theorem lemma79Central_typeIRight_evenAlpha_le_twoE_sub_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hright : C.rightSwitch ≤ k)
    (htwo : k + 2 ≤ D.profile.last) (hkEven : Even k) :
    b.alphaValue ⟨k, by
        have hbound := D.profile.lastDifference.bound
        omega⟩ ≤
      2 * (ramificationIndex K : ℚ) - 1 := by
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  have hlastBound := D.profile.lastDifference.bound
  have hkLarge : k < n + 2 := by omega
  have hkNextLarge : k + 1 < n + 2 := by omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨k + 1, by omega, hkNextLarge, hkNextLarge.le⟩
  have hnextOdd : Odd nextIdx.val := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hnextOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst (k + 1) (by omega) (by omega) (by
      simpa only [nextIdx] using hnextOdd)
  have hnextShift :
      a.orderSequence.entryOrZero (k + 1) =
        b.orderSequence.entryOrZero (k + 1) + 1 := hnextOrders.1
  have hsourceLower :=
    a.orderGap_ge_neg_two_mul_e ⟨k + 1, by omega⟩
  have hsourceGapUpper :
      a.orderSequence.entryOrZero (k + 1) -
          a.orderSequence.entryOrZero k ≤
        2 * (ramificationIndex K : Int) +
          (if k = C.rightSwitch then 1 else 0) := by
    unfold orderGap at hsourceLower
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order] at hsourceLower
    change -(2 * (ramificationIndex K : Int)) ≤
      a.orderSequence.entryOrZero (k + 2) -
        a.orderSequence.entryOrZero (k + 1) at hsourceLower
    by_cases hboundary : k = C.rightSwitch
    · have hskip := lemma69_v_typeI_rightSwitch_skip
        a b D C hfirst hrightLast
      rw [if_pos hboundary]
      rw [hboundary] at hsourceLower ⊢
      omega
    · have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
      have hkDistance : Even (k - D.anchor) := by
        rcases hkEven with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨d - e, by
          have hanchorRight := C.anchor_le_right
          omega⟩
      have hkTwoDistance : Even (k + 2 - D.anchor) := by
        rcases hkDistance with ⟨d, hd⟩
        exact ⟨d + 1, by
          have hanchorRight := C.anchor_le_right
          omega⟩
      have hsourceCurrent := C.source_after_right k (by omega)
        (by omega) hkDistance
      have hsourceFar := C.source_after_right (k + 2) (by omega)
        htwo hkTwoDistance
      rw [if_neg hboundary]
      omega
  have hcurrentShift :
      b.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero k +
          (if k = C.rightSwitch then 2 else 1) := by
    by_cases hboundary : k = C.rightSwitch
    · rw [if_pos hboundary, hboundary]
      exact lemma69_v_typeI_even_entry_gap_two
        a b D C hfirst C.rightSwitch C.right_even
          (C.left_le_anchor.trans C.anchor_le_right) le_rfl
    · rw [if_neg hboundary]
      let currentIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨k, by omega, hkLarge, hkLarge.le⟩
      have hraw := lemma79_typeI_caseSix_current_eq_source_add_one
        a b D C hfirst currentIdx (by
          simp only [currentIdx]
          omega) (by simp only [currentIdx]; omega) (by
          simpa only [currentIdx] using hkEven)
      simpa only [currentIdx] using hraw
  have htargetGapUpper :
      b.orderSequence.entryOrZero (k + 1) -
          b.orderSequence.entryOrZero k ≤
        2 * (ramificationIndex K : Int) - 2 := by
    by_cases hboundary : k = C.rightSwitch
    · rw [if_pos hboundary] at hsourceGapUpper hcurrentShift
      omega
    · rw [if_neg hboundary] at hsourceGapUpper hcurrentShift
      omega
  have hprofile := lemma79_typeI_right_target_twoStep_and_alpha
    a b D C hfirst nextIdx (by simp only [nextIdx]; omega)
      (by simp only [nextIdx]; omega) hnextOdd
  have hformula : b.alphaValue ⟨k, by omega⟩ =
      ((b.order ⟨k + 1, hkNextLarge⟩ -
        b.order ⟨k, hkLarge⟩ : Int) : ℚ) +
        b.alphaValue ⟨k + 1, by omega⟩ := by
    simpa only [nextIdx, show k + 1 - 1 = k by omega] using hprofile.2
  have hbetaOne : b.alphaValue ⟨k + 1, by omega⟩ = 1 :=
    beli2019Remark613_typeI_targetRightAlpha_eq_one
      a b D C hfirst hrightLast hdefect (k + 1)
        (by omega) (by omega) (by simpa only [nextIdx] using hnextOdd)
  have htargetGapUpper' :
      b.order ⟨k + 1, hkNextLarge⟩ - b.order ⟨k, hkLarge⟩ ≤
        2 * (ramificationIndex K : Int) - 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htargetGapUpper
  rw [hformula, hbetaOne]
  have htargetGapUpperQ :
      ((b.order ⟨k + 1, hkNextLarge⟩ -
        b.order ⟨k, hkLarge⟩ : Int) : ℚ) ≤
          2 * (ramificationIndex K : ℚ) - 2 := by
    exact_mod_cast htargetGapUpper'
  linarith

/-- Beyond the distinguished right boundary, the first adjacent target
alpha sum cannot exceed `2e`. -/
theorem lemma79Central_typeIRight_not_leftAlphaSum_of_not_boundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last)
    (hnotBoundary : i.val ≠ C.rightSwitch + 1) :
    ¬ 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := by
  intro hsum
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hpreviousOdd : Odd (i.val - 1) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hfarEven : Even (i.val - 2) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hfarTwo : i.val - 2 + 2 ≤ D.profile.last := by omega
    have hfarAlpha := lemma79Central_typeIRight_evenAlpha_le_twoE_sub_one
      a b D C hfirst hdefect (i.val - 2) (by omega) hfarTwo hfarEven
    have hpreviousOne := beli2019Remark613_typeI_targetRightAlpha_eq_one
      a b D C hfirst hrightLast hdefect (i.val - 1)
        (by omega) (by
          rcases hiEven with ⟨d, hd⟩
          rcases hlastEven with ⟨e, he⟩
          omega) hpreviousOdd
    rw [hpreviousOne] at hsum
    linarith
  · have hpreviousEven : Even (i.val - 1) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hfarOdd : Odd (i.val - 2) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hpreviousTwo : i.val - 1 + 2 ≤ D.profile.last := by
      rcases hiOdd with ⟨d, hd⟩
      rcases hlastEven with ⟨e, he⟩
      omega
    have hpreviousAlpha :=
      lemma79Central_typeIRight_evenAlpha_le_twoE_sub_one
        a b D C hfirst hdefect (i.val - 1) (by omega)
          hpreviousTwo hpreviousEven
    have hfarOne := beli2019Remark613_typeI_targetRightAlpha_eq_one
      a b D C hfirst hrightLast hdefect (i.val - 2)
        (by
          rcases C.right_even with ⟨d, hd⟩
          rcases hiOdd with ⟨e, he⟩
          omega) (by omega) hfarOdd
    rw [hfarOne] at hsum
    linarith

end BONG.GoodBONG

end Bong
