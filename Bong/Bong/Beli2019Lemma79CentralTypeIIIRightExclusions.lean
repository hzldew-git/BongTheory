/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIRightExclusions

/-!
# Beli (2019), Lemma 7.9(iii): type-III right exclusions

Once the type-III target center alpha is one, Remark 6.13 gives every
odd-distance right alpha.  The common even-distance bound then excludes all
adjacent alpha sums in cases 3 and 9, except the terminal mixed-prefix case.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 2000000 in
-- Each branch carries proof-relevant finite indices for the alternating alpha profile.
/-- Every left adjacent target-alpha sum in the type-III right difference
region is at most `2e`. -/
theorem lemma79Central_typeIIIRight_not_leftAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hcenterOne : b.alphaValue ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last) :
    ¬ 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ +
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
  intro hsum
  have hbaseLe : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
  have hlastBound := D.outer.lastDifference.bound
  have hiOne := i.one_lt
  have hiLarge := i.lt_large
  have hiRecover := Nat.sub_add_cancel hbaseLe
  rcases Nat.even_or_odd
      (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
  · have hfarEven : Even
        ((i.val - 2) - (D.outer.transition.firstTwo - 1)) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hpreviousOdd : Odd
        ((i.val - 1) - (D.outer.transition.firstTwo - 1)) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hfarTwo : i.val - 2 + 2 ≤ D.outer.last := by omega
    have hpreviousRight : D.outer.transition.firstTwo ≤ i.val - 1 := by
      rcases hiEven with ⟨d, hd⟩
      omega
    have hpreviousBefore : i.val - 1 < D.outer.last := by omega
    have hpreviousOne :=
      a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
        b D horder hdefect htotal hcenterOne (i.val - 1) hpreviousRight
          hpreviousBefore hpreviousOdd
    have hfarRight : D.outer.transition.firstTwo - 1 ≤ i.val - 2 := by
      rcases hiEven with ⟨d, hd⟩
      omega
    have hfarAlpha := lemma79Central_outerRight_evenAlpha_le_twoE_sub_one
      a b D.outer (i.val - 2) hfarRight hfarTwo hfarEven (by
        rw [show (⟨i.val - 2 + 1, by omega⟩ : Fin (n + 1)) =
            ⟨i.val - 1, by omega⟩ by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega]
        exact hpreviousOne)
    rw [hpreviousOne] at hsum
    linarith
  · have hpreviousEven : Even
        ((i.val - 1) - (D.outer.transition.firstTwo - 1)) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hiSucc := lemma79Central_succ_le_of_odd_distance_of_even_endpoint
      (D.outer.transition.firstTwo - 1) i.val D.outer.last hbaseLe
        hthroughLast hiOdd D.outer.right_even_distance
    have hpreviousTwo : i.val - 1 + 2 ≤ D.outer.last := by omega
    have hcurrentBefore : i.val < D.outer.last := by omega
    have hcurrentOne :=
      a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
        b D horder hdefect htotal hcenterOne i.val hright hcurrentBefore hiOdd
    have hpreviousAlpha :=
      lemma79Central_outerRight_evenAlpha_le_twoE_sub_one
        a b D.outer (i.val - 1) (by omega) hpreviousTwo hpreviousEven (by
          rw [show (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
              ⟨i.val, by omega⟩ by
            apply Fin.ext
            simp only [Fin.val_mk]
            omega]
          exact hcurrentOne)
    by_cases hboundary : i.val = D.outer.transition.firstTwo
    · have hfarOne : b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ = 1 := by
        rw [show (⟨i.val - 2, by omega⟩ : Fin (n + 1)) =
            ⟨D.outer.transition.lastZero, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ by
          apply Fin.ext
          simp only [Fin.val_mk]
          rw [hboundary, D.adjacent]
          omega]
        exact hcenterOne
      rw [hfarOne] at hsum
      linarith
    · have hfarOdd : Odd
          ((i.val - 2) - (D.outer.transition.firstTwo - 1)) := by
        rcases hiOdd with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have hfarOne :=
        a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
          b D horder hdefect htotal hcenterOne (i.val - 2) (by
            rcases hiOdd with ⟨d, hd⟩
            omega) (by omega) hfarOdd
      rw [hfarOne] at hsum
      linarith

/-- Once the target center alpha is one, the alpha immediately before the
last type-III difference boundary is also one. -/
theorem lemma79Central_typeIIIRight_terminal_currentAlpha_eq_one_of_center
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hcenterOne : b.alphaValue ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ = 1)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last) :
    b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 1 := by
  have hlastEven := D.outer.right_even_distance
  have hbaseLast := D.outer.right_le_last
  have hrecover := Nat.sub_add_cancel hbaseLast
  have hseparated := D.outer.transition.separated
  have hpreviousOdd : Odd
      ((i.val - 1) - (D.outer.transition.firstTwo - 1)) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousRight : D.outer.transition.firstTwo ≤ i.val - 1 := by
    rcases hlastEven with ⟨d, hd⟩
    omega
  have hpreviousBefore : i.val - 1 < D.outer.last := by
    have := i.one_lt
    omega
  exact a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
    b D horder hdefect htotal hcenterOne (i.val - 1) hpreviousRight
      hpreviousBefore hpreviousOdd

end BONG.GoodBONG

end Bong
