/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightArithmetic
import Bong.Bong.Beli2019Lemma69CappedPropagationRight

/-!
# Beli (2019), Lemma 6.9(i): right-tail capped defects

If the target alpha at the maximal right pivot were larger than one, every
source and target capped adjacent defect from that pivot to the last unequal
entry would lie strictly above the primary-candidate cut.  Two domination
steps per pair then propagate a comparison-defect bound backwards from the
right boundary.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The additive cut opposite the primary representation coefficient at the
right pivot. -/
noncomputable def typeIRightPivotCutoff
    (b : GoodBONG r M (n + 2)) (P : Nat) : ℚ :=
  ((b.orderSequence.entryOrZero P -
    b.orderSequence.entryOrZero (P + 1) + 1 : Int) : ℚ)

/-- Under `beta_p > 1`, every later source adjacent capped defect on the odd
right tail is strictly above the pivot cut. -/
theorem lemma69_i_typeI_rightSourceLocal_gt_cutoff
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (j : Nat) (hpivot : P.pivot ≤ j)
    (hlast : j < D.profile.last) (hodd : Odd j) :
    (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
      a.truncatedPrefixDefect a (-1) j (j + 2) := by
  have hlastBound := D.profile.lastDifference.bound
  let p : Fin (n + 1) := ⟨P.pivot, by
    have hpivotLast := P.pivot_le_last_previous
    omega⟩
  let jf : Fin (n + 1) := ⟨j, by omega⟩
  have hjOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst j (by
      have hnextPivot := P.next_le_pivot
      omega) hlast hodd
  have hpOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst P.pivot (by
      have hnextPivot := P.next_le_pivot
      omega) (by
        have hpivotLast := P.pivot_le_last_previous
        rcases P.pivot_odd with ⟨d, hd⟩
        omega) P.pivot_odd
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have htargetNext (k : Nat) (hkRight : C.rightSwitch < k)
      (hkLast : k < D.profile.last) (hkOdd : Odd k) :
      b.orderSequence.entryOrZero (k + 1) =
        b.orderSequence.entryOrZero (P.pivot + 1) := by
    have hkOneEven : Even (k + 1) := by
      rcases hkOdd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hpOneEven : Even (P.pivot + 1) := by
      rcases P.pivot_odd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hkDistance : Even (k + 1 - D.anchor) := by
      rcases hkOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        omega⟩
    have hpDistance : Even (P.pivot + 1 - D.anchor) := by
      rcases hpOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega⟩
    exact (C.target_from_anchor (k + 1) (by
        have hanchorRight := C.anchor_le_right
        omega) (by omega) hkDistance).trans
      (C.target_from_anchor (P.pivot + 1) (by
          have hanchorRight := C.anchor_le_right
          have hnextPivot := P.next_le_pivot
          omega) (by
            have hpivotLast := P.pivot_le_last_previous
            omega) hpDistance).symm
  have hcurrentMono :
      b.orderSequence.entryOrZero P.pivot ≤
        b.orderSequence.entryOrZero j := by
    rcases eq_or_lt_of_le hpivot with rfl | hlt
    · exact le_rfl
    · exact (P.later_current_gt j hlt (by omega) hodd).le
  have hjSucc : a.order jf.succ =
      a.orderSequence.entryOrZero (j + 1) := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply congrArg a.order
    apply Fin.ext
    rfl
  have hjCast : a.order jf.castSucc =
      a.orderSequence.entryOrZero j := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply congrArg a.order
    apply Fin.ext
    rfl
  have hgapCut :
      ((a.order jf.succ - a.order jf.castSucc : Int) : ℚ) +
          b.typeIRightPivotCutoff P.pivot ≤ -1 := by
    rw [hjSucc, hjCast, hjOrders.1]
    have hnext := htargetNext j (by
      have hnextPivot := P.next_le_pivot
      omega) hlast hodd
    have hnextSource :
        a.orderSequence.entryOrZero (j + 1) =
          b.orderSequence.entryOrZero (P.pivot + 1) - 1 := by
      omega
    rw [hnextSource]
    unfold typeIRightPivotCutoff
    push_cast
    exact_mod_cast (show
      b.orderSequence.entryOrZero (P.pivot + 1) - 1 -
          (b.orderSequence.entryOrZero j + 1) +
          (b.orderSequence.entryOrZero P.pivot -
            b.orderSequence.entryOrZero (P.pivot + 1) + 1) ≤ -1 by
      omega)
  have hbound := a.alpha_le_orderGap_add_cappedAdjacent jf
  by_contra hnot
  have hlocalLe : a.truncatedPrefixDefect a (-1) j (j + 2) ≤
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) :=
    le_of_not_gt hnot
  have hnonnegative : (0 : WithTop ℚ) ≤ a.alphaValue jf := by
    exact_mod_cast (a.alpha_p2 jf).1
  have hnegative : (a.alphaValue jf : WithTop ℚ) ≤ (-1 : ℚ) := by
    calc
      (a.alphaValue jf : WithTop ℚ) ≤
          ((((a.order jf.succ - a.order jf.castSucc : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect a (-1) j (j + 2)) := by
        simpa only [jf] using hbound
      _ ≤ ((((a.order jf.succ - a.order jf.castSucc : Int) : ℚ) :
              WithTop ℚ) + b.typeIRightPivotCutoff P.pivot) :=
        add_le_add_right hlocalLe _
      _ ≤ (-1 : ℚ) := by exact_mod_cast hgapCut
  have himpossible : (0 : ℚ) ≤ -1 := by
    exact_mod_cast hnonnegative.trans hnegative
  norm_num at himpossible

/-- Under `beta_p > 1`, every later target adjacent capped defect on the odd
right tail is strictly above the pivot cut. -/
theorem lemma69_i_typeI_rightTargetLocal_gt_cutoff
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hpivotAlpha : 1 < b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩)
    (j : Nat) (hpivot : P.pivot ≤ j)
    (hlast : j < D.profile.last) (hodd : Odd j) :
    (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
      b.truncatedPrefixDefect b (-1) j (j + 2) := by
  have hlastBound := D.profile.lastDifference.bound
  let p : Fin (n + 1) := ⟨P.pivot, by
    have hpivotLast := P.pivot_le_last_previous
    omega⟩
  let jf : Fin (n + 1) := ⟨j, by omega⟩
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have htargetNext :
      b.orderSequence.entryOrZero (j + 1) =
        b.orderSequence.entryOrZero (P.pivot + 1) := by
    have hjOneEven : Even (j + 1) := by
      rcases hodd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hpOneEven : Even (P.pivot + 1) := by
      rcases P.pivot_odd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hjDistance : Even (j + 1 - D.anchor) := by
      rcases hjOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega⟩
    have hpDistance : Even (P.pivot + 1 - D.anchor) := by
      rcases hpOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega⟩
    exact (C.target_from_anchor (j + 1) (by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega) (by omega) hjDistance).trans
      (C.target_from_anchor (P.pivot + 1) (by
          have hanchorRight := C.anchor_le_right
          have hnextPivot := P.next_le_pivot
          omega) (by
            have hpivotLast := P.pivot_le_last_previous
            omega) hpDistance).symm
  have hbound := b.alpha_le_laterOrder_sub_add_cappedAdjacent
    (i := p) (j := jf) (by
      change P.pivot ≤ j
      exact hpivot)
  by_contra hnot
  have hlocalLe : b.truncatedPrefixDefect b (-1) j (j + 2) ≤
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) :=
    le_of_not_gt hnot
  have hjSucc : b.order jf.succ =
      b.orderSequence.entryOrZero (j + 1) := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hpCast : b.order p.castSucc =
      b.orderSequence.entryOrZero P.pivot := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hformula :
      ((b.orderSequence.entryOrZero (P.pivot + 1) -
          b.orderSequence.entryOrZero P.pivot : Int) : ℚ) +
        b.typeIRightPivotCutoff P.pivot = 1 := by
    unfold typeIRightPivotCutoff
    push_cast
    ring
  have halphaTop : (b.alphaValue p : WithTop ℚ) ≤ 1 := by
    calc
      (b.alphaValue p : WithTop ℚ) ≤
          ((((b.order jf.succ - b.order p.castSucc : Int) : ℚ) :
              WithTop ℚ) +
            b.truncatedPrefixDefect b (-1) j (j + 2)) := by
        simpa only [p, jf] using hbound
      _ ≤ ((((b.order jf.succ - b.order p.castSucc : Int) : ℚ) :
              WithTop ℚ) + b.typeIRightPivotCutoff P.pivot) :=
        add_le_add_right hlocalLe _
      _ = 1 := by
        rw [hjSucc, hpCast, htargetNext]
        exact_mod_cast hformula
  have halphaLe : b.alphaValue p ≤ 1 := by exact_mod_cast halphaTop
  have hpivotAlpha' : 1 < b.alphaValue p := by
    simpa only [p] using hpivotAlpha
  linarith

/-- A strict comparison-defect bound at the boundary after the last unequal
entry propagates backwards to the prefix two places after the right pivot. -/
theorem lemma69_i_typeI_rightCommon_of_boundary
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hpivotAlpha : 1 < b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩)
    (hboundary :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b 1
          (D.profile.last + 1) (D.profile.last + 1)) :
    (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 (P.pivot + 2) (P.pivot + 2) := by
  have hlastBound := D.profile.lastDifference.bound
  have hpivotLast := P.pivot_le_last_previous
  have hpivotTwoLast : P.pivot + 2 ≤ D.profile.last + 1 := by
    rcases P.pivot_odd with ⟨d, hd⟩
    omega
  have hdistanceEven : Even
      ((D.profile.last + 1) - (P.pivot + 2)) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    have hlastEven : Even D.profile.last := by
      have hanchorEven : Even D.anchor := by
        by_cases heq : D.profile.first = D.anchor
        · rw [← heq, hfirst]
          exact ⟨0, by omega⟩
        · have hlt : D.profile.first < D.anchor :=
            lt_of_le_of_ne D.profile.first_le_anchor heq
          simpa only [hfirst, Nat.sub_zero] using
            (D.profile.leftProfile hlt).1
      have hlastDistance : Even (D.profile.last - D.anchor) := by
        have hanchorLast : D.anchor < D.profile.last := by
          have hnextPivot := P.next_le_pivot
          have hanchorRight := C.anchor_le_right
          omega
        exact (D.profile.rightProfile hanchorLast).1
      rcases hanchorEven with ⟨e, he⟩
      rcases hlastDistance with ⟨f, hf⟩
      exact ⟨e + f, by
        have hanchorLast : D.anchor ≤ D.profile.last :=
          D.profile.anchor_le_last
        omega⟩
    rcases hlastEven with ⟨e, he⟩
    exact ⟨e - d - 1, by omega⟩
  rcases hdistanceEven with ⟨pairs, hpairs⟩
  have hpropagate (steps k : Nat)
      (hkPivot : P.pivot + 2 ≤ k)
      (hkStop : D.profile.last + 1 = k + 2 * steps)
      (hkOdd : Odd k) :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 k k := by
    induction steps generalizing k with
    | zero =>
        have hk : k = D.profile.last + 1 := by omega
        simpa only [hk] using hboundary
    | succ steps ih =>
        have hkLast : k < D.profile.last := by omega
        have hkTwoStop :
            D.profile.last + 1 = (k + 2) + 2 * steps := by omega
        have hkTwoOdd : Odd (k + 2) := by
          rcases hkOdd with ⟨d, hd⟩
          exact ⟨d + 1, by omega⟩
        have hnext := ih (k + 2) (by omega) hkTwoStop hkTwoOdd
        have hsource := lemma69_i_typeI_rightSourceLocal_gt_cutoff
          (alphaV := alphaV) a b D C hfirst P k (by omega) hkLast hkOdd
        have htarget := lemma69_i_typeI_rightTargetLocal_gt_cutoff
          (alphaW := alphaW) a b D C hfirst P hpivotAlpha
          k (by omega) hkLast hkOdd
        have htargetReverse :
            (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
              b.truncatedPrefixDefect b (-1) (k + 2) k := by
          rw [b.truncatedPrefixDefect_comm b (-1) (k + 2) k]
          exact htarget
        have hfirstDom := a.truncatedPrefixDefect_domination b b
          1 (-1) (k + 2) (k + 2) k
        have hcross :
            (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
              a.truncatedPrefixDefect b (-1) (k + 2) k :=
          (lt_min hnext htargetReverse).trans_le (by simpa using hfirstDom)
        have hsecondDom := a.truncatedPrefixDefect_domination a b
          (-1) (-1) k (k + 2) k
        exact (lt_min hsource hcross).trans_le (by simpa using hsecondDom)
  have hstop : D.profile.last + 1 = P.pivot + 2 + 2 * pairs := by
    omega
  have hpivotTwoOdd : Odd (P.pivot + 2) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  exact hpropagate pairs (P.pivot + 2) le_rfl hstop hpivotTwoOdd

end BONG.GoodBONG

end Bong
