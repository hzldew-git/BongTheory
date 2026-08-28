/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightPivotAlpha
import Bong.Bong.Beli2019Lemma611TypeI
import Bong.Bong.Beli2009BinaryRemarks

/-!
# Beli (2019), Lemma 6.9(i): the terminal right-pivot branch

When the maximal right pivot is immediately before the last unequal order,
the optional secondary representation candidate need not be strictly
positive.  Its nonpositive branch instead forces two exterior target orders
to differ by one.  Lemma 6.11(i) makes the intervening adjacent product have
odd order, hence zero quadratic defect, and the corresponding right alpha
candidate gives the required bound.
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

/-- An adjacent product of odd valuation has zero capped-free defect. -/
theorem adjacentDefect_eq_zero_of_order_sum_odd
    (b : GoodBONG r M (n + 1)) (i : Fin n)
    (hodd : Odd (b.order i.castSucc + b.order i.succ)) :
    b.adjacentDefect i = 0 := by
  have ordUnit_neg_eq (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    exact ord_neg K (z : K)
  have hproductOrder :
      ordUnit K (b.adjacentProduct i) =
        b.order i.castSucc + b.order i.succ := by
    have horderUnit (j : Fin (n + 1)) :
        ordUnit K (b.valueUnit j) = b.order j := by
      exact (b.toBONG.order_eq_ordUnit j).symm
    unfold adjacentProduct
    rw [ordUnit_neg_eq, ordUnit_mul, horderUnit, horderUnit]
  unfold adjacentDefect defectOrder
  rw [quadraticDefect_eq_zero_of_odd_ordUnit _ (hproductOrder.symm ▸ hodd)]
  rfl

/-- If the terminal secondary candidate is nonpositive, the target alpha at
the maximal right pivot is already at most one. -/
theorem lemma69_i_typeI_rightPivotAlpha_of_secondary_of_endpoint
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hendpoint : P.pivot + 1 = D.profile.last)
    (hi : 1 < (typeIRightPivotIndex a b D C P).val ∧
      (typeIRightPivotIndex a b D C P).val + 1 < n + 2)
    (hsecondary : a.representationSecondaryDefect b
      (typeIRightPivotIndex a b D C P) hi ≤ 0) :
    b.alphaValue ⟨P.pivot, by
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  have hlastBound := D.profile.lastDifference.bound
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    typeIRightPivotIndex a b D C P
  have hidxVal : idx.val = P.pivot + 1 := rfl
  have hidxPred : idx.val - 1 = P.pivot := by
    rw [hidxVal]
    omega
  have hidxPrev : idx.val - 2 = P.pivot - 1 := by
    rw [hidxVal]
    omega
  have hidxNext : idx.val + 1 = P.pivot + 2 := by
    rw [hidxVal]
  have hpivotTwoBound : P.pivot + 2 < n + 2 := by
    simpa only [idx, typeIRightPivotIndex] using hi.2
  have hleftPivot : C.leftSwitch ≤ P.pivot := by
    exact (C.left_le_anchor.trans C.anchor_le_right).trans
      ((Nat.le_succ C.rightSwitch).trans P.next_le_pivot)
  have hpivotOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst P.pivot (by
      have hnextPivot := P.next_le_pivot
      omega) (by omega) P.pivot_odd
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpivotPrevEven : Even (P.pivot - 1) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hprevDistance : Even (P.pivot - 1 - D.anchor) := by
    rcases hpivotPrevEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega⟩
  have hpivotNextEven : Even (P.pivot + 1) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hnextDistance : Even (P.pivot + 1 - D.anchor) := by
    rcases hpivotNextEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega⟩
  have htargetPrev := C.target_from_anchor (P.pivot - 1) (by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega)
    (by omega) hprevDistance
  have hsourceNext := C.source_after_right (P.pivot + 1) (by
      have hnextPivot := P.next_le_pivot
      omega)
    (by omega) hnextDistance
  have hnextShift :
      a.orderSequence.entryOrZero (P.pivot + 1) =
        b.orderSequence.entryOrZero (P.pivot - 1) - 1 := by
    have hanchorGap := D.anchor_gap
    omega
  have hafter :
      a.orderSequence.entryOrZero (P.pivot + 2) =
        b.orderSequence.entryOrZero (P.pivot + 2) := by
    exact D.profile.lastDifference.after (P.pivot + 2) (by omega)
      hpivotTwoBound
  have hdefectNonneg := a.truncatedPrefixDefect_nonneg
    (alphaV := alphaV) (alphaW := alphaW) b 1
    (idx.val + 2) (idx.val - 2)
  have hcoefficientTop :
      (((a.order ⟨idx.val, idx.lt_large⟩ +
        a.order ⟨idx.val + 1, hi.2⟩ -
        b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
          Int) : ℚ) : WithTop ℚ) ≤ 0 := by
    unfold representationSecondaryDefect at hsecondary
    exact (le_add_of_nonneg_right hdefectNonneg).trans hsecondary
  have hcoefficientOrder :
      a.order ⟨idx.val, idx.lt_large⟩ +
        a.order ⟨idx.val + 1, hi.2⟩ -
        b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ ≤ 0 := by
    exact_mod_cast hcoefficientTop
  have haCurrent : a.order ⟨idx.val, idx.lt_large⟩ =
      a.orderSequence.entryOrZero idx.val :=
    (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
      idx.lt_large).symm
  have haNext : a.order ⟨idx.val + 1, hi.2⟩ =
      a.orderSequence.entryOrZero (idx.val + 1) :=
    (BeliOrderSequence.entryOrZero_of_lt a.orderSequence hi.2).symm
  have hbPrevious :
      b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
        b.orderSequence.entryOrZero (idx.val - 2) :=
    (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (show idx.val - 2 < n + 2 by omega)).symm
  have hbCurrent :
      b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
        b.orderSequence.entryOrZero (idx.val - 1) :=
    (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (show idx.val - 1 < n + 2 by omega)).symm
  rw [haCurrent, haNext, hbPrevious, hbCurrent, hidxNext,
    hidxPrev, hidxPred, hidxVal, hnextShift, hafter] at hcoefficientOrder
  have houterUpper :
      b.orderSequence.entryOrZero (P.pivot + 2) ≤
        b.orderSequence.entryOrZero P.pivot + 1 := by
    omega
  have hsourceMono := a.orderSequence.twoStep P.pivot (by
    exact hpivotTwoBound)
  have houterLower :
      b.orderSequence.entryOrZero P.pivot + 1 ≤
        b.orderSequence.entryOrZero (P.pivot + 2) := by
    rw [← hpivotOrders.1, ← hafter]
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hpivotTwoBound]
    exact hsourceMono
  have houterEq :
      b.orderSequence.entryOrZero (P.pivot + 2) =
        b.orderSequence.entryOrZero P.pivot + 1 :=
    le_antisymm houterUpper houterLower
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    exact (D.profile.rightProfile (by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega)).1
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    exact ⟨d + e, by
      have hanchorLast := D.profile.anchor_le_last
      omega⟩
  have hleftLastEven : Even (D.profile.last - C.leftSwitch) := by
    rcases hlastEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    exact ⟨d - e, by
      have hleftLast := C.left_le_anchor.trans D.profile.anchor_le_last
      omega⟩
  have htargetLeft := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have htargetLast := C.target_from_anchor D.profile.last
    D.profile.anchor_le_last le_rfl hlastDistance
  have htargetEndpoints :
      b.orderSequence.entryOrZero C.leftSwitch =
        b.orderSequence.entryOrZero D.profile.last := by
    rw [htargetLeft, htargetLast, D.anchor_gap]
  have hpivotMod := b.entryOrZero_modEq_of_equal_even_endpoints
    (i := C.leftSwitch) (j := D.profile.last) (k := P.pivot)
    (by exact C.left_le_anchor.trans_lt D.anchor_bound)
    hlastBound hleftPivot (by omega) (by omega) hleftLastEven
      htargetEndpoints
  have hnextMod := b.entryOrZero_modEq_of_equal_even_endpoints
    (i := C.leftSwitch) (j := D.profile.last) (k := P.pivot + 1)
    (by exact C.left_le_anchor.trans_lt D.anchor_bound)
    hlastBound (hleftPivot.trans (Nat.le_succ _)) (by omega) (by omega)
      hleftLastEven htargetEndpoints
  have hsameMod : Int.ModEq 2
      (b.orderSequence.entryOrZero P.pivot)
      (b.orderSequence.entryOrZero (P.pivot + 1)) :=
    hpivotMod.trans hnextMod.symm
  have houterMod : Int.ModEq 2
      (b.orderSequence.entryOrZero (P.pivot + 2))
      (b.orderSequence.entryOrZero (P.pivot + 1) + 1) := by
    rw [houterEq]
    exact hsameMod.add Int.ModEq.rfl
  have hsumOdd : Odd
      (b.orderSequence.entryOrZero (P.pivot + 1) +
        b.orderSequence.entryOrZero (P.pivot + 2)) := by
    have hodd := odd_add_of_modEq_add_one
      (a := b.orderSequence.entryOrZero (P.pivot + 2))
      (b := b.orderSequence.entryOrZero (P.pivot + 1)) houterMod
    simpa only [add_comm] using hodd
  let p : Fin (n + 1) := ⟨P.pivot, by omega⟩
  let next : Fin (n + 1) := ⟨P.pivot + 1, by omega⟩
  have horderSumOdd : Odd (b.order next.castSucc + b.order next.succ) := by
    rw [← b.orderSequence_entryOrZero_eq_order next.castSucc,
      ← b.orderSequence_entryOrZero_eq_order next.succ]
    simpa only [next, Fin.val_castSucc, Fin.val_succ] using hsumOdd
  have hadjacent : b.adjacentDefect next = 0 :=
    b.adjacentDefect_eq_zero_of_order_sum_odd next horderSumOdd
  have horderDifference : b.order next.succ - b.order p.castSucc = 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order next.succ,
      ← b.orderSequence_entryOrZero_eq_order p.castSucc]
    change b.orderSequence.entryOrZero (P.pivot + 2) -
      b.orderSequence.entryOrZero P.pivot = 1
    omega
  have hcandidate : b.rightDefectCandidate p next = (1 : WithTop ℚ) := by
    unfold rightDefectCandidate
    rw [hadjacent, horderDifference]
    norm_num
  have halpha := b.alpha_le_rightDefectCandidate
    (show p ≤ next by
      change P.pivot ≤ P.pivot + 1
      omega)
  rw [← b.coe_alphaValue, hcandidate] at halpha
  exact_mod_cast halpha

end BONG.GoodBONG

end Bong
