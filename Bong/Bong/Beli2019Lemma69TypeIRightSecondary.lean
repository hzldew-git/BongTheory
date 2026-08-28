/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightPivotAlpha

/-!
# Beli (2019), Lemma 6.9(i): the interior right-pivot candidate

If the maximal right pivot is not the last odd position of the type-I
profile, its optional secondary representation candidate is strictly
positive.  The coefficient is exactly the strict increase in the target
odd-order plateau; the capped defect contributes a nonnegative term.
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

/-- Away from the right endpoint, the optional secondary candidate at the
maximal right pivot is strictly positive. -/
theorem lemma69_i_typeI_rightPivot_secondary_pos_of_interior
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hpivotInterior : P.pivot + 2 < D.profile.last)
    (hi : 1 < (typeIRightPivotIndex a b D C P).val ∧
      (typeIRightPivotIndex a b D C P).val + 1 < n + 2) :
    (0 : WithTop ℚ) < a.representationSecondaryDefect b
      (typeIRightPivotIndex a b D C P) hi := by
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
  have hpivotNextEven : Even (P.pivot + 1) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hpivotTwoOdd : Odd (P.pivot + 2) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hprevDistance : Even (P.pivot - 1 - D.anchor) := by
    rcases hpivotPrevEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega⟩
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
  have hpivotTwoOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst (P.pivot + 2) (by
      have hnextPivot := P.next_le_pivot
      omega) hpivotInterior hpivotTwoOdd
  have hlater := P.later_current_gt (P.pivot + 2) (by omega)
    (by omega) hpivotTwoOdd
  have hcoefficient : 0 <
      a.orderSequence.entryOrZero (P.pivot + 1) +
        a.orderSequence.entryOrZero (P.pivot + 2) -
        b.orderSequence.entryOrZero (P.pivot - 1) -
        b.orderSequence.entryOrZero P.pivot := by
    omega
  have hcoefficientOrder : 0 <
      a.order ⟨idx.val, idx.lt_large⟩ +
        a.order ⟨idx.val + 1, hi.2⟩ -
        b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
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
      hidxPrev, hidxPred, hidxVal]
    exact hcoefficient
  have hdefectNonneg := a.truncatedPrefixDefect_nonneg
    (alphaV := alphaV) (alphaW := alphaW) b 1
    (idx.val + 2) (idx.val - 2)
  unfold representationSecondaryDefect
  calc
    (0 : WithTop ℚ) <
        (((a.order ⟨idx.val, idx.lt_large⟩ +
          a.order ⟨idx.val + 1, hi.2⟩ -
          b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ :
            Int) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hcoefficientOrder
    _ ≤ _ := le_add_of_nonneg_right hdefectNonneg

/-- In the nonterminal-pivot case, M279 now needs only the right comparison
boundary supplied by the dual form of Lemma 6.3. -/
theorem beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary_of_interior
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hdefect : a.RepresentationDefectCondition b)
    (hboundary :
      (b.typeIRightPivotCutoff P.pivot : WithTop ℚ) <
        a.truncatedPrefixDefect b 1
          (D.profile.last + 1) (D.profile.last + 1))
    (hpivotInterior : P.pivot + 2 < D.profile.last) :
    b.alphaValue ⟨P.pivot, by
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  apply beli2019Lemma69_i_typeI_rightPivotAlpha_of_boundary
    (alphaV := alphaV) (alphaW := alphaW)
    a b D C hfirst P hdefect hboundary
  intro hi
  exact lemma69_i_typeI_rightPivot_secondary_pos_of_interior
    (alphaV := alphaV) (alphaW := alphaW)
    a b D C hfirst P hpivotInterior hi

end BONG.GoodBONG

end Bong
