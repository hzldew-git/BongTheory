/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79NextAlpha
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint

/-!
# Beli (2019), Lemma 6.9(i): the type-II target left alpha

At the last alpha before the type-II right transition, the target orders are
`T, T + 1`.  Their sum is odd, so the adjacent defect vanishes and the local
alpha candidate is one.  P1 then propagates this bound backwards across the
constant target plateau and the even left outer coordinates.
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

/-- The type-II target alpha is at most one at every even coordinate through
the normalized left transition. -/
theorem beli2019Lemma69_i_typeII_targetLeftTail
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (k : Nat) (hk : k ≤ D.outer.transition.lastZero) (heven : Even k) :
    b.alphaValue ⟨k, by
      have hbound := D.outer.transition.firstTwo_le_rank
      have hlong := D.long
      omega⟩ ≤ 1 := by
  let left := D.outer.transition.lastZero
  let pivotIndex := D.outer.transition.firstTwo - 2
  have hpivotBound : pivotIndex < n + 1 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    simp only [pivotIndex]
    omega
  let pivot : Fin (n + 1) := ⟨pivotIndex, hpivotBound⟩
  let current : Fin (n + 1) := ⟨k, by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    omega⟩
  let T := b.orderSequence.entryOrZero left
  have hsourcePivot : a.orderSequence.entryOrZero pivotIndex = T := by
    simpa only [pivotIndex, left, T] using D.middle pivotIndex (by
      have hlong := D.long
      simp only [pivotIndex]
      omega) (by
        have hlong := D.long
        simp only [pivotIndex]
        omega)
  have hcommonPivot : a.orderSequence.entryOrZero pivotIndex =
      b.orderSequence.entryOrZero pivotIndex := by
    exact D.outer.transition.middle pivotIndex (by
      have hlong := D.long
      simp only [pivotIndex]
      omega) (by
        have hlong := D.long
        simp only [pivotIndex]
        omega)
  have htargetPivot : b.orderSequence.entryOrZero pivotIndex = T :=
    hcommonPivot.symm.trans hsourcePivot
  have htargetNext :
      b.orderSequence.entryOrZero (pivotIndex + 1) = T + 1 := by
    have hindex : pivotIndex + 1 =
        D.outer.transition.firstTwo - 1 := by
      have hlong := D.long
      simp only [pivotIndex]
      omega
    rw [hindex, D.right_target]
  have horderPivot : b.order pivot.castSucc = T := by
    rw [← b.orderSequence_entryOrZero_eq_order pivot.castSucc]
    change b.orderSequence.entryOrZero pivotIndex = T
    exact htargetPivot
  have horderNext : b.order pivot.succ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order pivot.succ]
    change b.orderSequence.entryOrZero (pivotIndex + 1) = T + 1
    exact htargetNext
  have hsumOdd : Odd (b.order pivot.castSucc + b.order pivot.succ) := by
    rw [horderPivot, horderNext]
    refine ⟨T, by omega⟩
  have hadjacent : b.adjacentDefect pivot = 0 :=
    b.adjacentDefect_eq_zero_of_order_sum_odd pivot hsumOdd
  have horderDifference : b.order pivot.succ -
      b.order pivot.castSucc = 1 := by
    rw [horderPivot, horderNext]
    omega
  have hcandidate : b.leftDefectCandidate pivot pivot =
      (1 : WithTop ℚ) := by
    unfold leftDefectCandidate
    rw [hadjacent, horderDifference]
    norm_num
  have hpivotAlphaTop := b.alpha_le_leftDefectCandidate
    (i := pivot) (j := pivot) le_rfl
  rw [← b.coe_alphaValue, hcandidate] at hpivotAlphaTop
  have hpivotAlpha : b.alphaValue pivot ≤ 1 := by
    exact_mod_cast hpivotAlphaTop
  have hcurrentOrderRaw := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two k hk heven
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftOrderRaw := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  have hcurrentOrder : b.order current.castSucc = T := by
    rw [← b.orderSequence_entryOrZero_eq_order current.castSucc]
    change b.orderSequence.entryOrZero k = T
    exact hcurrentOrderRaw.trans hleftOrderRaw.symm
  have hpivotOrder : b.order pivot.castSucc = T := horderPivot
  have hcurrentLePivot : current ≤ pivot := by
    change k ≤ pivotIndex
    have hlong := D.long
    simp only [pivotIndex] at *
    omega
  have hmono := b.alphaLeftEndpoint_monotone hcurrentLePivot
  unfold alphaLeftEndpoint at hmono
  rw [hcurrentOrder, hpivotOrder] at hmono
  have hcurrentAlpha : b.alphaValue current ≤ 1 := by
    linarith
  simpa only [current] using hcurrentAlpha

end BONG.GoodBONG

end Bong
