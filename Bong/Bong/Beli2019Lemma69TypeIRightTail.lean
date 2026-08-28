/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightPivot

/-!
# Beli (2019), Lemma 6.9(i): propagation from the type-I right pivot

Once the target alpha at the maximal right pivot is at most one, endpoint
monotonicity propagates the estimate through the whole odd right tail.  The
constant left-order head and the constant right endpoints on the tail are
the two direct counterparts of the left-pivot argument.
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
  [Beli2006AlphaLaws.{u, w} K]

/-- A bound at the maximal right pivot propagates to every odd target alpha
strictly between the right switch and the last unequal entry. -/
theorem lemma69_i_typeI_rightTailAlpha_le_of_pivot
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hpivotAlpha : b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1)
    (k : Nat) (hright : C.rightSwitch < k)
    (hlast : k < D.profile.last) (hodd : Odd k) :
    b.alphaValue ⟨k, by
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  have hlastBound := D.profile.lastDifference.bound
  have hpivotBound : P.pivot < n + 1 := by
    have hpivotLast := P.pivot_le_last_previous
    omega
  have hkBound : k < n + 1 := by omega
  let pivotFin : Fin (n + 1) := ⟨P.pivot, hpivotBound⟩
  let kFin : Fin (n + 1) := ⟨k, hkBound⟩
  have hpivotAlpha' : b.alphaValue pivotFin ≤ 1 := by
    simpa only [pivotFin] using hpivotAlpha
  by_cases hpivotK : P.pivot ≤ k
  · have hmono := b.alphaRightEndpoint_antitone
      (show pivotFin ≤ kFin by
        change P.pivot ≤ k
        exact hpivotK)
    have hanchorEven : Even D.anchor := by
      by_cases heq : D.profile.first = D.anchor
      · rw [← heq, hfirst]
        exact ⟨0, by omega⟩
      · have hlt : D.profile.first < D.anchor :=
          lt_of_le_of_ne D.profile.first_le_anchor heq
        simpa only [hfirst, Nat.sub_zero] using
          (D.profile.leftProfile hlt).1
    have hpivotOneEven : Even (P.pivot + 1) := by
      rcases P.pivot_odd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hkOneEven : Even (k + 1) := by
      rcases hodd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hpivotDistance : Even (P.pivot + 1 - D.anchor) := by
      rcases hpivotOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega⟩
    have hkDistance : Even (k + 1 - D.anchor) := by
      rcases hkOneEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by
        have hanchorRight := C.anchor_le_right
        omega⟩
    have hpivotOrder := C.target_from_anchor (P.pivot + 1) (by
        have hanchorRight := C.anchor_le_right
        have hnextPivot := P.next_le_pivot
        omega)
      (by
        have hpivotLast := P.pivot_le_last_previous
        omega) hpivotDistance
    have hkOrder := C.target_from_anchor (k + 1) (by
        have hanchorRight := C.anchor_le_right
        omega)
      (by omega) hkDistance
    have horders : b.order kFin.succ = b.order pivotFin.succ := by
      rw [← b.orderSequence_entryOrZero_eq_order kFin.succ,
        ← b.orderSequence_entryOrZero_eq_order pivotFin.succ]
      change b.orderSequence.entryOrZero (k + 1) =
        b.orderSequence.entryOrZero (P.pivot + 1)
      exact hkOrder.trans hpivotOrder.symm
    unfold alphaRightEndpoint at hmono
    rw [horders] at hmono
    linarith
  · have hkPivot : k ≤ P.pivot :=
      Nat.le_of_lt (lt_of_not_ge hpivotK)
    have hmono := b.alphaLeftEndpoint_monotone
      (show kFin ≤ pivotFin by
        change k ≤ P.pivot
        exact hkPivot)
    have hentry := P.head_current_eq k (by omega) hkPivot hodd
    have horders : b.order kFin.castSucc = b.order pivotFin.castSucc := by
      rw [← b.orderSequence_entryOrZero_eq_order kFin.castSucc,
        ← b.orderSequence_entryOrZero_eq_order pivotFin.castSucc]
      change b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero P.pivot
      exact hentry
    unfold alphaLeftEndpoint at hmono
    rw [horders] at hmono
    linarith

/-- In particular, the target alpha immediately after the right switch is
at most one once the pivot estimate is known. -/
theorem lemma69_i_typeI_nextTargetAlpha_le_of_pivot
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (P : Lemma69TypeIRightPivotData a b D C)
    (hpivotAlpha : b.alphaValue ⟨P.pivot, by
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1) :
    b.alphaValue ⟨C.rightSwitch + 1, by
      have hnextPivot := P.next_le_pivot
      have hpivotLast := P.pivot_le_last_previous
      have hlastBound := D.profile.lastDifference.bound
      omega⟩ ≤ 1 := by
  apply lemma69_i_typeI_rightTailAlpha_le_of_pivot
    a b D C hfirst hrightLast P hpivotAlpha (C.rightSwitch + 1)
  · omega
  · have hnextPivot := P.next_le_pivot
    have hpivotLast := P.pivot_le_last_previous
    omega
  · rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by omega⟩

end BONG.GoodBONG

end Bong
