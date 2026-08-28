/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightArithmetic
import Bong.Bong.Beli2019Lemma79TypeIBetaBound

/-!
# Beli (2019), Lemma 7.9(ii): type-I right-profile alpha identities

On the odd right tail, the two target orders surrounding the boundary are
equal. Corollary 2.3 therefore gives the exact recursion for the intervening
target alpha, just as it does in the central interval.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The two target-profile identities used in the right-tail beta branch of
Lemma 7.9(ii), case 4. -/
theorem lemma79_typeI_right_target_twoStep_and_alpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hlast : i.val < D.profile.last) (hodd : Odd i.val) :
    b.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ =
        b.order ⟨i.val + 1, by
          have hb := D.profile.lastDifference.bound
          omega⟩ ∧
      b.alphaValue ⟨i.val - 1, by
        have hb := D.profile.lastDifference.bound
        omega⟩ =
        ((b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i.val, by
            have hb := D.profile.lastDifference.bound
            omega⟩ := by
  rcases hodd with ⟨d, hd⟩
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpreviousEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hpreviousDistance : Even (i.val - 1 - D.anchor) := by
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have har := C.anchor_le_right
      omega⟩
  have hfarDistance : Even (i.val + 1 - D.anchor) := by
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d + 1 - e, by
      have har := C.anchor_le_right
      omega⟩
  have hpreviousTarget := C.target_from_anchor (i.val - 1) (by
      have har := C.anchor_le_right
      omega)
    (by omega) hpreviousDistance
  have hfarTarget := C.target_from_anchor (i.val + 1) (by
      have har := C.anchor_le_right
      omega)
    (by omega) hfarDistance
  have htwoStepEntries : b.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val + 1) := by
    rw [hpreviousTarget, hfarTarget]
  have hfarBound : i.val + 1 < n + 2 := by
    have hb := D.profile.lastDifference.bound
    omega
  have htwoStep : b.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val + 1, hfarBound⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htwoStepEntries
  refine ⟨htwoStep, ?_⟩
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let current : Fin (n + 1) := ⟨i.val, by omega⟩
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hcurrentCast : current.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : current.succ =
      (⟨i.val + 1, hfarBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpreviousCurrent : previous ≤ current := by
    change i.val - 1 ≤ i.val
    omega
  have hsum : b.adjacentOrderSum previous =
      b.adjacentOrderSum current := by
    unfold adjacentOrderSum
    rw [hpreviousCast, hpreviousSucc, hcurrentCast, hcurrentSucc]
    rw [htwoStep]
    omega
  have hconstant := b.beli2009Corollary23 previous current
    hpreviousCurrent hsum
  have hendpoint := hconstant.leftEndpoint_eq current
    hpreviousCurrent le_rfl
  unfold alphaLeftEndpoint at hendpoint
  have hresult : b.alphaValue previous =
      ((b.order current.castSucc - b.order previous.castSucc : Int) : ℚ) +
        b.alphaValue current := by
    push_cast at hendpoint ⊢
    linarith
  rw [hcurrentCast, hpreviousCast] at hresult
  simpa only [previous, current] using hresult

end BONG.GoodBONG

end Bong
