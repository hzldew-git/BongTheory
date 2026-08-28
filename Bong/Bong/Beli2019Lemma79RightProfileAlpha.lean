/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark613TypeIIIRightAlpha
import Bong.Bong.Beli2019Lemma79OrderRightAlternating

/-!
# Beli (2019), Lemma 7.9(ii): the case-7 target recursion

On the case-7 parity class, the target orders two places apart both lie in
the even part of the right outer profile.  Corollary 2.3 then gives the
exact recursion relating the current and next target alphas.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The target two-step equality and alpha recursion on the case-7 parity
class of a no-gap-two right profile. -/
theorem lemma79_rightProfile_target_twoStep_and_alpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : O.transition.firstTwo ≤ i.val)
    (hlast : i.val < O.last)
    (hodd : Odd (i.val - (O.transition.firstTwo - 1))) :
    b.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ =
        b.order ⟨i.val + 1, by
          have hb := O.lastDifference.bound
          omega⟩ ∧
      b.alphaValue ⟨i.val - 1, by
        have hb := O.lastDifference.bound
        omega⟩ =
        ((b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i.val, by
            have hb := O.lastDifference.bound
            omega⟩ := by
  rcases hodd with ⟨d, hd⟩
  have hpreviousEven : Even
      ((i.val - 1) - (O.transition.firstTwo - 1)) := ⟨d, by omega⟩
  have hfarEven : Even
      ((i.val + 1) - (O.transition.firstTwo - 1)) := ⟨d + 1, by omega⟩
  have hpreviousTarget := O.target_rightEven_eq_boundary
    (i.val - 1) (by omega) (by omega) hpreviousEven
  have hfarTarget := O.target_rightEven_eq_boundary
    (i.val + 1) (by omega) (by omega) hfarEven
  have htwoStepEntries : b.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val + 1) :=
    hpreviousTarget.trans hfarTarget.symm
  have hfarBound : i.val + 1 < n + 2 := by
    have hb := O.lastDifference.bound
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
