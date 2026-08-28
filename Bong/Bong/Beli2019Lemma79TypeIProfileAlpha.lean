/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeISum
import Bong.Bong.Beli2019Lemma79TypeIBetaBound

/-!
# Beli (2019), Lemma 7.9(ii): type-I target-alpha identities

At an odd paper boundary in the canonical type-I interval, the two target
orders two places apart agree.  Corollary 2.3 then gives the exact recursion
for the intervening target alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The two profile identities used in the target-alpha branch of case 4. -/
theorem lemma79_typeI_target_twoStep_and_alpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    b.order ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ =
        b.order ⟨i.val + 1, by
          rcases hodd with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          have hr := C.right_le_last
          have hb := D.profile.lastDifference.bound
          omega⟩ ∧
      b.alphaValue ⟨i.val - 1, by
        have hr := C.right_le_last
        have hb := D.profile.lastDifference.bound
        omega⟩ =
        ((b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i.val, by
            rcases hodd with ⟨d, hd⟩
            rcases C.right_even with ⟨e, he⟩
            have hr := C.right_le_last
            have hb := D.profile.lastDifference.bound
            omega⟩ := by
  rcases hodd with ⟨d, hd⟩
  have hpreviousEven : Even (i.val - 1) := ⟨d, by omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarRight : i.val + 1 ≤ C.rightSwitch := by
    rcases C.right_even with ⟨e, he⟩
    omega
  have hfarLeft : C.leftSwitch ≤ i.val + 1 := by omega
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hfarBound : i.val + 1 < n + 2 := hfarRight.trans_lt hrightBound
  have hcurrentAlphaBound : i.val < n + 1 := by omega
  have hpreviousAlphaBound : i.val - 1 < n + 1 := by omega
  have hsourceAt (k : Nat) (hkEven : Even k)
      (hkRight : k ≤ C.rightSwitch) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor := by
    by_cases hkAnchor : k ≤ D.anchor
    · exact C.source_to_anchor k hkAnchor hkEven
    · have hanchorK : D.anchor ≤ k := Nat.le_of_lt (lt_of_not_ge hkAnchor)
      have hanchorEven : Even D.anchor := by
        by_cases heq : D.profile.first = D.anchor
        · rw [← heq, hfirst]
          exact ⟨0, by omega⟩
        · have hlt : D.profile.first < D.anchor :=
            lt_of_le_of_ne D.profile.first_le_anchor heq
          simpa only [hfirst, Nat.sub_zero] using
            (D.profile.leftProfile hlt).1
      have hdistance : Even (k - D.anchor) := by
        rcases hkEven with ⟨x, hx⟩
        rcases hanchorEven with ⟨y, hy⟩
        exact ⟨x - y, by omega⟩
      exact C.source_to_right k hanchorK hkRight hdistance
  have hsourcePrevious := hsourceAt (i.val - 1) hpreviousEven hright.le
  have hsourceFar := hsourceAt (i.val + 1) hfarEven hfarRight
  have htargetPrevious := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst (i.val - 1) hpreviousEven hleft hright.le
  have htargetFar := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst (i.val + 1) hfarEven hfarLeft hfarRight
  have htwoStepEntries : b.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val + 1) := by omega
  have htwoStep : b.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val + 1, hfarBound⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htwoStepEntries
  refine ⟨htwoStep, ?_⟩
  let previous : Fin (n + 1) := ⟨i.val - 1, hpreviousAlphaBound⟩
  let current : Fin (n + 1) := ⟨i.val, hcurrentAlphaBound⟩
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
