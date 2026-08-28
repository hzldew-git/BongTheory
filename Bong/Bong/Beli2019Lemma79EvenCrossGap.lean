/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenSecondaryInterior
import Bong.Bong.Beli2019SequenceDual

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the cross-gap bound

The alternating left profile bounds the current source gap by `2e`.
Condition 2.1(i) and Lemma 1.8(ii) then show that the cross gap to the
third lattice is also at most `2e`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Equality two positions apart turns the universal lower bound on the
preceding gap into an upper bound on the current gap. -/
theorem orderGap_previous_le_twoE_of_twoStep
    (b : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩) :
    b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤ 2 * (ramificationIndex K : Int) := by
  let previous : Fin (n + 1) := ⟨i.val - 2, by
    have hb := i.lt_large
    omega⟩
  have hlower := b.orderGap_ge_neg_two_mul_e previous
  unfold orderGap at hlower ⊢
  have hpreviousSucc : previous.succ =
      (⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change i.val - 2 + 1 = i.val - 1
    omega
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [hpreviousSucc, hpreviousCast] at hlower
  let current : Fin (n + 1) := ⟨i.val - 1, by
    have hb := i.lt_large
    omega⟩
  change b.order current.succ - b.order current.castSucc ≤
    2 * (ramificationIndex K : Int)
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    have hp := i.pos
    omega
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [hcurrentSucc, hcurrentCast]
  omega

/-- If the source gap is at most `2e`, condition 2.1(i) forbids a larger
cross gap to the represented lattice. -/
theorem crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hsource : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤ 2 * (ramificationIndex K : Int)) :
    b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ ≤ 2 * (ramificationIndex K : Int) := by
  by_contra hnot
  have hcross : 2 * (ramificationIndex K : Int) <
      b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ := lt_of_not_ge hnot
  have hsequence :=
    (b.representationOrderCondition_iff c le_rfl).mp horder
  have hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderSequence.entry (i.val - 1 + 1) (by
        have hb := i.lt_large
        omega) -
      c.orderSequence.entry (i.val - 1) (by
        have hb := i.lt_large
        omega) := by
    simpa only [orderSequence_at, Nat.sub_add_cancel i.pos] using hcross.le
  have hpair := BeliOrderSequence.le_pair_of_large_crossGap
    hsequence b.orderSequence_isKappaBounded_two_mul_e
      c.orderSequence_isKappaBounded_two_mul_e
      (i.val - 1) (by
        have hb := i.lt_large
        omega) (by
        have hb := i.lt_large
        omega) hlarge
  have hprevious : b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      c.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
    simpa only [orderSequence_at] using hpair.1
  let current : Fin (n + 1) := ⟨i.val - 1, by
    have hb := i.lt_large
    omega⟩
  have hsource' : b.order current.succ - b.order current.castSucc ≤
      2 * (ramificationIndex K : Int) := by
    simpa only [current, orderGap] using hsource
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    have hp := i.pos
    omega
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [hcurrentSucc, hcurrentCast] at hsource'
  omega

end BONG.GoodBONG

end Bong
