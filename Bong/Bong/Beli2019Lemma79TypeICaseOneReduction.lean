/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICanonicalAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 1: reduction to the unique exception

At an even coordinate of the canonical type-I interval, condition 2.1(i)
normally bounds the cross gap by `2e`.  If this fails, the coordinate must be
the left switch, the preceding target and comparison orders coincide, and the
target gap is exactly `2e + 1`.  These are precisely the numerical hypotheses
of case 1 in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A large cross gap on the even canonical type-I interval is exactly the
exceptional first-switch configuration of Lemma 7.9(ii), case 1. -/
theorem beli2019Lemma79_typeI_canonical_crossGap_or_caseOne
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ ≤ 2 * (ramificationIndex K : Int) ∨
      (i.val = C.leftSwitch ∧
        b.orderGap ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ = 2 * (ramificationIndex K : Int) + 1 ∧
        c.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ =
          b.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩) := by
  by_cases hcross : b.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ ≤ 2 * (ramificationIndex K : Int)
  · exact Or.inl hcross
  · apply Or.inr
    have hcrossStrict : 2 * (ramificationIndex K : Int) <
        b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ := lt_of_not_ge hcross
    have hleftEq : i.val = C.leftSwitch := by
      by_contra hne
      have hleftTwo : C.leftSwitch ≤ i.val - 2 := by
        rcases hiEven with ⟨d, hd⟩
        rcases C.left_even with ⟨e, he⟩
        omega
      have hpreviousEven : Even (i.val - 2) := by
        rcases hiEven with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have hprevious := lemma76_typeI_target_even_order_eq_left
        a b D C hfirst (i.val - 2) hleftTwo (by omega) hpreviousEven
      have hcurrent := lemma76_typeI_target_even_order_eq_left
        a b D C hfirst i.val hiLeft hiRight hiEven
      have htwo : b.order ⟨i.val - 2, by
            have hiBound := i.lt_large
            omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
        rw [← b.orderSequence_entryOrZero_eq_order,
          ← b.orderSequence_entryOrZero_eq_order]
        exact hprevious.symm.trans hcurrent
      have hsource := b.orderGap_previous_le_twoE_of_twoStep
        i (by
          rcases hiEven with ⟨d, hd⟩
          omega) htwo
      exact hcross
        (crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
          b c horderBC i hsource)
    have hleftPos : 0 < C.leftSwitch := by
      have hiPos := i.pos
      omega
    let previous : Fin (n + 1) := ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩
    have hgapUpper : b.orderGap previous ≤
        2 * (ramificationIndex K : Int) + 1 := by
      simpa only [previous, hleftEq] using
        lemma79_typeI_leftSwitch_gap_le_twoE_add_one
          a b D C hleftPos
    have hpreviousSucc : previous.succ =
        (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [previous, Fin.val_succ]
      omega
    have hpreviousCast : previous.castSucc =
        (⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hgapUpper' : b.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ ≤ 2 * (ramificationIndex K : Int) + 1 := by
      unfold orderGap at hgapUpper
      rw [hpreviousSucc, hpreviousCast] at hgapUpper
      exact hgapUpper
    have hsequence :=
      (b.representationOrderCondition_iff c le_rfl).mp horderBC
    have hlarge : 2 * (ramificationIndex K : Int) ≤
        b.orderSequence.entry (i.val - 1 + 1) (by
          have hiBound := i.lt_large
          omega) -
        c.orderSequence.entry (i.val - 1) (by
          have hiBound := i.lt_large
          omega) := by
      simpa only [orderSequence_at, Nat.sub_add_cancel i.pos] using
        hcrossStrict.le
    have hpair := BeliOrderSequence.le_pair_of_large_crossGap
      hsequence b.orderSequence_isKappaBounded_two_mul_e
        c.orderSequence_isKappaBounded_two_mul_e
        (i.val - 1) (by
          have hiBound := i.lt_large
          omega) (by
          have hiBound := i.lt_large
          omega) hlarge
    have hpreviousLe : b.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ ≤
        c.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ := by
      simpa only [orderSequence_at] using hpair.1
    have hgapEq : b.orderGap previous =
        2 * (ramificationIndex K : Int) + 1 := by
      unfold orderGap
      rw [hpreviousSucc, hpreviousCast]
      omega
    have hpreviousEq : c.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ =
        b.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ := by omega
    exact ⟨hleftEq, by simpa only [previous] using hgapEq, hpreviousEq⟩

end BONG.GoodBONG

end Bong
