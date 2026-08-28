/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightNeighbor

/-!
# Beli (2019), Lemma 6.9(i): the type-I left-tail pivot

On the even indices preceding the canonical left switch, the intervening
odd source orders form a nondecreasing finite sequence.  This module chooses
the first index at which that sequence reaches its terminal value.  It is the
index `l` used in the long domination argument in the proof of Lemma 6.9(i).
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

/-- The canonical minimal pivot on the type-I left tail. -/
structure Lemma69TypeILeftPivotData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D) where
  pivot : Nat
  pivot_le_previous : pivot ≤ C.leftSwitch - 2
  pivot_even : Even pivot
  next_eq_terminal :
    a.orderSequence.entryOrZero (pivot + 1) =
      a.orderSequence.entryOrZero (C.leftSwitch - 1)
  earlier_next_lt (k : Nat) (hk : k < pivot) (heven : Even k) :
    a.orderSequence.entryOrZero (k + 1) <
      a.orderSequence.entryOrZero (pivot + 1)
  tail_next_eq (k : Nat) (hpivot : pivot ≤ k)
      (hprevious : k ≤ C.leftSwitch - 2) (heven : Even k) :
    a.orderSequence.entryOrZero (k + 1) =
      a.orderSequence.entryOrZero (pivot + 1)

/-- Existence of the minimal odd-order pivot used in Lemma 6.9(i). -/
theorem lemma69_i_typeI_leftPivotData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hleftPos : 0 < C.leftSwitch) :
    Nonempty (Lemma69TypeILeftPivotData a b D C) := by
  classical
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  let previous := C.leftSwitch - 2
  have hpreviousEq : previous + 1 = C.leftSwitch - 1 := by
    simp only [previous]
    omega
  have hpreviousEven : Even previous := by
    rcases C.left_even with ⟨d, hd⟩
    exact ⟨d - 1, by
      simp only [previous]
      omega⟩
  have hpreviousBound : previous + 1 < n + 2 := by
    have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
    simp only [previous]
    omega
  have hnextMonotone (k : Nat) (hk : k ≤ previous)
      (heven : Even k) :
      a.orderSequence.entryOrZero (k + 1) ≤
        a.orderSequence.entryOrZero (previous + 1) := by
    have hkBound : k + 1 < n + 2 := by omega
    have hgapEven : Even ((previous + 1) - (k + 1)) := by
      rcases hpreviousEven with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    exact a.orderSequence.entryOrZero_le_of_evenGap
      (k + 1) (previous + 1) (by omega) hpreviousBound hgapEven
  let pivotSet := (Finset.range (previous + 1)).filter fun k ↦
    Even k ∧ a.orderSequence.entryOrZero (k + 1) =
      a.orderSequence.entryOrZero (previous + 1)
  have hpreviousMem : previous ∈ pivotSet := by
    simp only [pivotSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpreviousEven, trivial⟩
  have hpivotSet : pivotSet.Nonempty := ⟨previous, hpreviousMem⟩
  let pivot := pivotSet.min' hpivotSet
  have hpivotMem : pivot ∈ pivotSet := pivotSet.min'_mem hpivotSet
  have hpivotData := Finset.mem_filter.mp hpivotMem
  have hpivotLe : pivot ≤ previous := by
    have hpivotRange := Finset.mem_range.mp hpivotData.1
    omega
  have hpivotEven := hpivotData.2.1
  have hpivotValue := hpivotData.2.2
  have hearlier (k : Nat) (hk : k < pivot) (heven : Even k) :
      a.orderSequence.entryOrZero (k + 1) <
        a.orderSequence.entryOrZero (pivot + 1) := by
    have hkPrevious : k ≤ previous := hk.le.trans hpivotLe
    have hle := hnextMonotone k hkPrevious heven
    rw [← hpivotValue] at hle
    exact lt_of_le_of_ne hle (by
      intro heq
      have hkMem : k ∈ pivotSet := by
        simp only [pivotSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, heven, heq.trans hpivotValue⟩
      exact (not_le_of_gt hk) (pivotSet.min'_le k hkMem))
  have htail (k : Nat) (hpivot : pivot ≤ k)
      (hkPrevious : k ≤ previous) (heven : Even k) :
      a.orderSequence.entryOrZero (k + 1) =
        a.orderSequence.entryOrZero (pivot + 1) := by
    have hkBound : k + 1 < n + 2 := by omega
    have hpivotBound : pivot + 1 < n + 2 := by omega
    have hgapEven : Even ((k + 1) - (pivot + 1)) := by
      rcases heven with ⟨d, hd⟩
      rcases hpivotEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have hlower := a.orderSequence.entryOrZero_le_of_evenGap
      (pivot + 1) (k + 1) (by omega) hkBound hgapEven
    have hupper := hnextMonotone k hkPrevious heven
    rw [← hpivotValue] at hupper
    exact le_antisymm hupper hlower
  exact ⟨{
    pivot := pivot
    pivot_le_previous := by simpa only [previous] using hpivotLe
    pivot_even := hpivotEven
    next_eq_terminal := by
      rw [← hpreviousEq]
      exact hpivotValue
    earlier_next_lt := hearlier
    tail_next_eq := by
      intro k hpivot hkPrevious heven
      exact htail k hpivot (by simpa only [previous] using hkPrevious)
        heven }⟩

end BONG.GoodBONG

end Bong
