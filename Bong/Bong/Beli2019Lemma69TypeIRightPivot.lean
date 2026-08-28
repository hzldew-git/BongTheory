/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeft

/-!
# Beli (2019), Lemma 6.9(i): the type-I right-tail pivot

The right tail uses the maximal odd index on the initial target-order
plateau.  Target odd orders are constant up to this pivot and strictly
larger afterwards.  This is the direct finite counterpart of the pivot
obtained by applying the paper's duality argument to the left tail.
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

/-- The maximal initial-order pivot on the odd type-I right tail. -/
structure Lemma69TypeIRightPivotData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D) where
  pivot : Nat
  next_le_pivot : C.rightSwitch + 1 ≤ pivot
  pivot_le_last_previous : pivot ≤ D.profile.last - 1
  pivot_odd : Odd pivot
  current_eq_initial :
    b.orderSequence.entryOrZero pivot =
      b.orderSequence.entryOrZero (C.rightSwitch + 1)
  later_current_gt (k : Nat) (hpivot : pivot < k)
      (hlast : k ≤ D.profile.last - 1) (hodd : Odd k) :
    b.orderSequence.entryOrZero pivot <
      b.orderSequence.entryOrZero k
  head_current_eq (k : Nat) (hnext : C.rightSwitch + 1 ≤ k)
      (hpivot : k ≤ pivot) (hodd : Odd k) :
    b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero pivot

/-- Existence of the maximal target-order pivot used on the type-I right
tail. -/
theorem lemma69_i_typeI_rightPivotData
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last) :
    Nonempty (Lemma69TypeIRightPivotData a b D C) := by
  classical
  have hlastBound := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    have hanchorLast : D.anchor < D.profile.last :=
      C.anchor_le_right.trans_lt hrightLast
    exact (D.profile.rightProfile hanchorLast).1
  have hrightDistance : Even (C.rightSwitch - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightLastEven : Even (D.profile.last - C.rightSwitch) := by
    rcases hlastDistance with ⟨d, hd⟩
    rcases hrightDistance with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hrightTwo : C.rightSwitch + 2 ≤ D.profile.last := by
    rcases hrightLastEven with ⟨d, hd⟩
    omega
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    exact ⟨d + e, by
      have hanchorLast := C.anchor_le_right.trans_lt hrightLast
      omega⟩
  have hnextOdd : Odd (C.rightSwitch + 1) := by
    rcases C.right_even with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hlastPreviousOdd : Odd (D.profile.last - 1) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  let next := C.rightSwitch + 1
  let lastPrevious := D.profile.last - 1
  have hnextLast : next ≤ lastPrevious := by
    simp only [next, lastPrevious]
    omega
  have horderMono (i j : Nat) (hnextI : next ≤ i)
      (hij : i ≤ j) (hjLast : j ≤ lastPrevious)
      (hiOdd : Odd i) (hjOdd : Odd j) :
      b.orderSequence.entryOrZero i ≤
        b.orderSequence.entryOrZero j := by
    have hjBound : j < n + 2 := by
      simp only [lastPrevious] at hjLast
      omega
    have hgapEven : Even (j - i) := by
      rcases hiOdd with ⟨d, hd⟩
      rcases hjOdd with ⟨e, he⟩
      exact ⟨e - d, by omega⟩
    exact b.orderSequence.entryOrZero_le_of_evenGap
      i j hij hjBound hgapEven
  let pivotSet := (Finset.Icc next lastPrevious).filter fun k ↦
    Odd k ∧ b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero next
  have hnextMem : next ∈ pivotSet := by
    simp only [pivotSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hnextLast⟩, by simpa only [next] using hnextOdd,
      trivial⟩
  have hpivotSet : pivotSet.Nonempty := ⟨next, hnextMem⟩
  let pivot := pivotSet.max' hpivotSet
  have hpivotMem : pivot ∈ pivotSet := pivotSet.max'_mem hpivotSet
  have hpivotData := Finset.mem_filter.mp hpivotMem
  have hpivotInterval := Finset.mem_Icc.mp hpivotData.1
  have hpivotOdd := hpivotData.2.1
  have hpivotValue := hpivotData.2.2
  have hlater (k : Nat) (hpivotK : pivot < k)
      (hkLast : k ≤ lastPrevious) (hkOdd : Odd k) :
      b.orderSequence.entryOrZero pivot <
        b.orderSequence.entryOrZero k := by
    have hle := horderMono next k le_rfl
      (hpivotInterval.1.trans hpivotK.le) hkLast
      (by simpa only [next] using hnextOdd) hkOdd
    rw [← hpivotValue] at hle
    exact lt_of_le_of_ne hle (by
      intro heq
      have hkMem : k ∈ pivotSet := by
        simp only [pivotSet, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hpivotInterval.1.trans hpivotK.le, hkLast⟩, hkOdd,
          heq.symm.trans hpivotValue⟩
      exact (not_le_of_gt hpivotK) (pivotSet.le_max' k hkMem))
  have hhead (k : Nat) (hnextK : next ≤ k)
      (hkPivot : k ≤ pivot) (hkOdd : Odd k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero pivot := by
    have hlower := horderMono next k le_rfl hnextK
      (hkPivot.trans hpivotInterval.2)
      (by simpa only [next] using hnextOdd) hkOdd
    have hupper := horderMono k pivot hnextK hkPivot hpivotInterval.2
      hkOdd hpivotOdd
    rw [hpivotValue] at hupper
    exact (le_antisymm hupper hlower).trans hpivotValue.symm
  exact ⟨{
    pivot := pivot
    next_le_pivot := by simpa only [next] using hpivotInterval.1
    pivot_le_last_previous := by
      simpa only [lastPrevious] using hpivotInterval.2
    pivot_odd := hpivotOdd
    current_eq_initial := by simpa only [next] using hpivotValue
    later_current_gt := by
      intro k hpivotK hkLast hkOdd
      exact hlater k hpivotK (by simpa only [lastPrevious] using hkLast)
        hkOdd
    head_current_eq := by
      intro k hnextK hkPivot hkOdd
      exact hhead k (by simpa only [next] using hnextK) hkPivot hkOdd }⟩

end BONG.GoodBONG

end Bong
