/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SecondOrderCriterion

/-!
# Beli (2019), canonical maximal indices in Section 5

The paper repeatedly says to choose a maximal `k` or `l`.  This file makes
both choices canonical finite maxima and proves the exact certificates used
by Lemma 5.7 and Corollary 5.8.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Candidate indices for the initial odd one-based plateau. -/
def initialOddPlateauSet {n : Nat} (y : BeliOrderSequence n Gamma) :
    Finset Nat :=
  (Finset.range n).filter fun r =>
    2 * r < n ∧ y.entryOrZero (2 * r) = y.entryOrZero 0

omit [IsOrderedAddMonoid Gamma] in
theorem initialOddPlateauSet_nonempty {n : Nat}
    (y : BeliOrderSequence n Gamma) (hn : 0 < n) :
    (y.initialOddPlateauSet).Nonempty := by
  refine ⟨0, ?_⟩
  simp [initialOddPlateauSet, hn]

/-- The canonical maximal `k` with `S₁ = S₃ = ... = S_{2k+1}`. -/
noncomputable def maximalInitialOddPlateauIndex {n : Nat}
    (y : BeliOrderSequence n Gamma) (hn : 0 < n) : Nat :=
  y.initialOddPlateauSet.max' (y.initialOddPlateauSet_nonempty hn)

omit [IsOrderedAddMonoid Gamma] in
/-- The canonical plateau index satisfies the maximality package used in
Lemma 5.7. -/
theorem maximalInitialOddPlateauIndex_spec {n : Nat}
    (y : BeliOrderSequence n Gamma) (hn : 0 < n) :
    y.IsMaximalInitialOddPlateau (y.maximalInitialOddPlateauIndex hn) := by
  let k := y.maximalInitialOddPlateauIndex hn
  have hkMem : k ∈ y.initialOddPlateauSet := by
    exact y.initialOddPlateauSet.max'_mem
      (y.initialOddPlateauSet_nonempty hn)
  have hkData := Finset.mem_filter.mp hkMem
  have hkBound : 2 * k < n := hkData.2.1
  have hkEq : y.entryOrZero (2 * k) = y.entryOrZero 0 := hkData.2.2
  refine
    { bound := hkBound
      eq_zero := ?_
      maximal := ?_ }
  · intro r hrk
    have hrBound : 2 * r < n := by omega
    have hzeroR := y.entryOrZero_le_of_evenGap 0 (2 * r)
      (by omega) hrBound ⟨r, by omega⟩
    have hrK := y.entryOrZero_le_of_evenGap (2 * r) (2 * k)
      (by omega) hkBound ⟨k - r, by omega⟩
    exact le_antisymm (hrK.trans_eq hkEq) hzeroR
  · intro r hrBound hrEq
    apply y.initialOddPlateauSet.le_max' r
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), ⟨hrBound, hrEq⟩⟩

/-- Candidate positive tail indices whose odd one-based coordinate is below
the target's first coordinate. -/
def tailOddBelowFirstSet {n : Nat}
    (x y : BeliOrderSequence n Gamma) : Finset Nat :=
  (Finset.range n).filter fun r =>
    0 < r ∧ 2 * r < n ∧ x.entryOrZero (2 * r) < y.entryOrZero 0

/-- The canonical `l` of Corollary 5.8, with zero as the fallback when the
candidate set is empty. -/
noncomputable def maximalTailOddBelowFirstIndex {n : Nat}
    (x y : BeliOrderSequence n Gamma) : Nat :=
  if h : (x.tailOddBelowFirstSet y).Nonempty then
    (x.tailOddBelowFirstSet y).max' h
  else
    0

omit [IsOrderedAddMonoid Gamma] in
/-- The canonical threshold index satisfies the maximality package used in
Corollary 5.8. -/
theorem maximalTailOddBelowFirstIndex_spec {n : Nat}
    (x y : BeliOrderSequence n Gamma) (hn : 0 < n) :
    IsMaximalTailOddBelowFirst x y
      (x.maximalTailOddBelowFirstIndex y) := by
  by_cases hs : (x.tailOddBelowFirstSet y).Nonempty
  · rw [maximalTailOddBelowFirstIndex, dif_pos hs]
    let l := (x.tailOddBelowFirstSet y).max' hs
    have hlMem : l ∈ x.tailOddBelowFirstSet y :=
      (x.tailOddBelowFirstSet y).max'_mem hs
    have hlData := Finset.mem_filter.mp hlMem
    refine
      { bound := hlData.2.2.1
        below_or_zero := Or.inr hlData.2.2.2
        maximal := ?_ }
    intro r hlr hrBound
    by_contra hnot
    have hrLT : x.entryOrZero (2 * r) < y.entryOrZero 0 :=
      lt_of_not_ge hnot
    have hrMem : r ∈ x.tailOddBelowFirstSet y := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), ⟨by omega, hrBound, hrLT⟩⟩
    exact (not_le_of_gt hlr) ((x.tailOddBelowFirstSet y).le_max' r hrMem)
  · rw [maximalTailOddBelowFirstIndex, dif_neg hs]
    refine
      { bound := by omega
        below_or_zero := Or.inl rfl
        maximal := ?_ }
    intro r hlr hrBound
    by_contra hnot
    have hrLT : x.entryOrZero (2 * r) < y.entryOrZero 0 :=
      lt_of_not_ge hnot
    apply hs
    refine ⟨r, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_range.mpr (by omega), ⟨hlr, hrBound, hrLT⟩⟩

end BeliOrderSequence

end Bong
