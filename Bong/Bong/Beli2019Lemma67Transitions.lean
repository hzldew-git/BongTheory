/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Bounds

/-!
# Beli (2019), Lemma 6.7: prefix-gap transitions

In the branch with no pointwise gap two, let `firstTwo` be the first prefix
whose cumulative gap is two and `lastZero` the last zero-gap prefix before
it.  The two indices are separated, every intermediate prefix gap is one,
the two boundary entries rise by one, and all entries strictly between the
boundaries agree.  These are the central order identities in the type-II/III
part of Lemma 6.7.
-/

namespace Bong

namespace BeliOrderSequence

/-- The target-minus-source cumulative order gap after `k` entries. -/
def prefixGap {n : Nat} (x y : BeliOrderSequence n Int) (k : Nat) : Int :=
  y.prefixSum k - x.prefixSum k

@[simp]
theorem prefixGap_zero {n : Nat} (x y : BeliOrderSequence n Int) :
    x.prefixGap y 0 = 0 := by
  simp [prefixGap]

/-- The increment of the prefix gap is the pointwise entry difference. -/
theorem prefixGap_succ {n : Nat} (x y : BeliOrderSequence n Int)
    (k : Nat) :
    x.prefixGap y (k + 1) = x.prefixGap y k +
      (y.entryOrZero k - x.entryOrZero k) := by
  simp only [prefixGap, x.prefixSum_succ, y.prefixSum_succ]
  ring

end BeliOrderSequence

namespace BeliOrderLE

/-- The finite transition package for the no-gap-two branch of Lemma 6.7. -/
structure PrefixGapTransitionConsequences {n : Nat}
    (x y : BeliOrderSequence n Int) where
  lastZero : Nat
  firstTwo : Nat
  firstTwo_le_rank : firstTwo ≤ n
  lastZero_lt_firstTwo : lastZero < firstTwo
  gap_lastZero : x.prefixGap y lastZero = 0
  gap_firstTwo : x.prefixGap y firstTwo = 2
  gap_between (k : Nat) (hlast : lastZero < k)
      (hfirst : k < firstTwo) :
    x.prefixGap y k = 1
  separated : lastZero + 1 < firstTwo
  leftBoundary :
    y.entryOrZero lastZero = x.entryOrZero lastZero + 1
  rightBoundary :
    y.entryOrZero (firstTwo - 1) =
      x.entryOrZero (firstTwo - 1) + 1
  middle (k : Nat) (hlast : lastZero < k)
      (hfirst : k + 1 < firstTwo) :
    x.entryOrZero k = y.entryOrZero k

/-- Construction of the prefix-gap transition package. -/
theorem prefixGapTransitionConsequences {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (hnoTwo : ∀ k, k < n →
      y.entryOrZero k ≠ x.entryOrZero k + 2) :
    Nonempty (PrefixGapTransitionConsequences x y) := by
  classical
  let twos := (Finset.range (n + 1)).filter fun k ↦
    x.prefixGap y k = 2
  have hgapN : x.prefixGap y n = 2 := by
    unfold BeliOrderSequence.prefixGap
    omega
  have hnMem : n ∈ twos := by
    simp only [twos, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hgapN⟩
  have htwos : twos.Nonempty := ⟨n, hnMem⟩
  let firstTwo := twos.min' htwos
  have hfirstMem : firstTwo ∈ twos := twos.min'_mem htwos
  have hfirstData := Finset.mem_filter.mp hfirstMem
  have hfirstBound : firstTwo ≤ n := by
    have := Finset.mem_range.mp hfirstData.1
    omega
  have hfirstGap : x.prefixGap y firstTwo = 2 := hfirstData.2
  have hfirstPos : 0 < firstTwo := by
    by_contra hnot
    have hzero : firstTwo = 0 := by omega
    rw [hzero, BeliOrderSequence.prefixGap_zero] at hfirstGap
    omega
  have hbeforeFirst (k : Nat) (hk : k < firstTwo) :
      x.prefixGap y k = 0 ∨ x.prefixGap y k = 1 := by
    have hkRank : k ≤ n := by omega
    rcases h.prefixGap_trichotomy_of_totalGap htotal k hkRank with
      hzero | hone | htwo
    · exact Or.inl hzero
    · exact Or.inr hone
    · have hkMem : k ∈ twos := by
        simp only [twos, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, htwo⟩
      exact ((not_le_of_gt hk) (twos.min'_le k hkMem)).elim
  let zeros := (Finset.range (firstTwo + 1)).filter fun k ↦
    x.prefixGap y k = 0
  have hzeroMem : 0 ∈ zeros := by
    simp [zeros]
  have hzeros : zeros.Nonempty := ⟨0, hzeroMem⟩
  let lastZero := zeros.max' hzeros
  have hlastMem : lastZero ∈ zeros := zeros.max'_mem hzeros
  have hlastData := Finset.mem_filter.mp hlastMem
  have hlastBound : lastZero ≤ firstTwo := by
    have := Finset.mem_range.mp hlastData.1
    omega
  have hlastGap : x.prefixGap y lastZero = 0 := hlastData.2
  have hlastLt : lastZero < firstTwo := by
    exact lt_of_le_of_ne hlastBound (by
      intro heq
      rw [heq, hfirstGap] at hlastGap
      omega)
  have hbetween (k : Nat) (hlast : lastZero < k)
      (hfirst : k < firstTwo) : x.prefixGap y k = 1 := by
    rcases hbeforeFirst k hfirst with hzero | hone
    · have hkMem : k ∈ zeros := by
        simp only [zeros, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hzero⟩
      exact ((not_le_of_gt hlast) (zeros.le_max' k hkMem)).elim
    · exact hone
  have hseparated : lastZero + 1 < firstTwo := by
    by_contra hnot
    have heq : firstTwo = lastZero + 1 := by omega
    have hstep := x.prefixGap_succ y lastZero
    rw [← heq, hfirstGap, hlastGap] at hstep
    have hlastRank : lastZero < n := by omega
    exact hnoTwo lastZero hlastRank (by omega)
  have hleftGap : x.prefixGap y (lastZero + 1) = 1 :=
    hbetween (lastZero + 1) (by omega) hseparated
  have hleftStep := x.prefixGap_succ y lastZero
  rw [hleftGap, hlastGap] at hleftStep
  have hleftEntry :
      y.entryOrZero lastZero = x.entryOrZero lastZero + 1 := by
    omega
  have hrightPrevious :
      x.prefixGap y (firstTwo - 1) = 1 := by
    apply hbetween (firstTwo - 1)
    · omega
    · omega
  have hrightStep := x.prefixGap_succ y (firstTwo - 1)
  have hrightIndex : firstTwo - 1 + 1 = firstTwo := by omega
  rw [hrightIndex, hfirstGap, hrightPrevious] at hrightStep
  have hrightEntry :
      y.entryOrZero (firstTwo - 1) =
        x.entryOrZero (firstTwo - 1) + 1 := by
    omega
  refine ⟨{
    lastZero := lastZero
    firstTwo := firstTwo
    firstTwo_le_rank := hfirstBound
    lastZero_lt_firstTwo := hlastLt
    gap_lastZero := hlastGap
    gap_firstTwo := hfirstGap
    gap_between := hbetween
    separated := hseparated
    leftBoundary := hleftEntry
    rightBoundary := hrightEntry
    middle := ?_ }⟩
  intro k hlast hfirst
  have hcurrent := hbetween k hlast (by omega)
  have hnext := hbetween (k + 1) (by omega) hfirst
  have hstep := x.prefixGap_succ y k
  rw [hnext, hcurrent] at hstep
  omega

end BeliOrderLE

end Bong
