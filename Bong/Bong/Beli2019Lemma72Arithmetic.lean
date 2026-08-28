/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Classification

/-!
# Beli (2019), Lemma 7.2: finite parity arithmetic

This file isolates the finite-sum calculation used in all three branches of
Lemma 7.2.  A congruence for every entry of a half-open interval is summed,
and the result is attached to an already controlled prefix.
-/

namespace Bong

open scoped BigOperators

namespace BeliOrderSequence

/-- The prefix through `j` splits into the prefix through `i` and the
half-open interval `[i, j)`. -/
theorem prefixSum_eq_add_sum_Ico {n : Nat} (x : BeliOrderSequence n Int)
    {i j : Nat} (hij : i ≤ j) :
    x.prefixSum j = x.prefixSum i +
      ∑ k ∈ Finset.Ico i j, x.entryOrZero k := by
  unfold prefixSum
  exact (Finset.sum_range_add_sum_Ico x.entryOrZero hij).symm

/-- A constant congruence class on `[i, j)` gives the expected congruence
for the interval sum. -/
theorem sum_Ico_modEq_mul {n : Nat} (x : BeliOrderSequence n Int)
    (c : Int) {i j : Nat} (hij : i ≤ j)
    (hentry : ∀ k, i ≤ k → k < j →
      Int.ModEq 2 (x.entryOrZero k) c) :
    Int.ModEq 2 (∑ k ∈ Finset.Ico i j, x.entryOrZero k)
      ((j - i : Nat) * c) := by
  have hsum := int_modEq_two_sum_Ico x.entryOrZero (fun _ ↦ c)
    hij hentry
  simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using hsum

/-- Extend a controlled prefix across an interval whose entries all have
one parity. -/
theorem prefixSum_modEq_add_mul_of_tail {n : Nat}
    (x : BeliOrderSequence n Int) (base c : Int) {i j : Nat}
    (hij : i ≤ j) (hbase : Int.ModEq 2 (x.prefixSum i) base)
    (hentry : ∀ k, i ≤ k → k < j →
      Int.ModEq 2 (x.entryOrZero k) c) :
    Int.ModEq 2 (x.prefixSum j)
      (base + (j - i : Nat) * c) := by
  rw [x.prefixSum_eq_add_sum_Ico hij]
  exact hbase.add (x.sum_Ico_modEq_mul c hij hentry)

/-- If all entries before `i` lie in one congruence class, the first `i`
entries have the congruence class `i * c`. -/
theorem prefixSum_modEq_mul {n : Nat} (x : BeliOrderSequence n Int)
    (c : Int) (i : Nat)
    (hentry : ∀ k, k < i → Int.ModEq 2 (x.entryOrZero k) c) :
    Int.ModEq 2 (x.prefixSum i) ((i : Int) * c) := by
  have hzero : Int.ModEq 2 (x.prefixSum 0) 0 := by simp
  have hsum := x.prefixSum_modEq_add_mul_of_tail 0 c
    (i := 0) (j := i) (Nat.zero_le i) hzero (by
      intro k _ hk
      exact hentry k hk)
  simpa using hsum

end BeliOrderSequence

end Bong
