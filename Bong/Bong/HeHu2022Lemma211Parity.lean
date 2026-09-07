/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSums

/-!
# He--Hu (2024), Lemma 2.11: the tail-pair parity argument

This file isolates the finite parity step in the exceptional branch of
Lemma 2.11.  If an even-length interval has odd cumulative sum, one of its
consecutive pairs has odd sum.  The formulation uses prefix differences, so
it applies directly to the order sequence of a good BONG without reindexing
the surrounding lattice.
-/

namespace Bong

namespace BeliOrderSequence

/-- A prefix whose entries are all even has even cumulative sum. -/
theorem prefixSum_even_of_entries_even
    {n : Nat} (x : BeliOrderSequence n Int) (length : Nat)
    (heven : ∀ k : Nat, k < length → Even (x.entryOrZero k)) :
    Even (x.prefixSum length) := by
  induction length with
  | zero =>
      simpa only [prefixSum_zero] using (Even.zero : Even (0 : Int))
  | succ length ih =>
      rw [show length + 1 = length + 1 by rfl, x.prefixSum_succ]
      exact (ih (fun k hk ↦ heven k (by omega))).add
        (heven length (by omega))

/-- An odd prefix-sum difference across `pairs` consecutive pairs contains
an odd pair.  The witness starts an even distance from `start`. -/
theorem exists_pair_sum_odd_of_prefixDifference_odd_pairs
    {n : Nat} (x : BeliOrderSequence n Int) (start pairs : Nat)
    (hodd : Odd
      (x.prefixSum (start + 2 * pairs) - x.prefixSum start)) :
    ∃ j : Nat, start ≤ j ∧ j + 1 < start + 2 * pairs ∧
      Even (j - start) ∧
      Odd (x.entryOrZero j + x.entryOrZero (j + 1)) := by
  induction pairs with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, sub_self] at hodd
      exact (Int.not_odd_iff_even.mpr Even.zero hodd).elim
  | succ pairs ih =>
      let pairStart := start + 2 * pairs
      let pairSum := x.entryOrZero pairStart +
        x.entryOrZero (pairStart + 1)
      have hend : start + 2 * (pairs + 1) = pairStart + 2 := by
        simp only [pairStart]
        omega
      have hsum :
          x.prefixSum (start + 2 * (pairs + 1)) - x.prefixSum start =
            (x.prefixSum (start + 2 * pairs) - x.prefixSum start) +
              pairSum := by
        rw [hend, x.prefixSum_add_two]
        simp only [pairStart, pairSum]
        omega
      rcases Int.even_or_odd pairSum with hpairEven | hpairOdd
      · have hpreviousOdd : Odd
            (x.prefixSum (start + 2 * pairs) - x.prefixSum start) := by
          rcases hodd with ⟨d, hd⟩
          rcases hpairEven with ⟨e, he⟩
          refine ⟨d - e, ?_⟩
          rw [hsum] at hd
          omega
        rcases ih hpreviousOdd with
          ⟨j, hjStart, hjEnd, hjDistance, hjOdd⟩
        exact ⟨j, hjStart, by omega, hjDistance, hjOdd⟩
      · refine ⟨pairStart, by simp only [pairStart]; omega, ?_, ?_, ?_⟩
        · simp only [pairStart]
          omega
        · simp only [pairStart, Nat.add_sub_cancel_left]
          exact ⟨pairs, by omega⟩
        · simpa only [pairSum] using hpairOdd

/-- If the interval starts at an odd index, the odd pair furnished above
also starts at an odd index. -/
theorem exists_odd_pair_sum_odd_of_prefixDifference_odd
    {n : Nat} (x : BeliOrderSequence n Int) (start stop : Nat)
    (hstartOdd : Odd start) (hlengthEven : Even (stop - start))
    (hstartStop : start < stop)
    (hodd : Odd (x.prefixSum stop - x.prefixSum start)) :
    ∃ j : Nat, Odd j ∧ start ≤ j ∧ j + 1 < stop ∧
      Odd (x.entryOrZero j + x.entryOrZero (j + 1)) := by
  rcases hlengthEven with ⟨pairs, hpairs⟩
  have hstop : stop = start + 2 * pairs := by omega
  have hpairsPositive : 0 < pairs := by omega
  have hodd' : Odd
      (x.prefixSum (start + 2 * pairs) - x.prefixSum start) := by
    rw [← hstop]
    exact hodd
  rcases x.exists_pair_sum_odd_of_prefixDifference_odd_pairs
      start pairs hodd' with
    ⟨j, hjStart, hjEnd, hjDistanceEven, hjPairOdd⟩
  have hjOdd : Odd j := by
    rcases hstartOdd with ⟨s, hs⟩
    rcases hjDistanceEven with ⟨d, hd⟩
    refine ⟨s + d, ?_⟩
    omega
  exact ⟨j, hjOdd, hjStart, by rw [hstop]; exact hjEnd, hjPairOdd⟩

end BeliOrderSequence

end Bong
