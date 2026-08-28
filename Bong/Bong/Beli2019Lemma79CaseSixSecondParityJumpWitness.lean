/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpBound

/-!
# Beli (2019), Lemma 7.9(ii), case 6: odd-jump witnesses

This file formalizes the finite parity argument in the type-II part of the
second parity branch.  An odd even-length prefix contains an odd adjacent
pair.  The good-BONG two-step law and the parity of the final order then
move such a pair to one whose first order is strictly above the profile
reference value.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- An odd prefix consisting of complete even-odd pairs contains a pair
whose order sum is odd. -/
theorem exists_even_entryPair_sum_odd_of_prefixSum_odd_pairs
    (c : GoodBONG q L (n + 2)) (pairs : Nat)
    (hbound : 2 * pairs ≤ n + 2)
    (hprefix : Odd (c.orderSequence.prefixSum (2 * pairs))) :
    ∃ j : Nat, Even j ∧ j + 1 < 2 * pairs ∧
      Odd (c.orderSequence.entryOrZero j +
        c.orderSequence.entryOrZero (j + 1)) := by
  induction pairs with
  | zero =>
      simp only [Nat.mul_zero, BeliOrderSequence.prefixSum_zero] at hprefix
      rcases hprefix with ⟨d, hd⟩
      omega
  | succ pairs ih =>
      let start := 2 * pairs
      have hlength : 2 * (pairs + 1) = start + 2 := by
        simp only [start]
        omega
      have hsum := c.orderSequence.prefixSum_add_two start
      rw [← hlength] at hsum
      let pairSum := c.orderSequence.entryOrZero start +
        c.orderSequence.entryOrZero (start + 1)
      have hsum' : c.orderSequence.prefixSum (2 * (pairs + 1)) =
          c.orderSequence.prefixSum (2 * pairs) + pairSum := by
        simpa only [start, pairSum] using hsum
      rcases Int.even_or_odd pairSum with hpairEven | hpairOdd
      · have hpreviousOdd :
            Odd (c.orderSequence.prefixSum (2 * pairs)) := by
          rcases hprefix with ⟨d, hd⟩
          rcases hpairEven with ⟨e, he⟩
          refine ⟨d - e, ?_⟩
          rw [hsum'] at hd
          omega
        have hpreviousBound : 2 * pairs ≤ n + 2 := by omega
        rcases ih hpreviousBound hpreviousOdd with
          ⟨j, hjEven, hjlt, hjOdd⟩
        exact ⟨j, hjEven, by omega, hjOdd⟩
      · refine ⟨start, ⟨pairs, by simp only [start]; omega⟩, ?_, ?_⟩
        · simp only [start]
          omega
        · simpa only [pairSum] using hpairOdd

/-- The preceding result with an arbitrary positive even prefix length. -/
theorem exists_even_entryPair_sum_odd_of_prefixSum_odd
    (c : GoodBONG q L (n + 2)) (length : Nat)
    (hlengthPos : 0 < length) (hlengthBound : length ≤ n + 2)
    (hlengthEven : Even length)
    (hprefix : Odd (c.orderSequence.prefixSum length)) :
    ∃ j : Nat, Even j ∧ j + 1 < length ∧
      Odd (c.orderSequence.entryOrZero j +
        c.orderSequence.entryOrZero (j + 1)) := by
  rcases hlengthEven with ⟨pairs, hpairs⟩
  have hlength : length = 2 * pairs := by omega
  have hbound : 2 * pairs ≤ n + 2 := by omega
  have hprefix' : Odd (c.orderSequence.prefixSum (2 * pairs)) := by
    rw [← hlength]
    exact hprefix
  rcases c.exists_even_entryPair_sum_odd_of_prefixSum_odd_pairs
      pairs hbound hprefix' with ⟨j, hjEven, hjlt, hjOdd⟩
  exact ⟨j, hjEven, by omega, hjOdd⟩

/-- An odd sum prevents its two summands from being congruent modulo two. -/
theorem caseSix_not_modEq_two_of_add_odd {x y : Int}
    (hodd : Odd (x + y)) : ¬ Int.ModEq 2 x y := by
  intro hmod
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨d, hd⟩
  rcases hodd with ⟨e, he⟩
  omega

/-- Two integers not congruent modulo two have odd sum. -/
theorem caseSix_odd_add_of_not_modEq_two {x y : Int}
    (hnot : ¬ Int.ModEq 2 x y) : Odd (x + y) := by
  rcases Int.even_or_odd (x + y) with heven | hodd
  · apply False.elim
    apply hnot
    apply int_modEq_two_of_even_sub
    rcases heven with ⟨d, hd⟩
    exact ⟨d - y, by omega⟩
  · exact hodd

/-- Upgrade an odd pair in an even prefix to an odd pair whose first order
is strictly above `reference`.  The final order has the parity of
`reference`, so the opposite parity class must end before `final`. -/
theorem exists_odd_entryPair_above_reference_of_even_prefix_odd
    (c : GoodBONG q L (n + 2)) (length final : Nat)
    (reference : Int)
    (hlengthPos : 0 < length) (hlengthBound : length ≤ n + 2)
    (hlengthEven : Even length)
    (hprefix : Odd (c.orderSequence.prefixSum length))
    (hfinalBound : final < n + 2)
    (hlengthFinal : length - 1 ≤ final)
    (hfirstLower : reference ≤ c.orderSequence.entryOrZero 0)
    (hfinalMod : Int.ModEq 2
      (c.orderSequence.entryOrZero final) reference) :
    ∃ k : Nat, k + 1 ≤ final ∧
      Odd (c.orderSequence.entryOrZero k +
        c.orderSequence.entryOrZero (k + 1)) ∧
      reference < c.orderSequence.entryOrZero k := by
  classical
  rcases c.exists_even_entryPair_sum_odd_of_prefixSum_odd
      length hlengthPos hlengthBound hlengthEven hprefix with
    ⟨j, hjEven, hjlt, hjPairOdd⟩
  have hjBound : j < n + 1 := by omega
  have hjNextBound : j + 1 < n + 2 := by omega
  have hjFinal : j + 1 ≤ final := by omega
  have hjMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 j (Nat.zero_le _) (by omega) hjEven
  have hreferenceJ : reference ≤ c.orderSequence.entryOrZero j :=
    hfirstLower.trans hjMonotone
  by_cases hjAbove : reference < c.orderSequence.entryOrZero j
  · exact ⟨j, hjFinal, hjPairOdd, hjAbove⟩
  · have hjEq : c.orderSequence.entryOrZero j = reference := by omega
    let gap : Fin (n + 1) := ⟨j, hjBound⟩
    have hgapFormula : c.orderGap gap =
        c.orderSequence.entryOrZero (j + 1) -
          c.orderSequence.entryOrZero j := by
      unfold orderGap
      rw [← c.orderSequence_entryOrZero_eq_order gap.succ,
        ← c.orderSequence_entryOrZero_eq_order gap.castSucc]
      simp only [gap, Fin.val_succ, Fin.val_castSucc]
    have hjNextAbove : reference <
        c.orderSequence.entryOrZero (j + 1) := by
      by_contra hnot
      have hgapNonpositive : c.orderGap gap ≤ 0 := by
        rw [hgapFormula]
        omega
      have hgapEven := c.orderGap_even_of_nonpositive gap hgapNonpositive
      have hgapOdd : Odd (c.orderGap gap) := by
        rw [hgapFormula, hjEq]
        rcases hjPairOdd with ⟨d, hd⟩
        exact ⟨d - reference, by omega⟩
      exact (Int.not_even_iff_odd.mpr hgapOdd) hgapEven
    have hjNextNeFinal : j + 1 ≠ final := by
      intro heq
      have hnextMod : Int.ModEq 2
          (c.orderSequence.entryOrZero (j + 1)) reference := by
        simpa only [heq] using hfinalMod
      have hpairNot := caseSix_not_modEq_two_of_add_odd hjPairOdd
      apply hpairNot
      simpa only [hjEq] using hnextMod.symm
    have hjTwoFinal : j + 2 ≤ final := by omega
    have hjTwoBound : j + 2 < n + 2 := hjTwoFinal.trans_lt hfinalBound
    have hjTwoLower := c.orderSequence.entryOrZero_le_of_evenGap
      j (j + 2) (by omega) hjTwoBound ⟨1, by omega⟩
    have hjTwoAbove : reference <
        c.orderSequence.entryOrZero (j + 2) := by
      by_contra hnot
      have hjTwoEq : c.orderSequence.entryOrZero (j + 2) = reference := by
        omega
      have hmiddleMod := c.entryOrZero_modEq_of_equal_even_endpoints
        (i := j) (j := j + 2) (k := j + 1)
        (by omega) hjTwoBound (by omega) (by omega) hjNextBound
        ⟨1, by omega⟩ (by omega)
      exact (caseSix_not_modEq_two_of_add_odd hjPairOdd)
        (by simpa only [hjEq] using hmiddleMod.symm)
    let start := j + 1
    have hstartFinal : start < final := by
      simp only [start]
      omega
    have hstartNotReference : ¬ Int.ModEq 2
        (c.orderSequence.entryOrZero start) reference := by
      intro hmod
      exact (caseSix_not_modEq_two_of_add_odd hjPairOdd) (by
        simpa only [start, hjEq] using hmod.symm)
    have hfinalNotStart : ¬ Int.ModEq 2
        (c.orderSequence.entryOrZero final)
        (c.orderSequence.entryOrZero start) := by
      intro hmod
      exact hstartNotReference (hmod.symm.trans hfinalMod)
    let P : Nat → Prop := fun t ↦ start < t ∧ t ≤ final ∧
      ¬ Int.ModEq 2 (c.orderSequence.entryOrZero t)
        (c.orderSequence.entryOrZero start)
    have hP : ∃ t, P t := ⟨final, hstartFinal, le_rfl,
      hfinalNotStart⟩
    let transition := Nat.find hP
    have htransition : P transition := Nat.find_spec hP
    let k := transition - 1
    have hkNext : k + 1 = transition := by
      simp only [k]
      omega
    have hstartK : start ≤ k := by
      simp only [k]
      omega
    have hkNextFinal : k + 1 ≤ final := by
      rw [hkNext]
      exact htransition.2.1
    have hkBound : k < n + 2 := by omega
    have hkModStart : Int.ModEq 2
        (c.orderSequence.entryOrZero k)
        (c.orderSequence.entryOrZero start) := by
      by_cases heq : k = start
      · rw [heq]
      · apply Classical.byContradiction
        intro hnot
        have hkLtTransition : k < transition := by
          rw [← hkNext]
          omega
        have hkP : P k := ⟨lt_of_le_of_ne hstartK (Ne.symm heq),
          by omega, hnot⟩
        have hminimal := Nat.find_min' hP hkP
        omega
    have hkNotNext : ¬ Int.ModEq 2
        (c.orderSequence.entryOrZero k)
        (c.orderSequence.entryOrZero (k + 1)) := by
      intro hmod
      have hnextStart := hmod.symm.trans hkModStart
      rw [hkNext] at hnextStart
      exact htransition.2.2 hnextStart
    have hkPairOdd := caseSix_odd_add_of_not_modEq_two hkNotNext
    have hkAbove : reference < c.orderSequence.entryOrZero k := by
      rcases Nat.even_or_odd (k - start) with hdistanceEven |
          hdistanceOdd
      · have hmono := c.orderSequence.entryOrZero_le_of_evenGap
          start k hstartK hkBound hdistanceEven
        exact hjNextAbove.trans_le (by simpa only [start] using hmono)
      · rcases hdistanceOdd with ⟨d, hd⟩
        have hjTwoK : j + 2 ≤ k := by
          simp only [start] at hstartK hd
          omega
        have hdistanceEven : Even (k - (j + 2)) := ⟨d, by
          simp only [start] at hd
          omega⟩
        have hmono := c.orderSequence.entryOrZero_le_of_evenGap
          (j + 2) k hjTwoK hkBound hdistanceEven
        exact hjTwoAbove.trans_le hmono
    exact ⟨k, hkNextFinal, hkPairOdd, hkAbove⟩

end BONG.GoodBONG

end Bong
