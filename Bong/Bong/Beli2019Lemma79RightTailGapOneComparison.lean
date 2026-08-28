/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneComplete
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityJumpWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 8: comparison-order growth

The gap-one proof repeatedly needs the same two consequences of Lemma 6.6.
For an even prefix with odd total order, an odd adjacent pair forces the
last order to lie strictly above a lower bound for the first order.  For an
odd prefix in the class `length * reference + 1`, equal first and last
orders would contradict Lemma 6.6(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- An odd even-length prefix forces its last entry to be strictly above
any common lower bound for the first entry. -/
theorem last_entry_ge_reference_add_one_of_even_prefix_odd
    (c : GoodBONG q L (n + 2)) (length : Nat) (reference : Int)
    (hlengthPos : 0 < length) (hlengthBound : length ≤ n + 2)
    (hlengthEven : Even length)
    (hprefix : Odd (c.orderSequence.prefixSum length))
    (hfirstLower : reference ≤ c.orderSequence.entryOrZero 0) :
    reference + 1 ≤ c.orderSequence.entryOrZero (length - 1) := by
  rcases c.exists_even_entryPair_sum_odd_of_prefixSum_odd
      length hlengthPos hlengthBound hlengthEven hprefix with
    ⟨j, hjEven, hjlt, hjOdd⟩
  have hjBound : j < n + 1 := by omega
  have hjNextBound : j + 1 < n + 2 := by omega
  have hjLower := c.orderSequence.entryOrZero_le_of_evenGap
    0 j (Nat.zero_le _) (by omega) hjEven
  have hreferenceJ : reference ≤ c.orderSequence.entryOrZero j :=
    hfirstLower.trans hjLower
  let gap : Fin (n + 1) := ⟨j, hjBound⟩
  have hgapFormula : c.orderGap gap =
      c.orderSequence.entryOrZero (j + 1) -
        c.orderSequence.entryOrZero j := by
    unfold orderGap
    rw [← c.orderSequence_entryOrZero_eq_order gap.succ,
      ← c.orderSequence_entryOrZero_eq_order gap.castSucc]
    simp only [gap, Fin.val_succ, Fin.val_castSucc]
  have hnextAbove : c.orderSequence.entryOrZero j <
      c.orderSequence.entryOrZero (j + 1) := by
    by_contra hnot
    have hgapNonpositive : c.orderGap gap ≤ 0 := by
      rw [hgapFormula]
      omega
    have hgapEven := c.orderGap_even_of_nonpositive gap hgapNonpositive
    have hgapOdd : Odd (c.orderGap gap) := by
      rcases hjOdd with ⟨d, hd⟩
      refine ⟨d - c.orderSequence.entryOrZero j, ?_⟩
      rw [hgapFormula]
      omega
    exact (Int.not_even_iff_odd.mpr hgapOdd) hgapEven
  have hjNextLast : j + 1 ≤ length - 1 := by omega
  have hdistanceEven : Even ((length - 1) - (j + 1)) := by
    rcases hlengthEven with ⟨d, hd⟩
    rcases hjEven with ⟨e, he⟩
    refine ⟨d - e - 1, ?_⟩
    omega
  have hlastBound : length - 1 < n + 2 := by omega
  have hnextLast := c.orderSequence.entryOrZero_le_of_evenGap
    (j + 1) (length - 1) hjNextLast hlastBound hdistanceEven
  omega

/-- For an odd-length prefix in the class `length * reference + 1`, the
last order is strictly above `reference` whenever the first order is not
smaller than `reference`. -/
theorem last_entry_ge_reference_add_one_of_odd_prefix_modEq
    (c : GoodBONG q L (n + 2)) (length : Nat) (reference : Int)
    (hlengthPos : 0 < length) (hlengthBound : length ≤ n + 2)
    (hlengthOdd : Odd length)
    (hprefix : Int.ModEq 2 (c.orderSequence.prefixSum length)
      ((length : Int) * reference + 1))
    (hfirstLower : reference ≤ c.orderSequence.entryOrZero 0) :
    reference + 1 ≤ c.orderSequence.entryOrZero (length - 1) := by
  have hlastBound : length - 1 < n + 2 := by omega
  have hdistanceEven : Even ((length - 1) - 0) := by
    rcases hlengthOdd with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    omega
  have hfirstLast := c.orderSequence.entryOrZero_le_of_evenGap
    0 (length - 1) (Nat.zero_le _) hlastBound hdistanceEven
  by_contra hnot
  have hfirstEq : c.orderSequence.entryOrZero 0 = reference := by omega
  have hlastEq : c.orderSequence.entryOrZero (length - 1) = reference := by
    omega
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let last : Fin (n + 2) := ⟨length - 1, hlastBound⟩
  have horders : c.order first = c.order last := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    simpa only [first, last] using hfirstEq.trans hlastEq.symm
  have H := c.beli2019Lemma66_i first last (by
      change 0 ≤ length - 1
      omega) (by simpa only [first, last] using hdistanceEven) horders
  have hclosedEq : c.orderSequence.closedSegmentSum 0 (length - 1) =
      c.orderSequence.prefixSum length := by
    simp [BeliOrderSequence.closedSegmentSum,
      BeliOrderSequence.prefixSum, Nat.sub_add_cancel hlengthPos]
  have hfirstOrder : c.order first = reference := by
    rw [← c.orderSequence_entryOrZero_eq_order]
    simpa only [first] using hfirstEq
  have hclosed := H.closedSum_modEq
  rw [hclosedEq, hfirstOrder] at hclosed
  have hcontradiction : Int.ModEq 2 reference
      ((length : Int) * reference + 1) := hclosed.symm.trans hprefix
  rcases hlengthOdd with ⟨d, hd⟩
  have hlengthMod : Int.ModEq 2 (length : Int) 1 := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    have hdInt : (length : Int) = 2 * (d : Int) + 1 := by
      exact_mod_cast hd
    omega
  have hreferenceShift : Int.ModEq 2
      ((length : Int) * reference + 1) (reference + 1) := by
    simpa only [one_mul] using
      (hlengthMod.mul_right reference).add
        (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
  have hbad : Int.ModEq 2 reference (reference + 1) :=
    hcontradiction.trans hreferenceShift
  rw [Int.modEq_iff_dvd] at hbad
  rcases hbad with ⟨z, hz⟩
  omega

end BONG.GoodBONG

end Bong
