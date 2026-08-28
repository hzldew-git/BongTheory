/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityPrimary

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the current-order contradiction

This file isolates the use of Lemma 6.6(ii) in the second parity branch.
If the third current order were below the target current order, parity and
the first-order bound would force an even third prefix, contradicting the
odd prefix supplied by the branch hypothesis.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- If a comparison prefix has odd order and its first factor has even
prefix sum, the second prefix sum is odd. -/
theorem caseSix_thirdPrefix_odd_of_comparison_odd_and_target_even
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (htarget : Even (b.orderSequence.prefixSum i.val)) :
    Odd (c.orderSequence.prefixSum i.val) := by
  have horder :
      ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val) =
        b.orderSequence.prefixSum i.val +
          c.orderSequence.prefixSum i.val := by
    rw [ordUnit_mul,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le,
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        i.val i.lt_large.le]
  rw [horder] at hcomparison
  rcases hcomparison with ⟨z, hz⟩
  rcases htarget with ⟨d, hd⟩
  exact ⟨z - d, by omega⟩

/-- Under the first-order upper bound, a strict reverse current comparison
forces the case-6 index to be even.  Otherwise good-BONG two-step
monotonicity contradicts the resulting drop below the third first order. -/
theorem caseSix_index_even_of_current_lt_and_orders_modEq
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hupper : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1)
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)))
    (hstrict : c.orderSequence.entryOrZero (i.val - 1) <
      b.orderSequence.entryOrZero i.val) :
    Even i.val := by
  have hordersRaw := horders
  rw [Int.modEq_iff_dvd] at hordersRaw
  rcases hordersRaw with ⟨d, hd⟩
  have hpreviousFirst : c.orderSequence.entryOrZero (i.val - 1) <
      c.orderSequence.entryOrZero 0 := by
    omega
  have hiPrevious : i.val - 1 < n + 2 :=
    lt_of_le_of_lt (Nat.sub_le i.val 1) i.lt_large
  rcases Nat.even_or_odd i.val with heven | hodd
  · exact heven
  · rcases hodd with ⟨r, hr⟩
    have hpreviousEven : Even ((i.val - 1) - 0) :=
      ⟨r, by omega⟩
    have hmonotone := c.orderSequence.entryOrZero_le_of_evenGap
      0 (i.val - 1) (by omega) hiPrevious hpreviousEven
    omega

/-- Lemma 6.6(ii) rules out a strict reverse current-order inequality when
the third prefix is odd and the target current order is at most one above
the third first order. -/
theorem caseSix_targetCurrent_le_thirdPrevious_of_modEq_and_prefix_odd
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hupper : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1)
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)))
    (hthirdPrefix : Odd (c.orderSequence.prefixSum i.val)) :
    b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero (i.val - 1) := by
  by_contra hnot
  have hstrict : c.orderSequence.entryOrZero (i.val - 1) <
      b.orderSequence.entryOrZero i.val := lt_of_not_ge hnot
  have hpreviousFirst : c.orderSequence.entryOrZero (i.val - 1) <
      c.orderSequence.entryOrZero 0 := by
    have hordersRaw := horders
    rw [Int.modEq_iff_dvd] at hordersRaw
    rcases hordersRaw with ⟨d, hd⟩
    omega
  have hiPrevious : i.val - 1 < n + 2 :=
    lt_of_le_of_lt (Nat.sub_le i.val 1) i.lt_large
  have hiEven := caseSix_index_even_of_current_lt_and_orders_modEq
    b c i hupper horders hstrict
  rcases hiEven with ⟨r, hr⟩
  have hiPositive : 0 < i.val := i.pos
  have hrPositive : 0 < r := by omega
  let first : Fin (n + 2) := ⟨0, by omega⟩
  let previous : Fin (n + 2) := ⟨i.val - 1, hiPrevious⟩
  have hfirstPrevious : first < previous := by
    change 0 < i.val - 1
    omega
  have hdistanceOdd : Odd (previous.val - first.val) := by
    refine ⟨r - 1, ?_⟩
    simp only [previous, first]
    omega
  have horder : c.order previous ≤ c.order first := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    simpa only [previous, first] using hpreviousFirst.le
  have hclosed := c.beli2019Lemma66_ii
    first previous hfirstPrevious hdistanceOdd horder
  have hclosedEq : c.orderSequence.closedSegmentSum 0 (i.val - 1) =
      c.orderSequence.prefixSum i.val := by
    simp [BeliOrderSequence.closedSegmentSum,
      BeliOrderSequence.prefixSum, Nat.sub_add_cancel i.pos]
  have hprefixEven : Even (c.orderSequence.prefixSum i.val) := by
    simpa only [first, previous, hclosedEq] using hclosed
  rcases hprefixEven with ⟨s, hs⟩
  rcases hthirdPrefix with ⟨t, ht⟩
  omega

/-- The current-order contradiction followed by the primary-candidate
argument proves the first subcase of the second parity branch. -/
theorem lemma79_caseSix_secondParity_of_prefix_odd_target_even_orders_modEq
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (c : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (htarget : Even (b.orderSequence.prefixSum i.val))
    (hupper : b.orderSequence.entryOrZero i.val ≤
      c.orderSequence.entryOrZero 0 + 1)
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hthirdPrefix :=
    caseSix_thirdPrefix_odd_of_comparison_odd_and_target_even
      b c i hcomparison htarget
  have hcurrent :=
    caseSix_targetCurrent_le_thirdPrevious_of_modEq_and_prefix_odd
      b c i hupper horders hthirdPrefix
  exact lemma79_caseSix_secondParity_of_prefix_odd_orders_modEq_current_le
    b c i hcomparison horders hcurrent

end BONG.GoodBONG

end Bong
