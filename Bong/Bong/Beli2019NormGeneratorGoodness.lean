/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ProjectionNormIdeal
import Bong.Bong.BeliLemma411

/-!
# Beli (2019), Corollary 5.9(ii): extending norm generators

This file proves the three sufficient conditions in Corollary 5.9(ii).
The first two arguments are isolated first at the level of Beli order
sequences.  They are then transferred to a prescribed BONG whose tail is
already good through `NormGeneratorComparisonData`.
-/

namespace Bong

open Dyadic

namespace BeliOrderLE

/-- If the target's first odd one-based plateau ends immediately, the
candidate and target have the same second order. -/
theorem second_eq_of_first_lt_third {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (hn : 3 ≤ n)
    (hfirstThird : y.entryOrZero 0 < y.entryOrZero 2)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    x.entryOrZero 1 = y.entryOrZero 1 := by
  let k := y.maximalInitialOddPlateauIndex (by omega)
  have hplateau := y.maximalInitialOddPlateauIndex_spec (by omega)
  have hkZero : k = 0 := by
    by_contra hk
    have hkOne : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have heq := hplateau.eq_zero 1 hkOne
    have heq' : y.entryOrZero 2 = y.entryOrZero 0 := by
      simpa using heq
    exact (ne_of_gt hfirstThird) heq'
  have hprofile := h.normGeneratorOrderProfile k hplateau htail
  rw [hkZero] at hprofile
  exact hprofile.stable_after 1 (by omega) (by omega)

/-- If the target has equal first and third orders and target second gap
`t`, the universal source-gap bound `-t` forces equality at the second
coordinate. -/
theorem second_eq_of_target_gap {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (hn : 3 ≤ n)
    (hfirstThird : y.entryOrZero 0 = y.entryOrZero 2)
    (htargetGap : y.entryOrZero 1 - y.entryOrZero 0 = t)
    (htail : x.suffixSum 1 = y.suffixSum 1)
    (hsourceLower : -t ≤ x.entryOrZero 2 - x.entryOrZero 1) :
    x.entryOrZero 1 = y.entryOrZero 1 := by
  let k := y.maximalInitialOddPlateauIndex (by omega)
  have hplateau := y.maximalInitialOddPlateauIndex_spec (by omega)
  have hkOne : 1 ≤ k := by
    apply hplateau.maximal 1 (by omega)
    simpa using hfirstThird.symm
  have hprofile := h.normGeneratorOrderProfile k hplateau htail
  have hpair := hprofile.pair_sum 1 (by omega) (by omega) ⟨0, by omega⟩
  have hpair' :
      x.entryOrZero 1 + x.entryOrZero 2 =
        y.entryOrZero 1 + y.entryOrZero 2 := by
    simpa using hpair
  have hcriterion := h.secondOrderCriterion k (by omega) hplateau htail
  apply le_antisymm
  · by_contra hnot
    have hstrict : y.entryOrZero 1 < x.entryOrZero 1 :=
      lt_of_not_ge hnot
    omega
  · exact hcriterion.second_le

end BeliOrderLE

namespace BONG.NormGeneratorComparisonData

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  {b : GoodBONG q L (n + 3)} {c : BONG V q L (n + 3)}
  {x : BeliOrderSequence (n + 3) Int}

private theorem orderSequence_entryOrZero {m : Nat}
    (b : GoodBONG q L m) (i : Nat) (hi : i < m) :
    b.orderSequence.entryOrZero i = b.order ⟨i, hi⟩ := by
  calc
    b.orderSequence.entryOrZero i = b.orderSequence.entry i hi :=
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi
    _ = b.order ⟨i, hi⟩ := b.orderSequence_at i hi

/-- Corollary 5.9(ii), first case: `S₁ < S₃`. -/
theorem second_order_eq_of_first_lt_third
    (D : NormGeneratorComparisonData b c x)
    (hfirstThird : b.order 0 < b.order 2) :
    c.order 1 = b.order 1 := by
  have hsequence :
      b.orderSequence.entryOrZero 0 <
        b.orderSequence.entryOrZero 2 := by
    calc
      b.orderSequence.entryOrZero 0 = b.order 0 :=
        orderSequence_entryOrZero b 0 (by omega)
      _ < b.order 2 := hfirstThird
      _ = b.orderSequence.entryOrZero 2 :=
        (orderSequence_entryOrZero b 2 (by omega)).symm
  have hsecond := D.order_le.second_eq_of_first_lt_third
    (by omega) hsequence D.tail_sum
  rw [D.source_second_eq, D.target_second_eq] at hsecond
  exact hsecond

/-- Under `S₁ < S₃`, every candidate supplied by the norm-generator
construction is a good BONG. -/
theorem isGood_of_first_lt_third
    (D : NormGeneratorComparisonData b c x)
    (hfirstThird : b.order 0 < b.order 2) : c.IsGood :=
  D.isGood_of_second_order_eq
    (D.second_order_eq_of_first_lt_third hfirstThird)

/-- Corollary 5.9(ii), second case: `S₂ - S₁ = 2e`. -/
theorem second_order_eq_of_second_gap_eq_two_mul_e
    (D : NormGeneratorComparisonData b c x)
    (hgap : b.order 1 - b.order 0 =
      2 * (ramificationIndex K : Int)) :
    c.order 1 = b.order 1 := by
  let i0 : Fin (n + 3) := ⟨0, by omega⟩
  have hi0 : i0.val + 2 < n + 3 := by
    simp only [i0]
    omega
  have hfirstThirdLE : b.order 0 ≤ b.order 2 := by
    have hg := b.good i0 hi0
    have hi0eq : i0 = (0 : Fin (n + 3)) := by
      apply Fin.ext
      simp [i0]
    have hi2eq :
        (⟨i0.val + 2, hi0⟩ : Fin (n + 3)) =
          (2 : Fin (n + 3)) := by
      apply Fin.ext
      change i0.val + 2 = 2 % (n + 3)
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hi2eq, hi0eq] at hg
    exact hg
  rcases lt_or_eq_of_le hfirstThirdLE with hfirstThird | hfirstThird
  · exact D.second_order_eq_of_first_lt_third hfirstThird
  · have hsequenceFirstThird :
        b.orderSequence.entryOrZero 0 =
          b.orderSequence.entryOrZero 2 := by
      calc
        b.orderSequence.entryOrZero 0 = b.order 0 :=
          orderSequence_entryOrZero b 0 (by omega)
        _ = b.order 2 := hfirstThird
        _ = b.orderSequence.entryOrZero 2 :=
          (orderSequence_entryOrZero b 2 (by omega)).symm
    have hsequenceGap :
        b.orderSequence.entryOrZero 1 -
          b.orderSequence.entryOrZero 0 =
          2 * (ramificationIndex K : Int) := by
      rw [orderSequence_entryOrZero b 1 (by omega),
        orderSequence_entryOrZero b 0 (by omega)]
      exact hgap
    let i1 : Fin (n + 3) := ⟨1, by omega⟩
    have hi1 : i1.val + 1 < n + 3 := by
      simp only [i1]
      omega
    have hcLower :
        -(2 * (ramificationIndex K : Int)) ≤
          c.order (2 : Fin (n + 3)) - c.order (1 : Fin (n + 3)) := by
      have hg := c.adjacentOrderGap_ge_neg_two_mul_e i1 hi1
      have hi1eq : i1 = (1 : Fin (n + 3)) := by
        apply Fin.ext
        simp [i1]
      have hi2eq :
          (⟨i1.val + 1, hi1⟩ : Fin (n + 3)) =
            (2 : Fin (n + 3)) := by
        apply Fin.ext
        change i1.val + 1 = 2 % (n + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hi2eq, hi1eq] at hg
      exact hg
    have hxTwo : x.entryOrZero 2 = c.order (2 : Fin (n + 3)) := by
      simpa using D.tail_order (1 : Fin (n + 2))
    have hxOne : x.entryOrZero 1 = c.order (1 : Fin (n + 3)) := by
      simpa using D.tail_order (0 : Fin (n + 2))
    have hxLower :
        -(2 * (ramificationIndex K : Int)) ≤
          x.entryOrZero 2 - x.entryOrZero 1 := by
      rw [hxTwo, hxOne]
      simpa using hcLower
    have hsecond := D.order_le.second_eq_of_target_gap
      (by omega) hsequenceFirstThird hsequenceGap D.tail_sum hxLower
    rw [D.source_second_eq, D.target_second_eq] at hsecond
    exact hsecond

/-- Under `S₂ - S₁ = 2e`, every candidate supplied by the norm-generator
construction is a good BONG. -/
theorem isGood_of_second_gap_eq_two_mul_e
    (D : NormGeneratorComparisonData b c x)
    (hgap : b.order 1 - b.order 0 =
      2 * (ramificationIndex K : Int)) : c.IsGood :=
  D.isGood_of_second_order_eq
    (D.second_order_eq_of_second_gap_eq_two_mul_e hgap)

end BONG.NormGeneratorComparisonData

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Corollary 5.9(ii), third case: every BONG of rank at most two is good. -/
theorem isGood_of_corollary59_rank_le_two
    (b : BONG V q L n) (hn : n ≤ 2) : b.IsGood :=
  b.isGood_of_length_le_two hn

end BONG

end Bong
