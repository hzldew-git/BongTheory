/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderGap

/-!
# Beli (2019), Lemma 6.7: fixed-gap bounds

This file formalizes the opening layer of Lemma 6.7.  For equal-rank order
sequences with total gap two, every target entry is at most two above the
matching source entry, every prefix gap lies between zero and two, and an
entry attaining the upper bound forces equality on the complementary prefix
and suffix.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem segmentSum_zero_left {n : Nat} (x : BeliOrderSequence n Gamma)
    (j : Nat) :
    x.segmentSum 0 j = x.prefixSum j := by
  simp [segmentSum]

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem segmentSum_singleton {n : Nat} (x : BeliOrderSequence n Gamma)
    (i : Nat) :
    x.segmentSum i (i + 1) = x.entryOrZero i := by
  rw [segmentSum, x.prefixSum_succ]
  exact sub_eq_iff_eq_add.mpr (add_comm _ _)

end BeliOrderSequence

namespace BeliOrderLE

/-- Lemma 5.5(iv), specialized to a singleton interval and total gap two. -/
theorem entryOrZero_le_add_two_of_totalGap {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (i : Nat) (hi : i < n) :
    y.entryOrZero i ≤ x.entryOrZero i + 2 := by
  have hsegment := h.segmentSum_le_add_totalGap htotal
    i (i + 1) (by omega) (by omega)
  simpa using hsegment

/-- Under total gap two, every prefix gap lies in the closed interval
`[0, 2]`. -/
theorem prefixGap_bounds_of_totalGap {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (k : Nat) (hk : k ≤ n) :
    0 ≤ y.prefixSum k - x.prefixSum k ∧
      y.prefixSum k - x.prefixSum k ≤ 2 := by
  have hlower := h.prefixSum_le k hk
  have hupper := h.segmentSum_le_add_totalGap htotal
    0 k (Nat.zero_le k) hk
  simp only [BeliOrderSequence.segmentSum_zero_left] at hupper
  omega

/-- Since the prefix gap is integral, its only possible values are zero,
one, and two. -/
theorem prefixGap_trichotomy_of_totalGap {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (k : Nat) (hk : k ≤ n) :
    y.prefixSum k - x.prefixSum k = 0 ∨
      y.prefixSum k - x.prefixSum k = 1 ∨
      y.prefixSum k - x.prefixSum k = 2 := by
  have hbounds := h.prefixGap_bounds_of_totalGap htotal k hk
  omega

/-- A strict pointwise increase is by one or two. -/
theorem entryOrZero_eq_add_one_or_two_of_lt {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (i : Nat) (hi : i < n)
    (hlt : x.entryOrZero i < y.entryOrZero i) :
    y.entryOrZero i = x.entryOrZero i + 1 ∨
      y.entryOrZero i = x.entryOrZero i + 2 := by
  have hupper := h.entryOrZero_le_add_two_of_totalGap htotal i hi
  omega

/-- Equality at the singleton upper bound is equivalent to equality of both
complementary sums.  This is the key split in Lemma 6.7. -/
theorem prefix_suffix_eq_of_entryOrZero_eq_add_two {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (i : Nat) (hi : i < n)
    (hentry : y.entryOrZero i = x.entryOrZero i + 2) :
    x.prefixSum i = y.prefixSum i ∧
      x.suffixSum (i + 1) = y.suffixSum (i + 1) := by
  apply (h.segmentSum_add_totalGap_eq_iff htotal
    i (i + 1) (by omega) (by omega)).mp
  simpa [add_comm] using hentry.symm

end BeliOrderLE

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Good-BONG form of the pointwise bound `S_i ≤ R_i + 2` used in
Lemma 6.7. -/
theorem targetOrder_le_sourceOrder_add_two_of_totalGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (i : Fin (n + 1)) :
    b.order i ≤ a.order i + 2 := by
  have hle := (a.representationOrderCondition_iff b le_rfl).mp horder
  have hbound := hle.entryOrZero_le_add_two_of_totalGap
    htotal i.val i.isLt
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt,
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence i.isLt] at hbound
  change b.order i ≤ a.order i + 2 at hbound
  exact hbound

/-- Good-BONG form of the prefix-gap trichotomy in Lemma 6.7. -/
theorem orderPrefixGap_trichotomy_of_totalGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (k : Nat) (hk : k ≤ n + 1) :
    b.orderSequence.prefixSum k - a.orderSequence.prefixSum k = 0 ∨
      b.orderSequence.prefixSum k - a.orderSequence.prefixSum k = 1 ∨
      b.orderSequence.prefixSum k - a.orderSequence.prefixSum k = 2 := by
  exact ((a.representationOrderCondition_iff b le_rfl).mp horder)
    |>.prefixGap_trichotomy_of_totalGap htotal k hk

end BONG.GoodBONG

end Bong
