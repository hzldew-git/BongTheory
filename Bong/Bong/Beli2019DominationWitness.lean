/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77
import Bong.Bong.DefectArithmetic

/-!
# Beli (2019): a finite witness for the domination principle

An even alternating prefix is the product of its disjoint adjacent pairs.
Repeated quadratic-defect domination therefore supplies one adjacent pair
whose defect is no larger than the defect of the whole prefix.  This is the
existential form used repeatedly in cases 3, 6, and 8 of Lemma 7.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Adding one adjacent pair factors the alternating prefix unit by that
pair's signed product. -/
theorem alternatingPrefixUnit_add_two
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hi : i + 1 < n + 2) (heven : Even i) :
    (-1) ^ ((i + 2) / 2) * b.prefixProduct (i + 2) =
      ((-1) ^ (i / 2) * b.prefixProduct i) *
        b.adjacentProduct ⟨i, by omega⟩ := by
  rcases heven with ⟨d, hd⟩
  subst i
  rw [b.prefixProduct_add_two (d + d) (by omega)]
  have hzero : (⟨d + d, by omega⟩ : Fin (n + 2)) =
      (⟨d + d, by omega⟩ : Fin (n + 1)).castSucc := by
    apply Fin.ext
    rfl
  have hone : (⟨d + d + 1, by omega⟩ : Fin (n + 2)) =
      (⟨d + d, by omega⟩ : Fin (n + 1)).succ := by
    apply Fin.ext
    rfl
  rw [hzero, hone]
  apply Units.ext
  simp only [adjacentProduct, GoodBONG.valueUnit, Units.val_mul,
    Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one]
  have hdivZero : (d + d) / 2 = d := by omega
  have hdivTwo : (d + d + 2) / 2 = d + 1 := by omega
  rw [hdivZero, hdivTwo, pow_succ]
  ring

/-- Among the first `pairs + 1` disjoint adjacent pairs, one pair has
defect at most the defect of their complete alternating product. -/
theorem exists_adjacentDefect_le_alternatingPrefixDefect_pairs
    (b : GoodBONG q L (n + 2)) (pairs : Nat)
    (hbound : 2 * (pairs + 1) ≤ n + 2) :
    ∃ t, ∃ ht : t ≤ pairs,
      b.adjacentDefect ⟨2 * t, by
        omega⟩ ≤
        b.alternatingPrefixDefect (2 * (pairs + 1)) := by
  induction pairs with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      have hunit := b.alternatingPrefixUnit_add_two 0 (by omega)
        ⟨0, by omega⟩
      unfold alternatingPrefixDefect
      rw [show 2 * (0 + 1) = 0 + 2 by omega, hunit]
      simp only [Nat.zero_div, pow_zero, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, one_mul, adjacentDefect, Nat.mul_zero]
      exact le_rfl
  | succ pairs ih =>
      have hpreviousBound : 2 * (pairs + 1) ≤ n + 2 := by omega
      rcases ih hpreviousBound with ⟨t, ht, htDefect⟩
      let previous := 2 * (pairs + 1)
      let last : Fin (n + 1) := ⟨previous, by
        simp only [previous]
        omega⟩
      have hpreviousEven : Even previous :=
        ⟨pairs + 1, by simp only [previous]; omega⟩
      have hunit := b.alternatingPrefixUnit_add_two previous
        (by simp only [previous]; omega) hpreviousEven
      have hdom :
          min (b.alternatingPrefixDefect previous)
              (b.adjacentDefect last) ≤
            b.alternatingPrefixDefect (previous + 2) := by
        unfold alternatingPrefixDefect adjacentDefect
        rw [hunit]
        exact defectOrder_mul_ge_min _ _
      by_cases hle : b.alternatingPrefixDefect previous ≤
          b.adjacentDefect last
      · refine ⟨t, ht.trans (Nat.le_succ _), ?_⟩
        have hprevious : b.alternatingPrefixDefect previous ≤
            b.alternatingPrefixDefect (previous + 2) := by
          simpa only [min_eq_left hle] using hdom
        simpa only [previous, show 2 * (pairs + 1 + 1) =
          2 * (pairs + 1) + 2 by omega] using
            htDefect.trans hprevious
      · have hlast : b.adjacentDefect last ≤
            b.alternatingPrefixDefect (previous + 2) := by
          simpa only [min_eq_right (le_of_not_ge hle)] using hdom
        refine ⟨pairs + 1, le_rfl, ?_⟩
        simpa only [last, previous, show 2 * (pairs + 1 + 1) =
          2 * (pairs + 1) + 2 by omega] using hlast

/-- Paper-indexed form of the domination witness.  For a positive even
prefix length `i`, the witness `j` is the zero-based start of an adjacent
pair, hence `j` is even and `j + 1 < i`. -/
theorem exists_even_adjacentDefect_le_alternatingPrefixDefect
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hiPos : 0 < i) (hiBound : i ≤ n + 2) (hiEven : Even i) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i ∧
      b.adjacentDefect j ≤
        b.alternatingPrefixDefect i := by
  rcases hiEven with ⟨d, hd⟩
  have hi : i = 2 * d := by omega
  have hdPos : 0 < d := by omega
  let pairs := d - 1
  have hpairs : 2 * (pairs + 1) = i := by
    simp only [pairs]
    omega
  have hbound : 2 * (pairs + 1) ≤ n + 2 := by omega
  rcases b.exists_adjacentDefect_le_alternatingPrefixDefect_pairs
      pairs hbound with ⟨t, ht, hdefect⟩
  let j : Fin (n + 1) := ⟨2 * t, by
    simp only [pairs] at ht
    omega⟩
  refine ⟨j, ⟨t, by simp only [j]; omega⟩, ?_, ?_⟩
  · simp only [j] at ⊢
    omega
  · simpa only [j, hpairs] using hdefect

/-! The preceding statements use the rank shape `n+2`, which is convenient
for Beli's Section 7.  Later papers often keep a fixed ambient rank `m+1` and
only assume that the even prefix lies strictly inside it.  The next three
lemmas record the identical argument in that indexing convention, avoiding
any transport through a predecessor equality. -/

/-- Fixed-rank version of `alternatingPrefixUnit_add_two`. -/
theorem alternatingPrefixUnit_add_two_fixedRank {m : Nat}
    (b : GoodBONG q L (m + 1)) (i : Nat)
    (hi : i + 1 < m + 1) (heven : Even i) :
    (-1) ^ ((i + 2) / 2) * b.prefixProduct (i + 2) =
      ((-1) ^ (i / 2) * b.prefixProduct i) *
        b.adjacentProduct ⟨i, by omega⟩ := by
  rcases heven with ⟨d, hd⟩
  subst i
  rw [b.prefixProduct_add_two (d + d) (by omega)]
  have hzero : (⟨d + d, by omega⟩ : Fin (m + 1)) =
      (⟨d + d, by omega⟩ : Fin m).castSucc := by
    apply Fin.ext
    rfl
  have hone : (⟨d + d + 1, by omega⟩ : Fin (m + 1)) =
      (⟨d + d, by omega⟩ : Fin m).succ := by
    apply Fin.ext
    rfl
  rw [hzero, hone]
  apply Units.ext
  simp only [adjacentProduct, GoodBONG.valueUnit, Units.val_mul,
    Units.val_neg, Units.val_pow_eq_pow_val, Units.val_one]
  have hdivZero : (d + d) / 2 = d := by omega
  have hdivTwo : (d + d + 2) / 2 = d + 1 := by omega
  rw [hdivZero, hdivTwo, pow_succ]
  ring

/-- Fixed-rank domination witness for a prescribed number of adjacent pairs. -/
theorem exists_adjacentDefect_le_alternatingPrefixDefect_pairs_fixedRank
    {m : Nat} (b : GoodBONG q L (m + 1)) (pairs : Nat)
    (hbound : 2 * (pairs + 1) ≤ m + 1) :
    ∃ t, ∃ ht : t ≤ pairs,
      b.adjacentDefect ⟨2 * t, by omega⟩ ≤
        b.alternatingPrefixDefect (2 * (pairs + 1)) := by
  induction pairs with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      have hunit := b.alternatingPrefixUnit_add_two_fixedRank 0 (by omega)
        ⟨0, by omega⟩
      unfold alternatingPrefixDefect
      rw [show 2 * (0 + 1) = 0 + 2 by omega, hunit]
      simp only [Nat.zero_div, pow_zero, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, one_mul, adjacentDefect, Nat.mul_zero]
      exact le_rfl
  | succ pairs ih =>
      have hpreviousBound : 2 * (pairs + 1) ≤ m + 1 := by omega
      rcases ih hpreviousBound with ⟨t, ht, htDefect⟩
      let previous := 2 * (pairs + 1)
      let last : Fin m := ⟨previous, by
        simp only [previous]
        omega⟩
      have hpreviousEven : Even previous :=
        ⟨pairs + 1, by simp only [previous]; omega⟩
      have hunit := b.alternatingPrefixUnit_add_two_fixedRank previous
        (by simp only [previous]; omega) hpreviousEven
      have hdom :
          min (b.alternatingPrefixDefect previous)
              (b.adjacentDefect last) ≤
            b.alternatingPrefixDefect (previous + 2) := by
        unfold alternatingPrefixDefect adjacentDefect
        rw [hunit]
        exact defectOrder_mul_ge_min _ _
      by_cases hle : b.alternatingPrefixDefect previous ≤
          b.adjacentDefect last
      · refine ⟨t, ht.trans (Nat.le_succ _), ?_⟩
        have hprevious : b.alternatingPrefixDefect previous ≤
            b.alternatingPrefixDefect (previous + 2) := by
          simpa only [min_eq_left hle] using hdom
        simpa only [previous, show 2 * (pairs + 1 + 1) =
          2 * (pairs + 1) + 2 by omega] using
            htDefect.trans hprevious
      · have hlast : b.adjacentDefect last ≤
            b.alternatingPrefixDefect (previous + 2) := by
          simpa only [min_eq_right (le_of_not_ge hle)] using hdom
        refine ⟨pairs + 1, le_rfl, ?_⟩
        simpa only [last, previous, show 2 * (pairs + 1 + 1) =
          2 * (pairs + 1) + 2 by omega] using hlast

/-- Fixed-rank form of the even-prefix domination principle. -/
theorem exists_even_adjacentDefect_le_alternatingPrefixDefect_fixedRank
    {m : Nat} (b : GoodBONG q L (m + 1)) (i : Nat)
    (hiPos : 0 < i) (hiBound : i ≤ m + 1) (hiEven : Even i) :
    ∃ j : Fin m, Even j.val ∧ j.val + 1 < i ∧
      b.adjacentDefect j ≤ b.alternatingPrefixDefect i := by
  rcases hiEven with ⟨d, hd⟩
  have hi : i = 2 * d := by omega
  have hdPos : 0 < d := by omega
  let pairs := d - 1
  have hpairs : 2 * (pairs + 1) = i := by
    simp only [pairs]
    omega
  have hbound : 2 * (pairs + 1) ≤ m + 1 := by omega
  rcases b.exists_adjacentDefect_le_alternatingPrefixDefect_pairs_fixedRank
      pairs hbound with ⟨t, ht, hdefect⟩
  let j : Fin m := ⟨2 * t, by
    simp only [pairs] at ht
    omega⟩
  refine ⟨j, ⟨t, by simp only [j]; omega⟩, ?_, ?_⟩
  · simp only [j] at ⊢
    omega
  · simpa only [j, hpairs] using hdefect

end BONG.GoodBONG

end Bong
