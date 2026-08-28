/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019): a capped witness for the domination principle

The domination principle in Lemma 7.9 is applied to square-bracket defects,
which include both endpoint alpha caps.  This file strengthens the raw
square-class witness to that capped form.  An even prefix contains an
adjacent pair whose capped defect is no larger than the capped defect of the
whole alternating prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Among the first `pairs + 1` disjoint adjacent pairs, one capped pair
defect is no larger than the capped alternating defect of their union. -/
theorem exists_cappedAdjacent_le_alternatingPrefix_pairs
    (b : GoodBONG q L (n + 2)) (pairs : Nat)
    (hbound : 2 * (pairs + 1) ≤ n + 2) :
    ∃ t, ∃ ht : t ≤ pairs,
      b.truncatedPrefixDefect b (-1) (2 * t) (2 * t + 2) ≤
        b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
          0 (2 * (pairs + 1)) := by
  induction pairs with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      norm_num
  | succ pairs ih =>
      have hpreviousBound : 2 * (pairs + 1) ≤ n + 2 := by
        omega
      rcases ih hpreviousBound with ⟨t, ht, htDefect⟩
      let previous := 2 * (pairs + 1)
      have hdomination := b.truncatedPrefixDefect_domination b b
        ((-1) ^ (pairs + 1)) (-1) 0 previous (previous + 2)
      have hdomination' :
          min
              (b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
                0 previous)
              (b.truncatedPrefixDefect b (-1) previous
                (previous + 2)) ≤
            b.truncatedPrefixDefect b ((-1) ^ (pairs + 2))
              0 (previous + 2) := by
        simpa only [pow_succ] using hdomination
      by_cases hle :
          b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
              0 previous ≤
            b.truncatedPrefixDefect b (-1) previous (previous + 2)
      · refine ⟨t, ht.trans (Nat.le_succ _), ?_⟩
        have hprevious :
            b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
                0 previous ≤
              b.truncatedPrefixDefect b ((-1) ^ (pairs + 2))
                0 (previous + 2) := by
          simpa only [min_eq_left hle] using hdomination'
        simpa only [previous,
          show 2 * (pairs + 1 + 1) = 2 * (pairs + 1) + 2 by omega]
            using htDefect.trans hprevious
      · have hlast :
            b.truncatedPrefixDefect b (-1) previous (previous + 2) ≤
              b.truncatedPrefixDefect b ((-1) ^ (pairs + 2))
                0 (previous + 2) := by
          simpa only [min_eq_right (le_of_not_ge hle)] using hdomination'
        refine ⟨pairs + 1, le_rfl, ?_⟩
        simpa only [previous,
          show 2 * (pairs + 1 + 1) = 2 * (pairs + 1) + 2 by omega]
            using hlast

/-- Paper-indexed capped domination witness.  The witness is the zero-based
even start of an adjacent pair strictly contained in the prefix. -/
theorem exists_even_cappedAdjacent_le_alternatingPrefix
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hiPos : 0 < i) (hiBound : i ≤ n + 2) (hiEven : Even i) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i ∧
      b.truncatedPrefixDefect b (-1) j.val (j.val + 2) ≤
        b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i := by
  rcases hiEven with ⟨d, hd⟩
  have hi : i = 2 * d := by
    omega
  have hdPos : 0 < d := by
    omega
  let pairs := d - 1
  have hpairs : 2 * (pairs + 1) = i := by
    simp only [pairs]
    omega
  have hbound : 2 * (pairs + 1) ≤ n + 2 := by
    omega
  rcases b.exists_cappedAdjacent_le_alternatingPrefix_pairs
      pairs hbound with ⟨t, ht, hdefect⟩
  let j : Fin (n + 1) := ⟨2 * t, by
    simp only [pairs] at ht
    omega⟩
  refine ⟨j, ⟨t, by simp only [j]; omega⟩, ?_, ?_⟩
  · simp only [j] at ⊢
    omega
  · have hdiv : i / 2 = pairs + 1 := by
      rw [hi]
      simp only [pairs]
      omega
    simpa only [j, hpairs, hdiv] using hdefect

end BONG.GoodBONG

end Bong
