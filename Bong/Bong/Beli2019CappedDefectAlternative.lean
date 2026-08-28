/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectMin

/-!
# A sharp alternative for three capped defects

For three prefix square classes whose product is a square, the first capped
defect dominates at least one of the other two.  This is the precise form of
the domination step used twice in Beli (2019), Lemma 2.18.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- In the capped-defect triangle

`d[-b_j b_l]`, `d[-a_i b_j]`, `d[a_i b_l]`,

the first term is at least one of the other two. -/
theorem truncatedPrefixDefect_triangle_alternative
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j l : Nat) :
    a.truncatedPrefixDefect b (-1) i j ≤
        b.truncatedPrefixDefect b (-1) j l ∨
      a.truncatedPrefixDefect b 1 i l ≤
        b.truncatedPrefixDefect b (-1) j l := by
  let x := b.truncatedPrefixDefect b (-1) j l
  let y := a.truncatedPrefixDefect b (-1) i j
  let z := a.truncatedPrefixDefect b 1 i l
  by_cases hyx : y ≤ x
  · exact Or.inl hyx
  · right
    have hxy : x < y := lt_of_not_ge hyx
    have hxCapJ : x < b.prefixAlphaCap j :=
      hxy.trans_le (a.truncatedPrefixDefect_le_rightCap b (-1) i j)
    let X : Kˣ := (-1) * b.prefixProduct j * b.prefixProduct l
    let Y : Kˣ := (-1) * a.prefixProduct i * b.prefixProduct j
    let Z : Kˣ := 1 * a.prefixProduct i * b.prefixProduct l
    by_cases hraw : defectOrder (K := K) X ≤
        min (b.prefixAlphaCap j) (b.prefixAlphaCap l)
    · have hx : x = defectOrder (K := K) X := by
        unfold x truncatedPrefixDefect
        simpa only [X] using min_eq_left hraw
      have hrawY : defectOrder (K := K) X < defectOrder (K := K) Y := by
        rw [← hx]
        exact hxy.trans_le
          (a.truncatedPrefixDefect_le_defect b (-1) i j)
      have hproduct := defectOrder_mul_eq_left_of_lt_right hrawY
      have hunit : X * Y = Z * (b.prefixProduct j) ^ 2 := by
        dsimp only [X, Y, Z]
        apply Units.ext
        simp only [Units.val_mul, Units.val_neg, Units.val_one,
          Units.val_pow_eq_pow_val]
        ring
      rw [hunit, defectOrder_mul_square] at hproduct
      calc
        z ≤ defectOrder (K := K) Z :=
          a.truncatedPrefixDefect_le_defect b 1 i l
        _ = defectOrder (K := K) X := hproduct
        _ = x := hx.symm
    · have hcaps : min (b.prefixAlphaCap j) (b.prefixAlphaCap l) <
          defectOrder (K := K) X := lt_of_not_ge hraw
      have hx : x = min (b.prefixAlphaCap j) (b.prefixAlphaCap l) := by
        unfold x truncatedPrefixDefect
        simpa only [X] using min_eq_right hcaps.le
      have hcapL : b.prefixAlphaCap l < b.prefixAlphaCap j := by
        rw [hx] at hxCapJ
        simpa only [min_lt_iff, lt_self_iff_false, false_or] using hxCapJ
      have hxL : x = b.prefixAlphaCap l := by
        rw [hx, min_eq_right hcapL.le]
      calc
        z ≤ b.prefixAlphaCap l :=
          a.truncatedPrefixDefect_le_rightCap b 1 i l
        _ = x := hxL.symm

end BONG.GoodBONG

end Bong
