/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CappedDefectAlternative

/-!
# Sharp multiplication for capped prefix defects

The domination principle becomes an equality when its two input defects are
strictly separated.  This is the capped analogue of the familiar rule
`d(xy) = d(x)` when `d(x) < d(y)`.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {m n k : Nat}

/-- Strict separation turns capped-defect domination into equality. -/
theorem truncatedPrefixDefect_mul_eq_left_of_lt_right
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (k + 1)) (ε η : Kˣ) (i j l : Nat)
    (h : a.truncatedPrefixDefect b ε i j <
      b.truncatedPrefixDefect c η j l) :
    a.truncatedPrefixDefect c (ε * η) i l =
      a.truncatedPrefixDefect b ε i j := by
  let x := a.truncatedPrefixDefect b ε i j
  let y := b.truncatedPrefixDefect c η j l
  let z := a.truncatedPrefixDefect c (ε * η) i l
  have hxz : x ≤ z := by
    have hdom := a.truncatedPrefixDefect_domination b c ε η i j l
    simpa only [x, y, z, min_eq_left h.le] using hdom
  apply le_antisymm _ hxz
  have hxCapA : x ≤ a.prefixAlphaCap i :=
    a.truncatedPrefixDefect_le_leftCap b ε i j
  by_cases hcapA : a.prefixAlphaCap i ≤ x
  · have hxEq : x = a.prefixAlphaCap i :=
      le_antisymm hxCapA hcapA
    calc
      z ≤ a.prefixAlphaCap i :=
        a.truncatedPrefixDefect_le_leftCap c (ε * η) i l
      _ = x := hxEq.symm
  · have hxLtCapA : x < a.prefixAlphaCap i := lt_of_not_ge hcapA
    have hxLtCapB : x < b.prefixAlphaCap j :=
      h.trans_le (b.truncatedPrefixDefect_le_leftCap c η j l)
    let dx := defectOrder (K := K)
      (ε * a.prefixProduct i * b.prefixProduct j)
    let dy := defectOrder (K := K)
      (η * b.prefixProduct j * c.prefixProduct l)
    let dz := defectOrder (K := K)
      ((ε * η) * a.prefixProduct i * c.prefixProduct l)
    have hxEqRaw : x = dx := by
      have hxFormula : x =
          min dx (min (a.prefixAlphaCap i) (b.prefixAlphaCap j)) := rfl
      by_cases hraw : dx ≤
          min (a.prefixAlphaCap i) (b.prefixAlphaCap j)
      · rw [hxFormula, min_eq_left hraw]
      · have hcaps : min (a.prefixAlphaCap i) (b.prefixAlphaCap j) ≤ dx :=
          le_of_not_ge hraw
        have hxEqCaps : x =
            min (a.prefixAlphaCap i) (b.prefixAlphaCap j) := by
          rw [hxFormula, min_eq_right hcaps]
        have hxLtCaps : x <
            min (a.prefixAlphaCap i) (b.prefixAlphaCap j) :=
          lt_min hxLtCapA hxLtCapB
        rw [hxEqCaps] at hxLtCaps
        exact ((lt_irrefl _) hxLtCaps).elim
    have hrawLt : dx < dy := by
      rw [← hxEqRaw]
      exact h.trans_le (b.truncatedPrefixDefect_le_defect c η j l)
    have hproduct := defectOrder_mul_eq_left_of_lt_right hrawLt
    have hunit :
        (ε * a.prefixProduct i * b.prefixProduct j) *
            (η * b.prefixProduct j * c.prefixProduct l) =
          ((ε * η) * a.prefixProduct i * c.prefixProduct l) *
            (b.prefixProduct j) ^ 2 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hrawProduct : dz = dx := by
      dsimp only [dx, dy, dz] at hproduct ⊢
      rw [hunit, defectOrder_mul_square] at hproduct
      exact hproduct
    calc
      z ≤ dz := a.truncatedPrefixDefect_le_defect c (ε * η) i l
      _ = dx := hrawProduct
      _ = x := hxEqRaw.symm

/-- A zero prefix is independent of the chosen left BONG. -/
theorem truncatedPrefixDefect_zero_left_eq_self
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (ε : Kˣ) (j : Nat) :
    a.truncatedPrefixDefect b ε 0 j =
      b.truncatedPrefixDefect b ε 0 j := by
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
  simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero,
    mul_one]

/-- A zero prefix is independent of the chosen right BONG. -/
theorem truncatedPrefixDefect_zero_right_eq_self
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (ε : Kˣ) (i : Nat) :
    a.truncatedPrefixDefect b ε i 0 =
      a.truncatedPrefixDefect a ε i 0 := by
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, a.prefixAlphaCap_zero]
  simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero,
    mul_one]

end BONG.GoodBONG

end Bong
