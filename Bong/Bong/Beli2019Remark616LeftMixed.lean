/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark616MixedPrefix

/-!
# Beli (2019), Remark 6.16: the left-alpha branch

The existing right-alpha formula treats `A_i = beta_i`.  This file proves
the symmetric formula used when `A_i = alpha_i`, including the paper's
two-unit comparison for an arbitrary third prefix.
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
  {n : Nat}

/-- Remark 6.16 when the representation invariant is the source alpha.
The third prefix may end at any natural boundary `j`. -/
theorem beli2019Remark616_leftMixedPrefix
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i =
      a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩)
    (epsilon : Kˣ) (j : Nat) :
    a.truncatedPrefixDefect c epsilon i.val j =
      min (b.truncatedPrefixDefect c epsilon i.val j)
        (a.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) := by
  let alpha : WithTop ℚ :=
    (a.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      have hp := i.pos
      omega⟩ : WithTop ℚ)
  let source := b.truncatedPrefixDefect c epsilon i.val j
  let cross := a.truncatedPrefixDefect b 1 i.val i.val
  let target := a.truncatedPrefixDefect c epsilon i.val j
  have hcrossLower : alpha ≤ cross := by
    dsimp only [alpha, cross]
    simpa only [hAlpha] using hdefect i
  have hcrossUpper : cross ≤ alpha := by
    dsimp only [cross, alpha]
    calc
      a.truncatedPrefixDefect b 1 i.val i.val ≤
          a.prefixAlphaCap i.val :=
        a.truncatedPrefixDefect_le_leftCap b 1 i.val i.val
      _ = (a.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) :=
        a.prefixAlphaCap_of_internal i.pos i.lt_large
  have hcrossEq : cross = alpha := le_antisymm hcrossUpper hcrossLower
  by_cases hsourceLt : source < alpha
  · rw [min_eq_left hsourceLt.le]
    have hsourceCross :
        c.truncatedPrefixDefect b epsilon j i.val <
          b.truncatedPrefixDefect a 1 i.val i.val := by
      rw [c.truncatedPrefixDefect_comm b,
        b.truncatedPrefixDefect_comm a]
      simpa only [source, cross, hcrossEq] using hsourceLt
    have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
      b a epsilon 1 j i.val i.val hsourceCross
    calc
      target = c.truncatedPrefixDefect a epsilon j i.val :=
        a.truncatedPrefixDefect_comm c epsilon i.val j
      _ = c.truncatedPrefixDefect b epsilon j i.val := by
        simpa only [mul_one] using hsharp
      _ = source := c.truncatedPrefixDefect_comm b epsilon j i.val
  · have halphaSource : alpha ≤ source := le_of_not_gt hsourceLt
    rw [min_eq_right halphaSource]
    apply le_antisymm
    · dsimp only [target, alpha]
      calc
        a.truncatedPrefixDefect c epsilon i.val j ≤
            a.prefixAlphaCap i.val :=
          a.truncatedPrefixDefect_le_leftCap c epsilon i.val j
        _ = (a.alphaValue ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ : WithTop ℚ) :=
          a.prefixAlphaCap_of_internal i.pos i.lt_large
    · have hdomination := c.truncatedPrefixDefect_domination
        b a epsilon 1 j i.val i.val
      calc
        alpha = min source cross := by
          rw [hcrossEq, min_eq_right halphaSource]
        _ ≤ c.truncatedPrefixDefect a (epsilon * 1) j i.val := by
          rw [c.truncatedPrefixDefect_comm b epsilon j i.val,
            b.truncatedPrefixDefect_comm a 1 i.val i.val]
            at hdomination
          simpa only [source, cross] using hdomination
        _ = target := by
          rw [mul_one, ← a.truncatedPrefixDefect_comm c epsilon i.val j]

/-- In the left-alpha branch, closeness of the two alpha values gives the
two-unit defect comparison stated after Remark 6.16. -/
theorem beli2019Remark616_leftMixedPrefix_right_le_add_two
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i =
      a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩)
    (hclose : b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩ + 2)
    (epsilon : Kˣ) (j : Nat) :
    b.truncatedPrefixDefect c epsilon i.val j ≤
      a.truncatedPrefixDefect c epsilon i.val j +
        ((2 : ℚ) : WithTop ℚ) := by
  have hformula := beli2019Remark616_leftMixedPrefix
    a b c hdefect i hAlpha epsilon j
  by_cases hbelow : b.truncatedPrefixDefect c epsilon i.val j ≤
      (a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩ : WithTop ℚ)
  · rw [hformula, min_eq_left hbelow]
    exact le_add_of_nonneg_right (by norm_num)
  · have halphaBelow :
        (a.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) ≤
        b.truncatedPrefixDefect c epsilon i.val j :=
      le_of_not_ge hbelow
    have hcap := b.truncatedPrefixDefect_le_leftCap
      c epsilon i.val j
    rw [b.prefixAlphaCap_of_internal i.pos i.lt_large] at hcap
    have hcloseTop :
        (b.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) ≤
        (a.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) + ((2 : ℚ) : WithTop ℚ) := by
      exact_mod_cast hclose
    rw [hformula, min_eq_right halphaBelow]
    exact hcap.trans hcloseTop

end BONG.GoodBONG

end Bong
