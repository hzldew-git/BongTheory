/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark616LeftMixed

/-!
# Beli (2019), Remark 6.16: arbitrary right mixed prefixes

The right-alpha transfer formula remains valid when the third prefix ends
at a boundary different from the first two prefixes.
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

/-- Remark 6.16's right-alpha formula with an arbitrary third-prefix
boundary `j`. -/
theorem beli2019Remark616_rightMixedPrefix_at
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        have hp := i.pos
        omega⟩)
    (epsilon : Kˣ) (j : Nat) :
    b.truncatedPrefixDefect c epsilon i.val j =
      min (a.truncatedPrefixDefect c epsilon i.val j)
        (b.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) := by
  let beta : WithTop ℚ :=
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      have hp := i.pos
      omega⟩ : WithTop ℚ)
  let source := a.truncatedPrefixDefect c epsilon i.val j
  let cross := a.truncatedPrefixDefect b 1 i.val i.val
  let target := b.truncatedPrefixDefect c epsilon i.val j
  have hcrossLower : beta ≤ cross := by
    dsimp only [beta, cross]
    simpa only [hAlpha] using hdefect i
  have hcrossUpper : cross ≤ beta := by
    dsimp only [cross, beta]
    calc
      a.truncatedPrefixDefect b 1 i.val i.val ≤
          b.prefixAlphaCap i.val :=
        a.truncatedPrefixDefect_le_rightCap b 1 i.val i.val
      _ = (b.alphaValue ⟨i.val - 1, by
          have hi := i.lt_large
          have hp := i.pos
          omega⟩ : WithTop ℚ) :=
        b.prefixAlphaCap_of_internal i.pos i.lt_large
  have hcrossEq : cross = beta := le_antisymm hcrossUpper hcrossLower
  by_cases hsourceLt : source < beta
  · rw [min_eq_left hsourceLt.le]
    have hsourceCross :
        c.truncatedPrefixDefect a epsilon j i.val <
          a.truncatedPrefixDefect b 1 i.val i.val := by
      rw [c.truncatedPrefixDefect_comm a]
      simpa only [source, cross, hcrossEq] using hsourceLt
    have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
      a b epsilon 1 j i.val i.val hsourceCross
    calc
      target = c.truncatedPrefixDefect b epsilon j i.val :=
        b.truncatedPrefixDefect_comm c epsilon i.val j
      _ = c.truncatedPrefixDefect a epsilon j i.val := by
        simpa only [mul_one] using hsharp
      _ = source := c.truncatedPrefixDefect_comm a epsilon j i.val
  · have hbetaSource : beta ≤ source := le_of_not_gt hsourceLt
    rw [min_eq_right hbetaSource]
    apply le_antisymm
    · dsimp only [target, beta]
      calc
        b.truncatedPrefixDefect c epsilon i.val j ≤
            b.prefixAlphaCap i.val :=
          b.truncatedPrefixDefect_le_leftCap c epsilon i.val j
        _ = (b.alphaValue ⟨i.val - 1, by
            have hi := i.lt_large
            have hp := i.pos
            omega⟩ : WithTop ℚ) :=
          b.prefixAlphaCap_of_internal i.pos i.lt_large
    · have hdomination := c.truncatedPrefixDefect_domination
        a b epsilon 1 j i.val i.val
      calc
        beta = min source cross := by
          rw [hcrossEq, min_eq_right hbetaSource]
        _ ≤ c.truncatedPrefixDefect b (epsilon * 1) j i.val := by
          rw [c.truncatedPrefixDefect_comm a epsilon j i.val]
            at hdomination
          simpa only [source, cross] using hdomination
        _ = target := by
          rw [mul_one, ← b.truncatedPrefixDefect_comm c epsilon i.val j]

end BONG.GoodBONG

end Bong
