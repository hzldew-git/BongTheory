/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78TargetAlpha

/-!
# Beli (2019), Remark 6.16: prefix-defect transfer

When the representation invariant at a boundary is the target alpha, the
mixed prefix defect is exactly that alpha.  The capped domination principle
then identifies every target prefix defect with the minimum of the
corresponding source prefix defect and the target alpha.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The right-alpha branch of Remark 6.16, specialized to a prefix ending at
the boundary where `A_i = beta_i`. -/
theorem beli2019Remark616_rightPrefix
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, by
        have := i.pos
        have := i.lt_large
        omega⟩)
    (epsilon : Kˣ) :
    b.truncatedPrefixDefect b epsilon 0 i.val =
      min (a.truncatedPrefixDefect a epsilon 0 i.val)
        (b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ :
          WithTop ℚ) := by
  let beta : WithTop ℚ :=
    (b.alphaValue ⟨i.val - 1, by
      have := i.pos
      have := i.lt_large
      omega⟩ : WithTop ℚ)
  let source := a.truncatedPrefixDefect a epsilon 0 i.val
  let cross := a.truncatedPrefixDefect b 1 i.val i.val
  let target := b.truncatedPrefixDefect b epsilon 0 i.val
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
          have := i.pos
          have := i.lt_large
          omega⟩ :
          WithTop ℚ) :=
        b.prefixAlphaCap_of_internal i.pos i.lt_large
  have hcrossEq : cross = beta := le_antisymm hcrossUpper hcrossLower
  by_cases hsourceLt : source < beta
  · have hsharp := a.truncatedPrefixDefect_mul_eq_left_of_lt_right
      a b epsilon 1 0 i.val i.val (by
        simpa only [source, cross, hcrossEq] using hsourceLt)
    rw [min_eq_left hsourceLt.le]
    calc
      target = a.truncatedPrefixDefect b epsilon 0 i.val := by
        exact (a.truncatedPrefixDefect_zero_left_eq_self
          b epsilon i.val).symm
      _ = source := by simpa only [mul_one, source] using hsharp
  · have hbetaSource : beta ≤ source := le_of_not_gt hsourceLt
    rw [min_eq_right hbetaSource]
    apply le_antisymm
    · dsimp only [target, beta]
      calc
        b.truncatedPrefixDefect b epsilon 0 i.val ≤
            b.prefixAlphaCap i.val :=
          b.truncatedPrefixDefect_le_rightCap b epsilon 0 i.val
        _ = (b.alphaValue ⟨i.val - 1, by
            have := i.pos
            have := i.lt_large
            omega⟩ :
            WithTop ℚ) :=
          b.prefixAlphaCap_of_internal i.pos i.lt_large
    · have hdomination := a.truncatedPrefixDefect_domination
        a b epsilon 1 0 i.val i.val
      have hbetaMixed : beta ≤
          a.truncatedPrefixDefect b epsilon 0 i.val := by
        calc
          beta = min source cross := by rw [hcrossEq, min_eq_right hbetaSource]
          _ ≤ a.truncatedPrefixDefect b (epsilon * 1) 0 i.val := by
            simpa only [source, cross] using hdomination
          _ = a.truncatedPrefixDefect b epsilon 0 i.val := by rw [mul_one]
      rw [← a.truncatedPrefixDefect_zero_left_eq_self b epsilon i.val]
      exact hbetaMixed

end BONG.GoodBONG

end Bong
