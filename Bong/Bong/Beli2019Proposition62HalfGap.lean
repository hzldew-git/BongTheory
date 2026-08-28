/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62TargetCandidate
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Proposition 6.2: the half-gap candidate

If the half-gap candidate realizes `A_i` and the current source order is at
most the target order, condition 2.1(ii) and the defining half-gap bound for
`alpha_i` give the direct comparison between the corresponding even
coordinates of the two `W`-sequences.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The half-gap branch of the even-coordinate comparison in Proposition
6.2. -/
theorem weightSequence_even_direct_of_halfGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ ≤
      b.order ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hhalf : a.representationAlpha b i =
      a.representationHalfGap b i) :
    (a.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : ℚ) +
        a.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ ≤
      (b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ : ℚ) +
        b.alphaValue ⟨i.val - 1, by
          have := i.pos
          have := i.lt_large
          omega⟩ := by
  let p : Fin n := ⟨i.val - 1, by
    have := i.pos
    have := i.lt_large
    omega⟩
  have hright := a.representationAlpha_le_rightAlpha b hdefect i
  rw [hhalf] at hright
  unfold representationHalfGap at hright
  norm_cast at hright
  rw [Rat.divInt_eq_div] at hright
  push_cast at hright
  have hright' : ((a.order p.succ : ℚ) - (b.order p.castSucc : ℚ)) / 2 +
      (ramificationIndex K : ℚ) ≤ b.alphaValue p := by
    simpa only [p, Fin.succ_mk, Fin.castSucc_mk, Nat.sub_add_cancel i.pos]
      using hright
  have halpha := a.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at halpha
  push_cast at halpha
  have hcurrentQ : (a.order p.castSucc : ℚ) ≤
      (b.order p.castSucc : ℚ) := by
    exact_mod_cast hcurrent
  change (a.order p.castSucc : ℚ) + a.alphaValue p ≤
    (b.order p.castSucc : ℚ) + b.alphaValue p
  linarith

end BONG.GoodBONG

end Bong
