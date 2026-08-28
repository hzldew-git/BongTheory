/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDiagonalEvenSpinorUpper
import Bong.Bong.BinaryDiagonalLowSpinor
import Bong.Bong.BinaryDiagonalMiddleSpinor

/-!
# Binary spinor norms in the nonnegative-order branch

This file assembles the unconditional diagonal calculations.  The low
branch includes the boundary `R = 0`; outside that branch an odd order is
impossible because the parameter defect is zero.  Thus the remaining case
is exactly the even shifted-model calculation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Beli (2003), Lemma 3.7 for every binary BONG with nonnegative relative
order, without a `BinarySpinorLocalLaws` hypothesis. -/
theorem spinorNormImage_eq_beliSpinorGroupRepresentative_of_nonnegative
    (b : BONG V q L 2) (hRnonneg : 0 ≤ b.binaryOrderGap) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (beliSpinorGroupRepresentative K b.binaryParameter :
        Set (SquareClass K)) := by
  by_cases hRupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int)
  · by_cases hdLower : 2 * beliParameterDefect K b.binaryParameter ≤
        (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)
    · exact b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_low_defect
        hRnonneg hRupper hdLower
    · have hEven : Even b.binaryOrderGap := by
        rcases Int.even_or_odd b.binaryOrderGap with hEven | hOdd
        · exact hEven
        · exfalso
          have hOddParameter : Odd (ordUnit K b.binaryParameter) := by
            change Odd b.binaryParameterOrder
            rwa [b.binaryParameterOrder_eq_orderGap]
          have hOddNegative : Odd (ordUnit K (-b.binaryParameter)) := by
            simpa only [ordUnit_neg] using hOddParameter
          have hzero : beliParameterDefect K b.binaryParameter = 0 := by
            unfold beliParameterDefect
            exact quadraticDefect_eq_zero_of_odd_ordUnit
              (-b.binaryParameter) hOddNegative
          apply hdLower
          rw [hzero]
          simp
      exact b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_even_nonlow
        hRnonneg hRupper hEven hdLower
  · have hR : 2 * (ramificationIndex K : Int) < b.binaryOrderGap := by
      omega
    exact b.spinorNormImage_eq_beliSpinorGroupRepresentative_of_two_e_lt hR

end BONG

end Bong
