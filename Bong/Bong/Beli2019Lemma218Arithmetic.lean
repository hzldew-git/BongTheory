/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlphaLocalFormula
import Bong.Bong.Beli2019CappedDefectAlternative

/-!
# Beli (2019), Lemma 2.18: affine arithmetic

This file isolates the common ordered-arithmetic argument in the two parts of
Lemma 2.18.  Infinite defects are handled before reducing the half-gap branch
to rational linear arithmetic.
-/

namespace Bong

/-- The common two-branch argument in Lemma 2.18.  Here `A` and `C` are the
two terms accompanying `alpha`, while `D` is the capped adjacent defect. -/
theorem withTop_alpha_sum_alternative
    (e gap : ℚ) (A C D alpha : WithTop ℚ)
    (hkey : ((2 * e : ℚ) : WithTop ℚ) <
      A + (gap : WithTop ℚ) + C)
    (halpha : alpha =
      min (((gap / 2 + e : ℚ)) : WithTop ℚ)
        ((gap : WithTop ℚ) + D))
    (halt : C ≤ D ∨ A ≤ D) :
    ((2 * e : ℚ) : WithTop ℚ) < alpha + A ∨
      ((2 * e : ℚ) : WithTop ℚ) < alpha + C := by
  rw [halpha]
  by_cases hhalf :
      (((gap / 2 + e : ℚ)) : WithTop ℚ) ≤
        (gap : WithTop ℚ) + D
  · rw [min_eq_left hhalf]
    by_cases hA : A = ⊤
    · left
      simp only [hA, add_top, WithTop.coe_lt_top]
    by_cases hC : C = ⊤
    · right
      simp only [hC, add_top, WithTop.coe_lt_top]
    rw [← WithTop.coe_untop A hA, ← WithTop.coe_untop C hC] at hkey ⊢
    norm_cast at hkey ⊢
    by_cases hleft : 2 * e < gap / 2 + e + A.untop hA
    · exact Or.inl hleft
    · exact Or.inr (by
        have hleft' : gap / 2 + e + A.untop hA ≤ 2 * e :=
          le_of_not_gt hleft
        linarith)
  · rw [min_eq_right (le_of_not_ge hhalf)]
    rcases halt with hC | hA
    · left
      exact hkey.trans_le (by
        calc
          A + (gap : WithTop ℚ) + C ≤
              A + (gap : WithTop ℚ) + D := add_le_add_right hC _
          _ = ((gap : WithTop ℚ) + D) + A := by ac_rfl)
    · right
      exact hkey.trans_le (by
        calc
          A + (gap : WithTop ℚ) + C ≤
              D + (gap : WithTop ℚ) + C := by
            simpa only [add_assoc] using
              add_le_add_left hA ((gap : WithTop ℚ) + C)
          _ = ((gap : WithTop ℚ) + D) + C := by ac_rfl)

end Bong
