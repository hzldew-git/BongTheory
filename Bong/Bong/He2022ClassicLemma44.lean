/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicSectionFour
import Bong.Bong.Beli2019CappedIntegrality

/-!
# He (2024), Lemma 4.4

The paper indices are one-based.  Thus `R_(j-2)` and `R_j` occur at Lean
indices `j-3` and `j-1`.  The proof makes explicit the discreteness step
which is implicit in the printed argument: a capped self-prefix defect below
one is integral, because its only possible nonintegral alpha cap lies above
`2e`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- He, Lemma 4.4.  The conclusion is the literal assertion
`{R_j, d[(-1)^(j/2) a_(1,j)]} subset {0,1}`. -/
theorem he2022ClassicLemma44 {m j : Nat}
    (a : GoodBONG q L (m + 2))
    (hjFour : 4 <= j) (hjBound : j <= m + 2)
    (hPrevious : a.order ⟨j - 3, by omega⟩ = 0)
    (hSum :
      (((a.order ⟨j - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (j / 2)) 0 j <= 1) :
    (a.order ⟨j - 1, by omega⟩ = 0 ∨
        a.order ⟨j - 1, by omega⟩ = 1) ∧
      (a.truncatedPrefixDefect a ((-1) ^ (j / 2)) 0 j = 0 ∨
        a.truncatedPrefixDefect a ((-1) ^ (j / 2)) 0 j = 1) := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  let current : Fin (m + 2) := ⟨j - 1, by omega⟩
  let capped : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (j / 2)) 0 j
  have hOrderMono := a.orderSequence.twoStep (j - 3) (by omega)
  have hOrderNonnegative : 0 <= a.order current := by
    change a.order ⟨j - 3, by omega⟩ <=
      a.order ⟨j - 3 + 2, by omega⟩ at hOrderMono
    have hindex : (⟨j - 3 + 2, by omega⟩ : Fin (m + 2)) =
        current := by
      apply Fin.ext
      simp only [current]
      omega
    rw [hPrevious, hindex] at hOrderMono
    exact hOrderMono
  have hCappedNonnegative : (0 : WithTop ℚ) <= capped := by
    exact a.truncatedPrefixDefect_nonneg
      a ((-1) ^ (j / 2)) 0 j
  have hOrderCastNonnegative : (0 : WithTop ℚ) <=
      (((a.order current : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hOrderNonnegative
  have hOrderCastLe :
      (((a.order current : Int) : ℚ) : WithTop ℚ) <= 1 := by
    calc
      (((a.order current : Int) : ℚ) : WithTop ℚ) <=
          (((a.order current : Int) : ℚ) : WithTop ℚ) + capped :=
        le_add_of_nonneg_right hCappedNonnegative
      _ <= 1 := by simpa only [current, capped] using hSum
  have hOrderLe : a.order current <= 1 := by
    exact_mod_cast hOrderCastLe
  have hOrderCases : a.order current = 0 ∨ a.order current = 1 := by
    omega
  have hCappedLe : capped <= 1 := by
    calc
      capped <=
          (((a.order current : Int) : ℚ) : WithTop ℚ) + capped :=
        le_add_of_nonneg_left hOrderCastNonnegative
      _ <= 1 := by simpa only [current, capped] using hSum
  have hCappedIntegral : IsWithTopRationalInteger capped := by
    by_cases hjInternal : j < m + 2
    · rcases a.alternatingSelfCapped_integral_or_eq_nonintegral_alpha
          ((-1) ^ (j / 2)) j (by omega) hjInternal with
        hinteger | hnoninteger
      · exact hinteger
      · exfalso
        have hlarge := a.twoE_lt_alternatingSelfCapped_of_not_integral
          ((-1) ^ (j / 2)) j (by omega) hjInternal (by
            intro hinteger
            exact hnoninteger.2 (by
              rcases hinteger with ⟨z, hz⟩
              refine ⟨z, ?_⟩
              rw [hnoninteger.1] at hz
              exact WithTop.coe_eq_coe.mp hz))
        have hePositive : 0 < ramificationIndex K :=
          ramificationIndex_pos (K := K)
        have hOneLeTwoE : (1 : WithTop ℚ) <=
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
          exact_mod_cast (show (1 : ℚ) <=
            2 * (ramificationIndex K : ℚ) by
              exact_mod_cast (show (1 : Int) <=
                2 * (ramificationIndex K : Int) by omega))
        have hOneLt : (1 : WithTop ℚ) < capped :=
          lt_of_le_of_lt hOneLeTwoE hlarge
        exact (not_lt_of_ge hCappedLe) hOneLt
    · have hjLast : j = m + 2 := by omega
      have hraw : capped = defectOrder (K := K)
          (((-1 : Kˣ) ^ (j / 2)) * a.prefixProduct 0 *
            a.prefixProduct j) := by
        dsimp only [capped]
        unfold truncatedPrefixDefect
        rw [a.prefixAlphaCap_zero, hjLast, a.prefixAlphaCap_last]
        simp
      rcases defectOrder_eq_top_or_isWithTopRationalInteger
          (K := K)
          (((-1 : Kˣ) ^ (j / 2)) * a.prefixProduct 0 *
            a.prefixProduct j) with htop | hinteger
      · exfalso
        rw [hraw, htop] at hCappedLe
        simp at hCappedLe
      · simpa only [hraw] using hinteger
  have hCappedCases : capped = 0 ∨ capped = 1 := by
    rcases hCappedIntegral with ⟨z, hz⟩
    have hzNonnegative : 0 <= z := by
      have : (0 : WithTop ℚ) <= ((z : ℚ) : WithTop ℚ) := by
        simpa only [hz] using hCappedNonnegative
      exact_mod_cast this
    have hzLe : z <= 1 := by
      have : ((z : ℚ) : WithTop ℚ) <= (1 : WithTop ℚ) := by
        simpa only [hz] using hCappedLe
      exact_mod_cast this
    rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl
    · left
      simpa only [Int.cast_zero, WithTop.coe_zero] using hz
    · right
      simpa only [Int.cast_one, WithTop.coe_one] using hz
  simpa only [current, capped] using And.intro hOrderCases hCappedCases

end BONG.GoodBONG

end Bong
