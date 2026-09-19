/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma54
import Bong.Bong.HeHu2022Lemma59

/-!
# He (2024), Lemma 5.5

For odd paper rank `N = 2*k+3`, the element called `cTilde` below is the
paper's `(-1)^((N+1)/2) a_(1,N+1)`.  The proof separates the capped prefix
defect supplied by `J2_E(N-1)` from the field defect, and records the exact
point at which the trigger `R_(N+1)=1 or R_(N+2)>1` removes the final alpha
cap.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The trigger in Lemma 5.5 makes the alpha cap immediately after
`R_(N+1)` strictly larger than `1-R_(N+1)`. -/
theorem he2022ClassicLemma55_nextAlpha_gt
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    (1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) <
      a.alphaValue ⟨2 * k + 3, by omega⟩ := by
  have hSumLe :
      (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) <= 1 := by
    have h := hJ2.2.1.le
    have hExponent : (2 * k + 2 + 2) / 2 = k + 2 := by omega
    simpa only [hExponent] using h
  have hPrevious : a.order ⟨2 * k + 1, by omega⟩ = 0 := by
    exact hJ1.1 ⟨2 * k + 1, by omega⟩
  have hLastIndex :
      (⟨2 * k + 4 - 1, by omega⟩ : Fin (m + 3)) =
        ⟨2 * k + 3, by omega⟩ := by
    apply Fin.ext
    change 2 * k + 4 - 1 = 2 * k + 3
    omega
  have hExponent' : (2 * k + 4) / 2 = k + 2 := by omega
  have hSumLe' :
      (((a.order ⟨2 * k + 4 - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ ((2 * k + 4) / 2)) 0
            (2 * k + 4) <= 1 := by
    rw [hLastIndex, hExponent']
    exact hSumLe
  have hCases := a.he2022ClassicLemma44 (m := m + 1) (j := 2 * k + 4)
    (by omega) (by omega) hPrevious hSumLe'
  have hBoundaryCases :
      a.order ⟨2 * k + 3, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 3, by omega⟩ = 1 := by
    rw [hLastIndex] at hCases
    exact hCases.1
  let next : Fin (m + 2) := ⟨2 * k + 3, by omega⟩
  have hGap : a.orderGap next =
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap next
    simp only [Fin.castSucc_mk, Fin.succ_mk]
  rcases hBoundaryCases with hBoundaryZero | hBoundaryOne
  · have hNextLarge : 1 < a.order ⟨2 * k + 4, by omega⟩ := by
      apply hTrigger.resolve_left
      intro hOne
      rw [hBoundaryZero] at hOne
      omega
    have hGapLarge : 1 < a.orderGap next := by
      rw [hGap, hBoundaryZero]
      omega
    by_cases hGapLe : a.orderGap next <=
        2 * (ramificationIndex K : Int)
    · have hLower := (a.he2022ClassicProposition22).lowerBound next hGapLe
      rw [hBoundaryZero]
      norm_num only [Int.cast_zero, sub_zero]
      have hGapLargeQ : (1 : ℚ) < (a.orderGap next : ℚ) := by
        exact_mod_cast hGapLarge
      exact hGapLargeQ.trans_le hLower.1
    · have hGapGt : 2 * (ramificationIndex K : Int) <
          a.orderGap next := lt_of_not_ge hGapLe
      have hAlphaGt :=
        (a.he2022ClassicProposition22).compareTwoE next |>.1.mpr hGapGt
      have hePositive : (0 : Int) < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      have hOneLtTwoE : (1 : ℚ) < 2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast (show (1 : Int) <
          2 * (ramificationIndex K : Int) by omega)
      rw [hBoundaryZero]
      norm_num only [Int.cast_zero, sub_zero]
      exact hOneLtTwoE.trans hAlphaGt
  · have hNextGe : 1 <= a.order ⟨2 * k + 4, by omega⟩ :=
      a.heHu2022Remark52_order_ge_one (n := 2 * k + 3)
        (by omega) ⟨k + 1, by omega⟩ (by omega) hClassic.isIntegral hBoundaryOne
    have hGapNonnegative : 0 <= a.orderGap next := by
      rw [hGap, hBoundaryOne]
      omega
    have hAlphaNe : a.alphaValue next ≠ 0 := by
      intro hZero
      have hGapMinusTwoE :=
        (a.he2022ClassicProposition23 next).alphaZero.mp hZero
      have hePositive : (0 : Int) < (ramificationIndex K : Int) := by
        exact_mod_cast ramificationIndex_pos (K := K)
      omega
    have hAlphaOne : 1 <= a.alphaValue next :=
      a.heHuOne_le_alphaValue_of_ne_zero next hAlphaNe
    rw [hBoundaryOne]
    norm_num only [Int.cast_one, sub_self]
    exact lt_of_lt_of_le (by norm_num) hAlphaOne

/-- He (2024), Lemma 5.5.  The three conclusions are the defect of the
signed prefix, the fact that its sharp companion is a unit, and the
complementary sharp defect. -/
theorem he2022ClassicLemma55
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      defectOrder (K := K) cTilde =
          ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) ∧
        IsValuationUnit K (heHuSharp cTilde hc : K) ∧
        defectOrder (K := K) (heHuSharp cTilde hc) =
          (((2 * (ramificationIndex K : Int) +
              a.order ⟨2 * k + 3, by omega⟩ - 1 : Int) : ℚ) :
            WithTop ℚ) := by
  dsimp only
  let cTilde : Kˣ := heHuLemma59CTilde a k
  have hSumLe :
      (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) <= 1 := by
    have h := hJ2.2.1.le
    have hExponent : (2 * k + 2 + 2) / 2 = k + 2 := by omega
    simpa only [hExponent] using h
  have hPrevious : a.order ⟨2 * k + 1, by omega⟩ = 0 :=
    hJ1.1 ⟨2 * k + 1, by omega⟩
  have hLastIndex :
      (⟨2 * k + 4 - 1, by omega⟩ : Fin (m + 3)) =
        ⟨2 * k + 3, by omega⟩ := by
    apply Fin.ext
    change 2 * k + 4 - 1 = 2 * k + 3
    omega
  have hExponent' : (2 * k + 4) / 2 = k + 2 := by omega
  have hSumLe' :
      (((a.order ⟨2 * k + 4 - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ ((2 * k + 4) / 2)) 0
            (2 * k + 4) <= 1 := by
    rw [hLastIndex, hExponent']
    exact hSumLe
  have hBoundaryCases :=
    (a.he2022ClassicLemma44 (m := m + 1) (j := 2 * k + 4)
      (by omega) (by omega) hPrevious hSumLe').1
  have hBoundaryCases' :
      a.order ⟨2 * k + 3, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 3, by omega⟩ = 1 := by
    rw [hLastIndex] at hBoundaryCases
    exact hBoundaryCases
  have hCapped :
      a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) =
        ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) := by
    have hRaw := hJ2.2.1
    have hExponent : (2 * k + 2 + 2) / 2 = k + 2 := by omega
    rw [hExponent] at hRaw
    apply WithTop.add_left_cancel (WithTop.coe_ne_top)
    calc
      (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (k + 2)) 0 (2 * k + 4) =
        1 := hRaw
      _ = (((a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) := by
        norm_cast
        ring
  have hAlphaNext := a.he2022ClassicLemma55_nextAlpha_gt hm hClassic
    hJ1 hJ2 hTrigger
  have hAlphaNextTop :
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) <
        (a.alphaValue ⟨2 * k + 3, by omega⟩ : WithTop ℚ) := by
    exact_mod_cast hAlphaNext
  have hRawDefect : defectOrder (K := K) cTilde =
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
    unfold truncatedPrefixDefect at hCapped
    rw [a.prefixAlphaCap_zero,
      a.prefixAlphaCap_of_internal (i := 2 * k + 4) (by omega) (by omega)] at hCapped
    simp only [min_top_left] at hCapped
    have hPrefixIndex :
        (⟨2 * k + 4 - 1, by omega⟩ : Fin (m + 2)) =
          ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      change 2 * k + 4 - 1 = 2 * k + 3
      omega
    have hProduct :
        (-1) ^ (k + 2) * a.prefixProduct 0 *
            a.prefixProduct (2 * k + 4) = cTilde := by
      simp only [cTilde, heHuLemma59CTilde, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one]
    rw [hPrefixIndex, hProduct] at hCapped
    by_cases hRawLe : defectOrder (K := K) cTilde <=
        (a.alphaValue ⟨2 * k + 3, by omega⟩ : WithTop ℚ)
    · simpa only [min_eq_left hRawLe] using hCapped
    · have hCapLe : (a.alphaValue ⟨2 * k + 3, by omega⟩ : WithTop ℚ) <=
          defectOrder (K := K) cTilde := le_of_not_ge hRawLe
      rw [min_eq_right hCapLe] at hCapped
      exact (ne_of_gt hAlphaNextTop hCapped).elim
  have hDefectNonnegative :
      0 <= (1 : Int) - a.order ⟨2 * k + 3, by omega⟩ := by
    rcases hBoundaryCases' with hZero | hOne <;> omega
  have hDefectLt :
      (1 : Int) - a.order ⟨2 * k + 3, by omega⟩ <
        2 * (ramificationIndex K : Int) := by
    have hePositive : (0 : Int) < (ramificationIndex K : Int) := by
      exact_mod_cast ramificationIndex_pos (K := K)
    rcases hBoundaryCases' with hZero | hOne <;> omega
  let hc : HeHuSharpDomain cTilde :=
    heHuLemma45_sharpDomain_of_defect_lt_twoE cTilde
      (1 - a.order ⟨2 * k + 3, by omega⟩) hRawDefect hDefectLt
  refine ⟨hc, hRawDefect, (heHu2022Proposition32 cTilde hc).1, ?_⟩
  have hSource : (heHuSharpData cTilde hc).sourceDefect =
      ((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) := by
    have hs := (heHuSharpData cTilde hc).source_defectOrder
    rw [hRawDefect] at hs
    exact WithTop.coe_eq_coe.mp hs.symm
  have hSharp := (heHu2022Proposition32 cTilde hc).2.1
  rw [hSource] at hSharp
  convert hSharp using 1
  norm_cast
  ring

end BONG.GoodBONG

end Bong
