/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionFive

/-!
# He--Hu 2022, Lemma 5.8

This file proves the defect calculation which supplies the two test lattices
in Lemma 5.9.  The paper rank is written as `n + 2`; thus the displayed
element below is `(-1)^((N+1)/2) a_{1,N+1}` for `N = n + 2`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The signed prefix occurring in He--Hu, Lemma 5.8. -/
noncomputable def heHuLemma58Prefix {m n : Nat}
    (a : GoodBONG q L (m + 3)) : Kˣ :=
  (-1) ^ ((n + 3) / 2) * a.prefixProduct (n + 3)

/-- Under the hypotheses of Lemma 5.8, the next alpha cap is strictly
larger than `1 - R_(N+1)`.  This is the step that removes the final cap
from Lemma 2.10(ii). -/
theorem heHuLemma58_nextAlpha_gt {m n : Nat}
    (a : GoodBONG q L (m + 3))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hAlpha : a.alphaValue ⟨n + 1, by omega⟩ = 1)
    (hTrigger : a.order ⟨n + 2, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 3, by omega⟩) :
    (1 : ℚ) - (a.order ⟨n + 2, by omega⟩ : ℚ) <
      a.alphaValue ⟨n + 2, by omega⟩ := by
  let boundary : Fin (m + 2) := ⟨n + 1, by omega⟩
  let next : Fin (m + 2) := ⟨n + 2, by omega⟩
  have hcurrent : a.order ⟨n + 1, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n + 1, by omega⟩ hnOdd
  have hboundaryGap : a.orderGap boundary = a.order ⟨n + 2, by omega⟩ := by
    unfold orderGap boundary
    simp only [Fin.castSucc_mk, Fin.succ_mk]
    have hnextIndex : (⟨n + 1 + 1, by omega⟩ : Fin (m + 3)) =
        ⟨n + 2, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hnextIndex]
    rw [hcurrent]
    omega
  have hshape := (a.heHu2022Proposition26 boundary).alphaOne hAlpha |>.1
  rw [hboundaryGap] at hshape
  have hRLower : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨n + 2, by omega⟩ := by
    rcases hshape with hOne | hEven
    · rw [hOne]
      have he := ramificationIndex_pos (K := K)
      omega
    · exact hEven.2.1
  have hnextGap : a.orderGap next =
      a.order ⟨n + 3, by omega⟩ - a.order ⟨n + 2, by omega⟩ := by
    unfold orderGap next
    simp only [Fin.castSucc_mk, Fin.succ_mk]
  rcases hTrigger with hROne | hNextLarge
  · have hNextGe : 1 ≤ a.order ⟨n + 3, by omega⟩ :=
      a.heHu2022Remark52_order_ge_one hn hnOdd (by omega) hIntegral hROne
    have hgapNonneg : 0 ≤ a.orderGap next := by
      rw [hnextGap, hROne]
      omega
    have hAlphaNe : a.alphaValue next ≠ 0 := by
      intro hzero
      have hgap := (a.heHu2022Proposition26 next).alphaZero.mp hzero
      have he := ramificationIndex_pos (K := K)
      omega
    have hAlphaOne : 1 ≤ a.alphaValue next :=
      a.heHuOne_le_alphaValue_of_ne_zero next hAlphaNe
    have hAlphaOne' : 1 ≤ a.alphaValue ⟨n + 2, by omega⟩ := by
      simpa only [next] using hAlphaOne
    rw [hROne]
    have hzeroLt : (0 : ℚ) < a.alphaValue ⟨n + 2, by omega⟩ :=
      lt_of_lt_of_le (by norm_num) hAlphaOne'
    norm_num only [Int.cast_one, sub_self]
    exact hzeroLt
  · by_cases hgapLe : a.orderGap next ≤
        2 * (ramificationIndex K : Int)
    · have hLower := (a.heHu2022Proposition26 next).lowerBound hgapLe |>.1
      rw [hnextGap] at hLower
      have hNextLargeQ : (1 : ℚ) <
          (a.order ⟨n + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hNextLarge
      push_cast at hLower
      linarith
    · have hgapGt : 2 * (ramificationIndex K : Int) < a.orderGap next :=
        lt_of_not_ge hgapLe
      have hAlphaGt :=
        (a.heHu2022Proposition26 next).compareTwoE.2.2.mpr hgapGt
      have hRLowerQ :
          (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
            (a.order ⟨n + 2, by omega⟩ : ℚ) := by
        exact_mod_cast hRLower
      linarith

/-- He--Hu, Lemma 5.8.  The existential witness is the proof that the
paper's sharp operation is defined on the displayed square class; its three
conclusions are respectively the source defect, unit property, and
complementary sharp defect asserted in the paper. -/
theorem heHu2022Lemma58 {m n : Nat}
    (a : GoodBONG q L (m + 3))
    (hn : 3 ≤ n + 2) (hnOdd : Odd (n + 2)) (hm : n + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (n + 1) (by omega))
    (hI2 : a.HeHuI2E (n + 1) (by omega))
    (hAlpha : a.alphaValue ⟨n + 1, by omega⟩ = 1)
    (hTrigger : a.order ⟨n + 2, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 3, by omega⟩) :
    let c := a.heHuLemma58Prefix (n := n)
    ∃ hc : HeHuSharpDomain c,
      defectOrder (K := K) c =
          ((((1 : Int) - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) ∧
        IsValuationUnit K (heHuSharp c hc : K) ∧
        defectOrder (K := K) (heHuSharp c hc) =
          (((2 * (ramificationIndex K : Int) +
              a.order ⟨n + 2, by omega⟩ - 1 : Int) : ℚ) : WithTop ℚ) := by
  dsimp only
  let boundary : Fin (m + 2) := ⟨n + 1, by omega⟩
  let idx : LongRepresentationIndex (m + 3) (n + 2) :=
    { val := n + 1
      one_lt := by omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  let c : Kˣ := a.heHuLemma58Prefix (n := n)
  have hcurrent : a.order ⟨n + 1, by omega⟩ = 0 :=
    hI1.oddOrder ⟨n + 1, by omega⟩ hnOdd
  have hpreviousEven : Even (n + 1) := by
    rcases hnOdd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hprevious : a.order ⟨n, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) :=
    hI1.evenOrder ⟨n, by omega⟩ hpreviousEven
  have hboundaryGap : a.orderGap boundary = a.order ⟨n + 2, by omega⟩ := by
    unfold orderGap boundary
    simp only [Fin.castSucc_mk, Fin.succ_mk]
    have hnextIndex : (⟨n + 1 + 1, by omega⟩ : Fin (m + 3)) =
        ⟨n + 2, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hnextIndex]
    rw [hcurrent]
    omega
  have hshape := (a.heHu2022Proposition26 boundary).alphaOne hAlpha |>.1
  rw [hboundaryGap] at hshape
  have hRLower : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨n + 2, by omega⟩ := by
    rcases hshape with hOne | hEven
    · rw [hOne]
      have he := ramificationIndex_pos (K := K)
      omega
    · exact hEven.2.1
  have hRUpper : a.order ⟨n + 2, by omega⟩ ≤ 1 := by
    rcases hshape with hOne | hEven
    · rw [hOne]
    · omega
  have hnextTwo : -(2 * (ramificationIndex K : Int)) <
      a.order ⟨n + 2, by omega⟩ := by
    omega
  have hlocal :=
    (a.heHuI2E_iff_alpha_le_one_and_capped_boundary
      (n := n + 1) (by omega)).mp hI2 |>.2 hAlpha
  have hlocal' :
      a.truncatedPrefixDefect a (-1) idx.val (idx.val + 2) =
        ((((1 : Int) - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    simpa only [idx, heHuAdjacentCappedDefect, Int.cast_sub,
      Int.cast_one] using hlocal
  have hfull :=
    (a.heHu2022Lemma210ii hIntegral idx hpreviousEven hprevious
      hcurrent hnextTwo).mp hlocal'
  have hfull' :
      a.truncatedPrefixDefect a ((-1) ^ ((n + 3) / 2)) 0 (n + 3) =
        ((((1 : Int) - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    simpa only [idx] using hfull
  have hAlphaNext := a.heHuLemma58_nextAlpha_gt hn hnOdd hm hIntegral
    hI1 hAlpha hTrigger
  have hAlphaNextTop :
      ((((1 : Int) - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) <
        (a.alphaValue ⟨n + 2, by omega⟩ : WithTop ℚ) := by
    exact_mod_cast hAlphaNext
  have hraw : defectOrder (K := K) c =
      ((((1 : Int) - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    unfold truncatedPrefixDefect at hfull'
    rw [a.prefixAlphaCap_zero,
      a.prefixAlphaCap_of_internal (i := n + 3) (by omega) (by omega)] at hfull'
    simp only [min_top_left] at hfull'
    have hprefixIndex : (⟨n + 3 - 1, by omega⟩ : Fin (m + 2)) =
        ⟨n + 2, by omega⟩ := by
      apply Fin.ext
      change n + 3 - 1 = n + 2
      omega
    have hproduct :
        (-1) ^ ((n + 3) / 2) * a.prefixProduct 0 *
            a.prefixProduct (n + 3) = c := by
      simp only [c, heHuLemma58Prefix, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero, mul_one]
    rw [hprefixIndex, hproduct] at hfull'
    by_cases hrawLe : defectOrder (K := K) c ≤
        (a.alphaValue ⟨n + 2, by omega⟩ : WithTop ℚ)
    · simpa only [min_eq_left hrawLe] using hfull'
    · have hcapLe : (a.alphaValue ⟨n + 2, by omega⟩ : WithTop ℚ) ≤
          defectOrder (K := K) c := le_of_not_ge hrawLe
      rw [min_eq_right hcapLe] at hfull'
      exact (ne_of_gt hAlphaNextTop hfull').elim
  have hdNonnegative : 0 ≤
      (1 : Int) - a.order ⟨n + 2, by omega⟩ := by
    omega
  have hdLt : (1 : Int) - a.order ⟨n + 2, by omega⟩ <
      2 * (ramificationIndex K : Int) := by
    omega
  let hc : HeHuSharpDomain c :=
    heHuLemma45_sharpDomain_of_defect_lt_twoE c
      (1 - a.order ⟨n + 2, by omega⟩) hraw hdLt
  refine ⟨hc, hraw, ?_, ?_⟩
  · exact (heHu2022Proposition32 c hc).1
  · have hsource : (heHuSharpData c hc).sourceDefect =
        ((1 - a.order ⟨n + 2, by omega⟩ : Int) : ℚ) := by
      have hs := (heHuSharpData c hc).source_defectOrder
      rw [hraw] at hs
      exact WithTop.coe_eq_coe.mp hs.symm
    have hsharp := (heHu2022Proposition32 c hc).2.1
    rw [hsource] at hsharp
    convert hsharp using 1
    norm_cast
    ring

end BONG.GoodBONG

end Bong
