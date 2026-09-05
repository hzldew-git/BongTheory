/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma31
import Bong.Bong.Beli2019Lemma79DefectOdd

/-!
# He (2024), Lemma 3.3

This file proves the first-index defect condition from the two zero source
orders and the paper's hypothesis `alpha_2 = 1`.  Both branches of the
published proof are retained: positive target first order makes `A_1`
nonpositive, while target first order zero makes all three caps in
`d[a_1 b_1]` at least one.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- Lemma 3.3: `R_1=R_2=0` and `alpha_2=1` imply condition
2.5(ii) at the paper index one. -/
theorem he2022ClassicLemma33 {m n : Nat}
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M (n + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hfirst : a.order (0 : Fin (m + 3)) = 0)
    (hsecond : a.order (1 : Fin (m + 3)) = 0)
    (halphaTwo : a.alphaValue (1 : Fin (m + 2)) = 1)
    (i : RepresentationIndex (m + 3) (n + 2)) (hi : i.val = 1) :
    a.HeClassicDefectConditionAt b i := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  letI : PerfectResidueFieldLaws K := perfectResidueFieldLaws K
  let gapOne : Fin (m + 2) := ⟨1, by omega⟩
  have hzeroPrefix :
      ∀ j : Fin (m + 3), j ≤ gapOne.castSucc → a.order j = 0 := by
    intro j hj
    have hjVal : j.val ≤ 1 := by
      have hjVal' : j.val ≤ gapOne.castSucc.val := hj
      change j.val ≤ 1 at hjVal'
      exact hjVal'
    rcases Nat.eq_zero_or_pos j.val with hjZero | hjPos
    · have hjEq : j = (0 : Fin (m + 3)) := by
        apply Fin.ext
        exact hjZero
      simpa only [hjEq] using hfirst
    · have hjEq : j = (1 : Fin (m + 3)) := by
        apply Fin.ext
        change j.val = 1
        omega
      simpa only [hjEq] using hsecond
  have halphaOne : a.alphaValue (0 : Fin (m + 2)) = 1 := by
    have hgapOne : gapOne = (1 : Fin (m + 2)) := by
      rfl
    have hAlphaGap : a.alphaValue gapOne ≤ (1 : ℚ) := by
      rw [hgapOne, halphaTwo]
    have hall := (a.he2022ClassicProposition24 hAClassic).alphaOneOnZeroPrefix
      gapOne hzeroPrefix gapOne le_rfl hAlphaGap
    exact hall 0 (by simp [gapOne])
  have haIndex : (⟨i.val, i.lt_large⟩ : Fin (m + 3)) = 1 := by
    apply Fin.ext
    exact hi
  have hbIndex : (⟨i.val - 1, by omega⟩ : Fin (n + 2)) = 0 := by
    apply Fin.ext
    change i.val - 1 = 0
    omega
  have htargetNonnegative : 0 ≤ b.order (0 : Fin (n + 2)) := by
    have hbounds := (b.he2022ClassicProposition24 hBClassic).oddIndexed
      0 0 le_rfl Even.zero Even.zero
    exact hbounds.1
  have hprimaryCap :
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) ≤
        (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hAlphaIndex :
        (⟨i.val + 1 - 1, by omega⟩ : Fin (m + 2)) = 1 := by
      apply Fin.ext
      change i.val + 1 - 1 = 1
      omega
    rw [hAlphaIndex, halphaTwo] at hcap
    exact hcap
  have hAlphaUpperTop :
      (a.representationAlphaValue b i : WithTop ℚ) ≤
        (((1 - b.order (0 : Fin (n + 2)) : Int) : ℚ) : WithTop ℚ) := by
    calc
      (a.representationAlphaValue b i : WithTop ℚ) =
          a.representationAlpha b i := a.coe_representationAlphaValue b i
      _ ≤ a.representationPrimaryDefect b i :=
        a.representationAlpha_le_primary b i
      _ ≤ (((a.order ⟨i.val, i.lt_large⟩ -
              b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) + 1 :=
        by
          unfold representationPrimaryDefect
          exact add_le_add (le_refl _) hprimaryCap
      _ = (((1 - b.order (0 : Fin (n + 2)) : Int) : ℚ) : WithTop ℚ) := by
        rw [haIndex, hbIndex, hsecond]
        push_cast
        simp only [sub_eq_add_neg, zero_add, add_comm]
  have hAlphaUpper :
      a.representationAlphaValue b i ≤
        ((1 - b.order (0 : Fin (n + 2)) : Int) : ℚ) := by
    exact_mod_cast hAlphaUpperTop
  by_cases htargetPositive : 1 ≤ b.order (0 : Fin (n + 2))
  · have hnonpositive : a.representationAlphaValue b i ≤ 0 := by
      have hshift :
          ((1 - b.order (0 : Fin (n + 2)) : Int) : ℚ) ≤ 0 := by
        exact_mod_cast (show 1 - b.order (0 : Fin (n + 2)) ≤ 0 by omega)
      exact hAlphaUpper.trans hshift
    exact (show (a.representationAlphaValue b i : WithTop ℚ) ≤ 0 by
      exact_mod_cast hnonpositive).trans
        (a.truncatedPrefixDefect_nonneg
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws) b 1 i.val i.val)
  · have htargetZero : b.order (0 : Fin (n + 2)) = 0 := by omega
    have hAlphaOne : a.representationAlphaValue b i ≤ 1 := by
      simpa only [htargetZero, sub_zero, Int.cast_one] using hAlphaUpper
    let targetGap : Fin (n + 1) := 0
    have htargetSecondLower :
        -(ramificationIndex K : Int) ≤
          b.order (1 : Fin (n + 2)) := by
      have hbounds := (b.he2022ClassicProposition24 hBClassic).evenIndexed
        1 1 le_rfl odd_one odd_one
      exact hbounds.1
    have hbetaNe : b.alphaValue targetGap ≠ 0 := by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      intro hzero
      have hgap := (b.alpha_p2 targetGap).2.mp hzero
      unfold orderGap at hgap
      change b.order (1 : Fin (n + 2)) -
        b.order (0 : Fin (n + 2)) =
          -(2 * (ramificationIndex K : Int)) at hgap
      rw [htargetZero] at hgap
      have hePos := ramificationIndex_pos (K := K)
      omega
    have hbetaOne : (1 : ℚ) ≤ b.alphaValue targetGap := by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      letI : Beli2009AlphaParityLaws.{u, w} K :=
        beliUniversalAlphaParityLaws
      exact b.one_le_alphaValue_of_ne_zero targetGap hbetaNe
    have hproductEven :
        Even (ordUnit K (a.prefixProduct i.val * b.prefixProduct i.val)) := by
      apply a.comparisonPrefixProduct_order_even_of_prefixSum_modEq
        b i.val (by omega) (by omega)
      rw [hi, BeliOrderSequence.prefixSum_one,
        BeliOrderSequence.prefixSum_one]
      simpa only [
        BeliOrderSequence.entryOrZero_of_lt a.orderSequence
          (i := 0) (by omega),
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence
          (i := 0) (by omega),
        orderSequence_at, Fin.zero_eta, hfirst, htargetZero] using
          (Int.ModEq.rfl : Int.ModEq 2 (0 : Int) 0)
    have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
        (1 * a.prefixProduct i.val * b.prefixProduct i.val) := by
      simpa only [one_mul] using
        defectOrder_one_le_of_even
          (a.prefixProduct i.val * b.prefixProduct i.val) hproductEven
    have hsourceCap : (1 : WithTop ℚ) ≤ a.prefixAlphaCap i.val := by
      rw [hi, a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hAlphaIndex :
          (⟨1 - 1, by omega⟩ : Fin (m + 2)) = 0 := by
        apply Fin.ext
        rfl
      rw [hAlphaIndex, halphaOne]
      norm_num
    have htargetCap : (1 : WithTop ℚ) ≤ b.prefixAlphaCap i.val := by
      rw [hi, b.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hAlphaIndex :
          (⟨1 - 1, by omega⟩ : Fin (n + 1)) = targetGap := by
        apply Fin.ext
        rfl
      rw [hAlphaIndex]
      exact_mod_cast hbetaOne
    have htruncated : (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 i.val i.val := by
      unfold truncatedPrefixDefect
      exact le_min hraw (le_min hsourceCap htargetCap)
    exact (show (a.representationAlphaValue b i : WithTop ℚ) ≤ 1 by
      exact_mod_cast hAlphaOne).trans htruncated

end BONG.GoodBONG

end Bong
