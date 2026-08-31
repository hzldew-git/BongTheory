/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaParityProof
import Bong.Bong.BeliUniversalOrder

/-!
# The alpha-zero and alpha-one alternatives

This file formalizes Lemma 2.8 and its first-boundary Corollary 2.9 from
Beli's universal-forms paper.  All alpha-law interfaces are discharged by
the concrete results already proved for the earlier Beli papers.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The concrete alpha laws used in the universal-forms paper. -/
theorem beliUniversalAlphaLaws : Beli2006AlphaLaws.{u, v} K := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : HilbertSymbolLaws K := Dyadic.hilbertSymbolLawsProved
  letI : UnitQuadraticDefectParityLaws K :=
    unitQuadraticDefectParityLawsProved
  exact beli2006AlphaLaws_proved

/-- The concrete alpha-parity laws used in the universal-forms paper. -/
theorem beliUniversalAlphaParityLaws :
    Beli2009AlphaParityLaws.{u, v} K := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : HilbertSymbolLaws K := Dyadic.hilbertSymbolLawsProved
  letI : UnitQuadraticDefectParityLaws K :=
    unitQuadraticDefectParityLawsProved
  exact beli2009AlphaParityLaws_proved

namespace BONG.GoodBONG

/-- If the alpha value is one and the half-gap candidate is strictly larger,
the adjacent capped defect attains the other candidate. -/
private theorem cappedAdjacent_eq_one_sub_orderGap
    [Beli2006AlphaLaws.{u, v} K]
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (halpha : a.alphaValue i = 1)
    (hhalf : (1 : WithTop ℚ) < a.halfGapCandidate i) :
    a.truncatedPrefixDefect a (-1) i.val (i.val + 2) =
      ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) := by
  have hformula := a.alpha_eq_min_halfGap_add_cappedAdjacent i
  rw [halpha] at hformula
  let D := a.truncatedPrefixDefect a (-1) i.val (i.val + 2)
  let g : ℚ := a.orderGap i
  have hformula' :
      ((1 : ℚ) : WithTop ℚ) =
        min (a.halfGapCandidate i) ((g : WithTop ℚ) + D) := by
    simpa only [D, g, orderGap] using hformula
  have hsum : (g : WithTop ℚ) + D = ((1 : ℚ) : WithTop ℚ) := by
    by_cases hle : (g : WithTop ℚ) + D ≤ a.halfGapCandidate i
    · rw [min_eq_right hle] at hformula'
      exact hformula'.symm
    · have hreverse : a.halfGapCandidate i ≤ (g : WithTop ℚ) + D :=
        le_of_not_ge hle
      rw [min_eq_left hreverse] at hformula'
      exact False.elim ((ne_of_lt hhalf) hformula')
  have hone :
      ((1 : ℚ) : WithTop ℚ) =
        (g : WithTop ℚ) + ((((1 : ℚ) - g) : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    congr 1
    ring
  have hcancel := WithTop.add_left_cancel
    (show (g : WithTop ℚ) ≠ ⊤ by simp) (hsum.trans hone)
  simpa only [g] using hcancel

/-- Beli, Lemma 2.8(i). -/
theorem cappedAdjacent_ge_two_e_of_alphaValue_eq_zero
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (halpha : a.alphaValue i = 0) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have hgap := (a.alpha_p2 i).2.mp halpha
  have hbound := a.order_sub_add_alpha_le_cappedAdjacent i
  have hdifference :
      a.order i.castSucc - a.order i.succ =
        2 * (ramificationIndex K : Int) := by
    unfold orderGap at hgap
    omega
  rw [halpha, hdifference] at hbound
  norm_num at hbound
  exact hbound

/-- Beli, Lemma 2.8(ii), including the parity split and the sharp adjacent
defect value away from the left endpoint. -/
theorem alphaValue_eq_one_consequences
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (halpha : a.alphaValue i = 1) :
    (-(2 * (ramificationIndex K : Int)) < a.orderGap i ∧
      a.orderGap i ≤ 1) ∧
    (a.orderGap i = 1 ∨
      (Even (a.orderGap i) ∧
        2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
        a.orderGap i ≤ 0)) ∧
    ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) ∧
    (a.orderGap i ≠ 2 - 2 * (ramificationIndex K : Int) →
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ)) := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have hlowerWeak := a.orderGap_ge_neg_two_mul_e i
  have hnotLower :
      a.orderGap i ≠ -(2 * (ramificationIndex K : Int)) := by
    intro hgap
    have hzero := (a.alpha_p2 i).2.mpr hgap
    rw [halpha] at hzero
    norm_num at hzero
  have hlower :
      -(2 * (ramificationIndex K : Int)) < a.orderGap i := by
    omega
  have hePos := ramificationIndex_pos K
  have halphaLt :
      a.alphaValue i < 2 * (ramificationIndex K : ℚ) := by
    rw [halpha]
    exact_mod_cast (show (1 : Int) < 2 * (ramificationIndex K : Int) by omega)
  have hgapLt :
      a.orderGap i < 2 * (ramificationIndex K : Int) :=
    (a.alpha_p5 i).1.mp halphaLt
  have hgapLeAlpha := (a.alpha_p3 i hgapLt.le).1
  have hupper : a.orderGap i ≤ 1 := by
    rw [halpha] at hgapLeAlpha
    exact_mod_cast hgapLeAlpha
  have hparity :
      a.orderGap i = 1 ∨
        (Even (a.orderGap i) ∧
          2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
          a.orderGap i ≤ 0) := by
    by_cases hone : a.orderGap i = 1
    · exact Or.inl hone
    · right
      have hnonpos : a.orderGap i ≤ 0 := by omega
      have heven : Even (a.orderGap i) := by
        by_cases hzero : a.orderGap i = 0
        · rw [hzero]
          exact Even.zero
        · exact a.orderGap_even_of_negative i (by omega)
      obtain ⟨z, hz⟩ := heven
      refine ⟨⟨z, hz⟩, ?_, hnonpos⟩
      omega
  have hbound := a.order_sub_add_alpha_le_cappedAdjacent i
  have hbound' :
      ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    convert hbound using 1
    · congr 1
      unfold orderGap
      push_cast
      rw [halpha]
      ring
  refine ⟨⟨hlower, hupper⟩, hparity, hbound', ?_⟩
  intro hnotEndpoint
  have hgapStrict :
      2 - 2 * (ramificationIndex K : Int) < a.orderGap i := by
    rcases hparity with hone | heven
    · rw [hone]
      omega
    · omega
  have hhalf : (1 : WithTop ℚ) < a.halfGapCandidate i := by
    have hgapStrictQ :
        2 - 2 * (ramificationIndex K : ℚ) < (a.orderGap i : ℚ) := by
      exact_mod_cast hgapStrict
    have hhalfQ : (1 : ℚ) < a.halfGapValue i := by
      unfold halfGapValue
      linarith
    rw [← a.coe_halfGapValue]
    exact_mod_cast hhalfQ
  exact cappedAdjacent_eq_one_sub_orderGap a i halpha hhalf

/-- Beli, Lemma 2.8(iii). -/
theorem alphaValue_eq_one_iff_cappedAdjacent
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (hlower : 2 - 2 * (ramificationIndex K : Int) < a.orderGap i)
    (_hupper : a.orderGap i ≤ 0) :
    a.alphaValue i = 1 ↔
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  constructor
  · intro halpha
    have hhalf : (1 : WithTop ℚ) < a.halfGapCandidate i := by
      have hlowerQ :
          2 - 2 * (ramificationIndex K : ℚ) < (a.orderGap i : ℚ) := by
        exact_mod_cast hlower
      have hhalfQ : (1 : ℚ) < a.halfGapValue i := by
        unfold halfGapValue
        linarith
      rw [← a.coe_halfGapValue]
      exact_mod_cast hhalfQ
    exact cappedAdjacent_eq_one_sub_orderGap a i halpha hhalf
  · intro hdefect
    have hhalf :
        (1 : WithTop ℚ) ≤ a.halfGapCandidate i := by
      have hlowerQ :
          2 - 2 * (ramificationIndex K : ℚ) < (a.orderGap i : ℚ) := by
        exact_mod_cast hlower
      have hhalfQ : (1 : ℚ) ≤ a.halfGapValue i := by
        unfold halfGapValue
        linarith
      rw [← a.coe_halfGapValue]
      exact_mod_cast hhalfQ
    have hsum :
        (((((a.order i.succ - a.order i.castSucc : Int) : ℚ)) :
            WithTop ℚ) +
          ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ)) = 1 := by
      rw [show a.order i.succ - a.order i.castSucc = a.orderGap i by rfl,
        ← WithTop.coe_add]
      congr 1
      ring
    have hcoe :
        (a.alphaValue i : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := by
      calc
        (a.alphaValue i : WithTop ℚ) =
            min (a.halfGapCandidate i)
              (((((a.order i.succ - a.order i.castSucc : Int) : ℚ)) :
                  WithTop ℚ) +
                a.truncatedPrefixDefect a (-1) i.val (i.val + 2)) :=
          a.alpha_eq_min_halfGap_add_cappedAdjacent i
        _ = min (a.halfGapCandidate i) 1 := by rw [hdefect, hsum]
        _ = 1 := min_eq_right hhalf
    exact WithTop.coe_eq_coe.mp hcoe

/-- The two endpoint gaps in Lemma 2.8(iii) force alpha one. -/
theorem alphaValue_eq_one_of_orderGap_eq_endpoint
    {n : Nat} (a : GoodBONG q L (n + 1)) (i : Fin n)
    (hgap : a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 1) :
    a.alphaValue i = 1 := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  rcases hgap with hleft | hone
  · have hhalf := a.beli2009Corollary29_i i
      (Or.inr (Or.inr (Or.inl hleft)))
    rw [hhalf]
    unfold halfGapValue
    rw [hleft]
    push_cast
    ring
  · have hle : a.orderGap i ≤ 2 * (ramificationIndex K : Int) := by
      rw [hone]
      have he := ramificationIndex_pos K
      omega
    simpa [hone] using
      (a.alpha_p3 i hle).2.mpr (Or.inr (by rw [hone]; exact odd_one))

end BONG.GoodBONG

end Bong
