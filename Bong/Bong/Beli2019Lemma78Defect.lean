/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Dual
import Bong.Bong.Beli2019Lemma69TypeIIISecondary

/-!
# Beli (2019), Lemma 7.8: isolation of the central mixed defect

At the type-III center the representation alpha is zero.  Once the
half-gap and optional secondary candidates are strictly positive, the
primary candidate is therefore exactly zero.  Cancelling its finite order
shift gives the mixed capped-defect equality used in Lemma 7.8.
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
  {L N : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- If every candidate in Definition 4 is nonnegative, then so is the
representation alpha. -/
theorem representationAlpha_nonneg_of_candidates
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hHalf : 0 ≤ a.representationHalfGap b i)
    (hPrimary : 0 ≤ a.representationPrimaryDefect b i)
    (hSecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < m + 1,
      0 ≤ a.representationSecondaryDefect b i hi) :
    0 ≤ a.representationAlpha b i := by
  rw [a.representationAlpha_eq_min_halfGap_prime b i]
  apply le_min hHalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < m + 1
  · rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
    exact le_min hPrimary (hSecondary hi)
  · rw [a.representationAlphaPrime_eq_primary_of_not_interior b i hi]
    exact hPrimary

/-- If `A_i = 0` and every other candidate is positive, the primary
candidate is the unique candidate attaining zero. -/
theorem representationPrimaryDefect_eq_zero_of_alphaValue_eq_zero
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i = 0)
    (hHalf : 0 < a.representationHalfGap b i)
    (hSecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < m + 1,
      0 < a.representationSecondaryDefect b i hi) :
    a.representationPrimaryDefect b i = 0 := by
  have hAlphaTop : a.representationAlpha b i = 0 := by
    rw [← a.coe_representationAlphaValue b i, hAlpha]
    norm_num
  rw [a.representationAlpha_eq_min_halfGap_prime b i] at hAlphaTop
  have hPrime : a.representationAlphaPrime b i = 0 := by
    by_cases hle : a.representationHalfGap b i ≤
        a.representationAlphaPrime b i
    · rw [min_eq_left hle] at hAlphaTop
      exact ((ne_of_gt hHalf) hAlphaTop).elim
    · have hle' : a.representationAlphaPrime b i ≤
          a.representationHalfGap b i := le_of_not_ge hle
      simpa only [min_eq_right hle'] using hAlphaTop
  by_cases hi : 1 < i.val ∧ i.val + 1 < m + 1
  · rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
      at hPrime
    by_cases hle : a.representationPrimaryDefect b i ≤
        a.representationSecondaryDefect b i hi
    · simpa only [min_eq_left hle] using hPrime
    · have hle' : a.representationSecondaryDefect b i hi ≤
          a.representationPrimaryDefect b i := le_of_not_ge hle
      rw [min_eq_right hle'] at hPrime
      exact ((ne_of_gt (hSecondary hi)) hPrime).elim
  · rw [a.representationAlphaPrime_eq_primary_of_not_interior b i hi]
      at hPrime
    exact hPrime

/-- A zero primary candidate identifies its capped defect with the
negative finite order shift. -/
theorem truncatedPrefixDefect_eq_neg_order_of_primary_eq_zero
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hPrimary : a.representationPrimaryDefect b i = 0) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
      ((((b.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
        a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let shift : ℚ :=
    (a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int)
  unfold representationPrimaryDefect at hPrimary
  change (shift : WithTop ℚ) +
      a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) = 0
    at hPrimary
  have hzero : (shift : WithTop ℚ) + ((-shift : ℚ) : WithTop ℚ) = 0 := by
    norm_cast
    ring
  have hcancel : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) = ((-shift : ℚ) : WithTop ℚ) := by
    apply WithTop.add_left_cancel WithTop.coe_ne_top
    exact hPrimary.trans hzero.symm
  rw [hcancel]
  norm_cast
  dsimp only [shift]
  push_cast
  ring

/-- Combined candidate-isolation form of the central mixed-defect step. -/
theorem truncatedPrefixDefect_eq_neg_order_of_alphaValue_eq_zero
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hAlpha : a.representationAlphaValue b i = 0)
    (hHalf : 0 < a.representationHalfGap b i)
    (hSecondary : ∀ hi : 1 < i.val ∧ i.val + 1 < m + 1,
      0 < a.representationSecondaryDefect b i hi) :
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) =
      ((((b.order ⟨i.val - 1, by have := i.le_small; omega⟩ -
        a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)) : WithTop ℚ) := by
  apply a.truncatedPrefixDefect_eq_neg_order_of_primary_eq_zero b i
  exact a.representationPrimaryDefect_eq_zero_of_alphaValue_eq_zero
    b i hAlpha hHalf hSecondary

/-- A positive integral coefficient makes the secondary candidate positive. -/
theorem representationSecondaryDefect_pos_of_orderCoefficient_pos
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (hCoefficient : 0 <
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩) :
    0 < a.representationSecondaryDefect b i hi := by
  have hdefect := a.truncatedPrefixDefect_nonneg
    (alphaV := alphaV) (alphaW := alphaW)
    b 1 (i.val + 2) (i.val - 2)
  unfold representationSecondaryDefect
  have hCoefficientTop : (0 : WithTop ℚ) <
      (((a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
        WithTop ℚ) := by
    norm_cast
  calc
    (0 : WithTop ℚ) <
        (((a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hi.2⟩ -
            b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
            b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + 0 := by simpa using hCoefficientTop
    _ ≤ _ := by gcongr

/-- Lemma 7.8's lower bound makes its central half-gap candidate positive. -/
theorem lemma78_typeIII_representationHalfGap_pos
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b)
    (hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ + 1) :
    0 < a.representationHalfGap b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } := by
  let left := D.outer.transition.lastZero
  have hleftBound : left < n + 1 := by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : left + 1 < n + 1 := by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let center : Fin n := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let idx : RepresentationIndex (n + 1) (n + 1) := {
    val := left + 1
    pos := by omega
    lt_large := hrightBound
    le_small := hrightBound.le }
  have hleftOrder : b.order ⟨left, hleftBound⟩ =
      a.order ⟨left, hleftBound⟩ + 1 := by
    have hboundary := D.outer.transition.leftBoundary
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hleftBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
      at hboundary
    exact hboundary
  have hcross :
      a.order ⟨idx.val, idx.lt_large⟩ -
          b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
        a.orderGap center - 1 := by
    unfold orderGap
    change a.order ⟨left + 1, hrightBound⟩ -
        b.order ⟨left, hleftBound⟩ =
      a.order ⟨left + 1, hrightBound⟩ -
        a.order ⟨left, hleftBound⟩ - 1
    rw [hleftOrder]
    ring
  have hgap' : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 := by
    simpa only [center, left] using hgap
  have hpositive : (0 : ℚ) <
      ((a.orderGap center - 1 : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    have hgapQ : (3 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
        (a.orderGap center : ℚ) + 1 := by
      exact_mod_cast hgap'
    push_cast
    linarith
  change (0 : WithTop ℚ) <
    (((((a.order ⟨idx.val, idx.lt_large⟩ -
      b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ : Int) : ℚ) /
      2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ)
  rw [hcross]
  exact_mod_cast hpositive

/-- Coordinate-free form of Lemma 7.8's first mixed-defect equality. -/
theorem beli2019Lemma78_centralMixedDefect
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (D : Lemma67TypeIII a b)
    (hAlpha : a.representationAlphaValue b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } = 0)
    (hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ + 1)
    (hSecondaryCoefficient :
      ∀ hi : 1 < D.outer.transition.lastZero + 1 ∧
          D.outer.transition.lastZero + 1 + 1 < n + 1,
        0 <
          a.order ⟨D.outer.transition.lastZero + 1, by omega⟩ +
            a.order ⟨D.outer.transition.lastZero + 1 + 1, hi.2⟩ -
            b.order ⟨D.outer.transition.lastZero + 1 - 2, by omega⟩ -
            b.order ⟨D.outer.transition.lastZero + 1 - 1, by omega⟩) :
    a.truncatedPrefixDefect b (-1)
        (D.outer.transition.lastZero + 2)
        D.outer.transition.lastZero =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  let idx : RepresentationIndex (n + 1) (n + 1) := {
    val := D.outer.transition.lastZero + 1
    pos := by omega
    lt_large := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    le_small := by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega }
  have hHalf : 0 < a.representationHalfGap b idx := by
    simpa only [idx] using
      a.lemma78_typeIII_representationHalfGap_pos b D hgap
  have hSecondary : ∀ hi : 1 < idx.val ∧ idx.val + 1 < n + 1,
      0 < a.representationSecondaryDefect b idx hi := by
    intro hi
    apply a.representationSecondaryDefect_pos_of_orderCoefficient_pos
      (alphaV := alpha) (alphaW := alpha) b idx hi
    simpa only [idx] using hSecondaryCoefficient hi
  have hplus : D.outer.transition.lastZero + 1 + 1 =
      D.outer.transition.lastZero + 2 := by omega
  have hminus : D.outer.transition.lastZero + 1 - 1 =
      D.outer.transition.lastZero := by omega
  simpa only [idx, hplus, hminus] using
    a.truncatedPrefixDefect_eq_neg_order_of_alphaValue_eq_zero
      b idx hAlpha hHalf hSecondary

/-- Lemma 7.8's central mixed-defect equality, conditional only on the
`A_t = 0` conclusion of Lemma 6.9(i). -/
theorem beli2019Lemma78_centralMixedDefect_of_alpha_zero
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q N (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hAlpha : a.representationAlphaValue b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } = 0)
    (hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ + 1) :
    a.truncatedPrefixDefect b (-1)
        (D.outer.transition.lastZero + 2)
        D.outer.transition.lastZero =
      ((((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : ℚ)) : WithTop ℚ) := by
  apply a.beli2019Lemma78_centralMixedDefect b D hAlpha hgap
  intro hi
  exact a.lemma69_typeIII_secondaryCoefficient_pos b D hfirst hi

end BONG.GoodBONG

end Bong
