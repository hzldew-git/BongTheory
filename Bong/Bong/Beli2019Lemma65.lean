/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 6.5

An odd discrepancy between the two cumulative order sums makes the
comparison-prefix product have odd valuation.  Condition 2.1(ii) then forces
one of the explicit candidates defining `A_i` to be nonpositive, which gives
one of the two cross-order inequalities in the paper.
-/

namespace Bong

open Dyadic

universe u v w

/-- Congruence to one more than `b` makes `a + b` odd. -/
theorem odd_add_of_modEq_add_one {a b : Int}
    (h : Int.ModEq 2 a (b + 1)) : Odd (a + b) := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨c, hc⟩
  refine ⟨b - c, ?_⟩
  omega

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The prefix-sum congruence in Lemma 6.5 makes the comparison-prefix
product have odd valuation. -/
theorem comparisonPrefixProduct_order_odd_of_modEq_add_one
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hparity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val + 1)) :
    Odd (ordUnit K (a.prefixProduct i.val * b.prefixProduct i.val)) := by
  rw [ordUnit_mul,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum i.val i.lt_large.le,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum i.val i.le_small]
  exact odd_add_of_modEq_add_one hparity

/-- A nonpositive half-gap candidate gives the first cross-order bound in
Lemma 6.5. -/
theorem sourceNext_le_targetCurrent_of_halfGap_le_zero
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (h : a.representationHalfGap b i ≤ 0) :
    a.order ⟨i.val, i.lt_large⟩ ≤
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
  unfold representationHalfGap at h
  norm_cast at h
  push_cast at h
  simp only [Rat.divInt_eq_div] at h
  have hePos : (0 : ℚ) < (ramificationIndex K : ℚ) := by
    exact_mod_cast ramificationIndex_pos K
  by_contra hnot
  have hdiffInt : 0 < a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
    omega
  have hdiffRat : (0 : ℚ) <
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) := by
    exact_mod_cast hdiffInt
  linarith

/-- A nonpositive primary candidate gives the first cross-order bound in
Lemma 6.5. -/
theorem sourceNext_le_targetCurrent_of_primary_le_zero
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (h : a.representationPrimaryDefect b i ≤ 0) :
    a.order ⟨i.val, i.lt_large⟩ ≤
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
  have hdefect := a.truncatedPrefixDefect_nonneg
    (alphaV := alphaV) (alphaW := alphaW)
    b (-1) (i.val + 1) (i.val - 1)
  have hshift :
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤ 0 := by
    calc
      (((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤
          (((a.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1) :=
        le_add_of_nonneg_right hdefect
      _ = a.representationPrimaryDefect b i := by
        rfl
      _ ≤ 0 := h
  norm_cast at hshift
  exact_mod_cast (sub_nonpos.mp hshift)

/-- A nonpositive secondary candidate gives the adjacent-pair alternative
in Lemma 6.5. -/
theorem sourcePair_le_targetPair_of_secondary_le_zero
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1)
    (h : a.representationSecondaryDefect b i hi ≤ 0) :
    a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ ≤
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
  have hdefect := a.truncatedPrefixDefect_nonneg
    (alphaV := alphaV) (alphaW := alphaW)
    b 1 (i.val + 2) (i.val - 2)
  have hshift :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤ 0 := by
    calc
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤
          (((a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hi.2⟩ -
            b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
            b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) :=
        le_add_of_nonneg_right hdefect
      _ = a.representationSecondaryDefect b i hi := by
        rfl
      _ ≤ 0 := h
  norm_cast at hshift
  omega

/-- Beli (2019), Lemma 6.5, with one-based paper index `i.val`. -/
theorem beli2019Lemma65
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (m + 1) (n + 1))
    (hparity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val + 1)) :
    a.order ⟨i.val, i.lt_large⟩ ≤
        b.order ⟨i.val - 1, by have := i.le_small; omega⟩ ∨
      ∃ hi : 1 < i.val ∧ i.val + 1 < m + 1,
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ ≤
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
            b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
  have hodd := a.comparisonPrefixProduct_order_odd_of_modEq_add_one
    b i hparity
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order
    (alphaV := alphaV) (alphaW := alphaW) b i.val hodd
  have hAlphaValue := hdefect i
  rw [hzero] at hAlphaValue
  have hAlpha : a.representationAlpha b i ≤ 0 := by
    rw [← a.coe_representationAlphaValue b i]
    exact hAlphaValue
  rw [a.representationAlpha_eq_min_halfGap_prime b i] at hAlpha
  rcases min_le_iff.mp hAlpha with hhalf | hprime
  · exact Or.inl
      (a.sourceNext_le_targetCurrent_of_halfGap_le_zero b i hhalf)
  · by_cases hi : 1 < i.val ∧ i.val + 1 < m + 1
    · rw [a.representationAlphaPrime_eq_min_primary_secondary b i hi]
        at hprime
      rcases min_le_iff.mp hprime with hprimary | hsecondary
      · exact Or.inl
          (a.sourceNext_le_targetCurrent_of_primary_le_zero
            (alphaV := alphaV) (alphaW := alphaW) b i hprimary)
      · exact Or.inr ⟨hi,
          a.sourcePair_le_targetPair_of_secondary_le_zero
            (alphaV := alphaV) (alphaW := alphaW) b i hi hsecondary⟩
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior b i hi]
        at hprime
      exact Or.inl
        (a.sourceNext_le_targetCurrent_of_primary_le_zero
          (alphaV := alphaV) (alphaW := alphaW) b i hprime)

end BONG.GoodBONG

end Bong
