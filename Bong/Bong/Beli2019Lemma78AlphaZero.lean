/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIIPrimary
import Bong.Bong.Beli2019Lemma78Defect

/-!
# Beli (2019), Lemma 7.8: the central representation alpha

This file closes the `A_t = 0` step in Lemma 7.8.  The odd prefix gives
`A_t <= 0`; the numerical gap, primary-candidate propagation, and optional
secondary calculation give the reverse inequality candidate by candidate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 7.8: the representation invariant at the type-III center is zero. -/
theorem beli2019Lemma78_representationAlpha_eq_zero
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
    a.representationAlphaValue b {
      val := D.outer.transition.lastZero + 1
      pos := by omega
      lt_large := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      le_small := by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega } = 0 := by
  let left := D.outer.transition.lastZero
  let center : Fin n := ⟨left, by
    dsimp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let idx : RepresentationIndex (n + 1) (n + 1) := {
    val := left + 1
    pos := by omega
    lt_large := by
      dsimp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega
    le_small := by
      dsimp only [left]
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega }
  have hdata := a.beli2019Lemma78_alphas_and_gap
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  have hsourceAlpha : a.alphaValue center = 1 := by
    simpa only [center, left] using hdata.1
  have hgap : 3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 := by
    simpa only [center, left] using hdata.2.2
  have hHalf : 0 ≤ a.representationHalfGap b idx := by
    have hpositive := a.lemma78_typeIII_representationHalfGap_pos b D
      (by simpa only [center, left] using hgap)
    simpa only [idx, left] using hpositive.le
  have hPrimary : 0 ≤ a.representationPrimaryDefect b idx := by
    have hnonneg := a.lemma69_typeIII_primaryDefect_nonneg
      (alphaV := alpha) (alphaW := alpha) b D hfirst
      (by simpa only [center, left] using hsourceAlpha)
    simpa only [idx, left] using hnonneg
  have hSecondary : ∀ hi : 1 < idx.val ∧ idx.val + 1 < n + 1,
      0 ≤ a.representationSecondaryDefect b idx hi := by
    intro hi
    have hcoefficient := a.lemma69_typeIII_secondaryCoefficient_pos
      b D hfirst (by simpa only [idx, left] using hi)
    have hpositive := a.representationSecondaryDefect_pos_of_orderCoefficient_pos
      (alphaV := alpha) (alphaW := alpha) b idx hi
      (by simpa only [idx, left] using hcoefficient)
    exact hpositive.le
  have hnonnegative : 0 ≤ a.representationAlpha b idx :=
    a.representationAlpha_nonneg_of_candidates b idx
      hHalf hPrimary hSecondary
  have hprefixGap :
      a.orderSequence.prefixGap b.orderSequence idx.val = 1 := by
    have hbetween := D.outer.transition.gap_between (left + 1)
      (by omega) (by have hadjacent := D.adjacent; omega)
    simpa only [idx] using hbetween
  have hsum : b.orderSequence.prefixSum idx.val =
      a.orderSequence.prefixSum idx.val + 1 := by
    unfold BeliOrderSequence.prefixGap at hprefixGap
    omega
  have hzeroDefect := a.truncatedPrefixDefect_eq_zero_of_prefixSum_succ
    (alphaV := alpha) (alphaW := alpha) b idx.val
    idx.lt_large.le idx.le_small hsum
  have hupper := hdefect idx
  rw [hzeroDefect] at hupper
  have hlower : (0 : WithTop ℚ) ≤
      (a.representationAlphaValue b idx : WithTop ℚ) := by
    rw [a.coe_representationAlphaValue b idx]
    exact hnonnegative
  have htop : (a.representationAlphaValue b idx : WithTop ℚ) = 0 :=
    le_antisymm hupper hlower
  have hvalue : a.representationAlphaValue b idx = 0 := by
    exact_mod_cast htop
  simpa only [idx, left] using hvalue

/-- Lemma 7.8's first mixed-defect equality with all Section 7 hypotheses
made explicit and no remaining `A_t = 0` premise. -/
theorem beli2019Lemma78_centralMixedDefect_exact
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) :
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
  have hdata := a.beli2019Lemma78_alphas_and_gap
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  have hAlpha := a.beli2019Lemma78_representationAlpha_eq_zero
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
  apply a.beli2019Lemma78_centralMixedDefect_of_alpha_zero
    b D hfirst hAlpha
  exact hdata.2.2

end BONG.GoodBONG

end Bong
