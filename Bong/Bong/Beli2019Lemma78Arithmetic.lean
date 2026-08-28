/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeIII

/-!
# Beli (2019), Lemma 7.8: central type-III arithmetic

Under the Section 7 assumption `R₂ - R₁ > -2e`, the central type-III
source gap is also strictly above `-2e`.  Lemmas 6.9(i) and 6.11(iii),
together with Corollary 2.8, then force the central source alpha to be one.
The same parity calculation gives the paper's bound `S - R ≥ 3 - 2e`.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The central type-III source gap dominates the initial source gap. -/
theorem lemma78_typeIII_initialGap_le_centralGap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0) :
    a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≤
      a.orderGap ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hsourceLeft : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left := by
    by_cases heq : D.outer.first = left
    · simpa only [hfirst, left] using congrArg
        (fun k ↦ a.orderSequence.entryOrZero k) heq
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := D.outer.leftProfile hlt
      have heqSource := (hp.2.2 left D.outer.first_le_left
        le_rfl hp.1).symm
      simpa only [hfirst, left] using heqSource
  have hoddDistance : Even (right - 1) := by
    rcases hleftEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hsourceOdd := a.orderSequence.entryOrZero_le_of_evenGap
    1 right (by omega) (by omega) hoddDistance
  let initial : Fin n := ⟨0, by omega⟩
  let central : Fin n := ⟨left, hleftBound⟩
  have hinitialGap : a.orderGap initial =
      a.orderSequence.entryOrZero 1 -
        a.orderSequence.entryOrZero 0 := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    congr 1
  have hcentralGap : a.orderGap central =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [central, Fin.val_succ]
    exact hrightEq.symm
  simpa only [initial, central] using (show
    a.orderGap initial ≤ a.orderGap central by
      rw [hinitialGap, hcentralGap, hsourceLeft]
      omega)

/-- In the nonoverlapping type-III branch, the central source gap is even. -/
theorem lemma78_typeIII_centralGap_even
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1) :
    Even (a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩) := by
  let center : Fin n := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let C := a.lemma611TypeIII_of_defect
    (alphaV := alphaV) (alphaW := alphaW)
    b D hfirst hdefect hnotOverlap
  have hcentralFormula : a.orderGap center =
      a.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1) -
        a.orderSequence.entryOrZero
          D.outer.transition.lastZero := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [center, Fin.val_succ]
    rw [D.adjacent]
    omega
  rw [hcentralFormula]
  exact C.central_gap_even

/-- The first two numerical conclusions of Lemma 7.8: the central source
alpha is one and the central gap plus one is at least `3 - 2e`. -/
theorem beli2019Lemma78_sourceAlpha_and_gap
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
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
    a.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 ∧
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ + 1 := by
  let center : Fin n := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have halphaLe : a.alphaValue center ≤ 1 := by
    simpa only [center] using a.beli2019Lemma69_i_typeIII
      (alphaV := alphaV) (alphaW := alphaW) b D hfirst hdefect
  let C := a.lemma611TypeIII_of_defect
    (alphaV := alphaV) (alphaW := alphaW)
    b D hfirst hdefect hnotOverlap
  have hcentralFormula : a.orderGap center =
      a.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1) -
        a.orderSequence.entryOrZero
          D.outer.transition.lastZero := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
        have hbound := D.outer.transition.firstTwo_le_rank
        omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [center, Fin.val_succ]
    rw [D.adjacent]
    omega
  have hgapEven : Even (a.orderGap center) := by
    rw [hcentralFormula]
    exact C.central_gap_even
  have hgapGt : -(2 * (ramificationIndex K : Int)) <
      a.orderGap center := by
    have hmono := lemma78_typeIII_initialGap_le_centralGap
      a b D hfirst
    simpa only [center] using hinitial.trans_le hmono
  have halphaNe : a.alphaValue center ≠ 0 := by
    intro hzero
    have hgapEq := (a.alpha_p2 center).2.mp hzero
    omega
  have halphaIntegral : IsRationalInteger (a.alphaValue center) := by
    apply a.beli2009Corollary28_i center
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr hgapEven) hodd
  have halphaEq : a.alphaValue center = 1 := by
    rcases halphaIntegral with ⟨z, hz⟩
    have hzNonnegative : (0 : Int) ≤ z := by
      exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
        simpa only [← hz] using (a.alpha_p2 center).1)
    have hzLe : z ≤ (1 : Int) := by
      exact_mod_cast (show (z : ℚ) ≤ 1 by
        simpa only [← hz] using halphaLe)
    have hzNe : z ≠ 0 := by
      intro hzZero
      apply halphaNe
      rw [hz, hzZero]
      norm_num
    have hzOne : z = 1 := by omega
    rw [hz, hzOne]
    norm_num
  refine ⟨by simpa only [center] using halphaEq, ?_⟩
  rcases hgapEven with ⟨d, hd⟩
  simpa only [center] using (show
    3 - 2 * (ramificationIndex K : Int) ≤
      a.orderGap center + 1 by omega)

end BONG.GoodBONG

end Bong
