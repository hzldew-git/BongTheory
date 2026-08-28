/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIITargetLocal
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCenter

/-!
# Beli (2019), Lemma 7.8: local type-III central alphas

The source arguments in Lemma 7.8 are already local to the difference
interval.  Replacing only the reverse-dual target bound removes the former
assumption that the last unequal order has full rank.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 7.8's central alpha equalities and numerical gap bound, without a
full-rank hypothesis on the last unequal order. -/
theorem beli2019Lemma78_alphas_and_gap_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
      b.alphaValue ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 ∧
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ + 1 := by
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hsource := a.beli2019Lemma78_sourceAlpha_and_gap
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap hinitial
  have htargetLe : b.alphaValue center ≤ 1 := by
    simpa only [center] using a.beli2019Lemma69_i_typeIII_target_local
      b D horder hdefect htotal
  have hgapEq : b.orderGap center = a.orderGap center := by
    simpa only [center] using a.lemma78_typeIII_targetGap_eq_sourceGap b D
  have hsourceEven : Even (a.orderGap center) := by
    simpa only [center] using a.lemma78_typeIII_centralGap_even
      (alphaV := alpha) (alphaW := alpha)
      b D hfirst hdefect hnotOverlap
  have htargetEven : Even (b.orderGap center) := by
    rw [hgapEq]
    exact hsourceEven
  have hsourceGapBound :
      3 - 2 * (ramificationIndex K : Int) ≤
        a.orderGap center + 1 := by
    simpa only [center] using hsource.2
  have htargetGapGt : -(2 * (ramificationIndex K : Int)) <
      b.orderGap center := by
    rw [hgapEq]
    omega
  have htargetNe : b.alphaValue center ≠ 0 := by
    intro hzero
    have hgapZero := (b.alpha_p2 center).2.mp hzero
    omega
  have htargetIntegral : IsRationalInteger (b.alphaValue center) := by
    apply b.beli2009Corollary28_i center
    rintro ⟨hodd, _⟩
    exact (Int.not_odd_iff_even.mpr htargetEven) hodd
  have htargetEq : b.alphaValue center = 1 := by
    rcases htargetIntegral with ⟨z, hz⟩
    have hzNonnegative : (0 : Int) ≤ z := by
      exact_mod_cast (show (0 : ℚ) ≤ (z : ℚ) by
        simpa only [← hz] using (b.alpha_p2 center).1)
    have hzLe : z ≤ (1 : Int) := by
      exact_mod_cast (show (z : ℚ) ≤ 1 by
        simpa only [← hz] using htargetLe)
    have hzNe : z ≠ 0 := by
      intro hzZero
      apply htargetNe
      rw [hz, hzZero]
      norm_num
    have hzOne : z = 1 := by omega
    rw [hz, hzOne]
    norm_num
  exact ⟨by simpa only [center] using hsource.1,
    by simpa only [center] using htargetEq,
    by simpa only [center] using hsourceGapBound⟩

/-- The target central alpha in the overlapping type-III branch is one,
without a full-rank hypothesis on the last unequal order. -/
theorem beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    b.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 := by
  let center : Fin (n + 1) :=
    ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩
  have hsourceGap : a.orderGap center = 1 := by
    simpa only [center] using hoverlap
  have htargetGap : b.orderGap center = 1 := by
    calc
      b.orderGap center = a.orderGap center := by
        simpa only [center] using
          a.lemma78_typeIII_targetGap_eq_sourceGap b D
      _ = 1 := hsourceGap
  have hePos : (0 : Int) < ramificationIndex K := by
    exact_mod_cast ramificationIndex_pos K
  have hgapLe : b.orderGap center ≤
      2 * (ramificationIndex K : Int) := by
    rw [htargetGap]
    omega
  have hlower := (b.beli2009Lemma27_iii center hgapLe).1
  have hupper : b.alphaValue center ≤ 1 := by
    simpa only [center] using
      a.beli2019Lemma69_i_typeIII_target_local
        b D horder hdefect htotal
  rw [htargetGap] at hlower
  have hresult : b.alphaValue center = 1 := by
    norm_num at hlower
    linarith
  simpa only [center] using hresult

end BONG.GoodBONG

end Bong
