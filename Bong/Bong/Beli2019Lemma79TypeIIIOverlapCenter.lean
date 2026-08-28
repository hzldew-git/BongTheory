/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Dual
import Bong.Bong.Beli2009AlphaArithmetic

/-!
# Beli (2019), Lemma 7.9(ii): the overlapping type-III centre

When the central source gap of a type-III pair is one, the paper regards the
profile as the overlapping type-II/III case.  The classification datatype keeps
this profile in the type-III constructor, so the two central alpha equalities
needed by the type-II-style argument are derived directly here.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the overlapping type-II/III branch, the source central alpha is one. -/
theorem beli2019Lemma79_typeIII_overlap_sourceCenterAlpha_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    a.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1 := by
  let center : Fin (n + 1) :=
    ⟨D.outer.transition.lastZero, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩
  have hgap : a.orderGap center = 1 := by
    simpa only [center] using hoverlap
  have hePos : (0 : Int) < ramificationIndex K := by
    exact_mod_cast ramificationIndex_pos K
  have hgapLe : a.orderGap center ≤
      2 * (ramificationIndex K : Int) := by
    rw [hgap]
    omega
  have hlower := (a.beli2009Lemma27_iii center hgapLe).1
  have hupper : a.alphaValue center ≤ 1 := by
    simpa only [center] using
      a.beli2019Lemma69_i_typeIII
        (alphaV := alpha) (alphaW := alpha) b D hfirst hdefect
  rw [hgap] at hlower
  have hresult : a.alphaValue center = 1 := by
    norm_num at hlower
    linarith
  simpa only [center] using hresult

/-- In the overlapping type-II/III branch, the target central alpha is one. -/
theorem beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hlast : D.outer.last = n + 1)
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
      a.beli2019Lemma69_i_typeIII_target
        b D horder hdefect htotal hlast
  rw [htargetGap] at hlower
  have hresult : b.alphaValue center = 1 := by
    norm_num at hlower
    linarith
  simpa only [center] using hresult

end BONG.GoodBONG

end Bong
