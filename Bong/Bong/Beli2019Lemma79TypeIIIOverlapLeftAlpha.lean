/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenAlphaShiftLeftOuter
import Bong.Bong.Beli2019Lemma79EvenAlphaCloseLeftOuter
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCenter

/-!
# Beli (2019), Lemma 7.9(ii): overlapping type-III left alphas

The generic no-gap left-profile arguments only require that the source alpha
two coordinates earlier is one and that the corresponding target alpha is at
most one.  In the overlap branch the first fact follows from the central
gap-one identity, while the target tail bound is unchanged.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The exact alpha shift on the left interval of an overlapping type-III
profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_alphaShift
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hcenter :=
    a.beli2019Lemma79_typeIII_overlap_sourceCenterAlpha_eq_one
      b D hfirst hdefect hoverlap
  apply lemma79_even_alphaShift_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
      b D hfirst hcenter i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail
      b D hfirst horder hdefect htotal hlast (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  · exact hsmall

/-- Neighboring alpha values are within two units on the overlapping
type-III left interval. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_alphaClose
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hcenter :=
    a.beli2019Lemma79_typeIII_overlap_sourceCenterAlpha_eq_one
      b D hfirst hdefect hoverlap
  apply lemma79_even_alphaClose_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
      b D hfirst hcenter i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail
      b D hfirst horder hdefect htotal hlast (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

end BONG.GoodBONG

end Bong
