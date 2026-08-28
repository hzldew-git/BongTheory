/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Remark613TypeIIIRightAlpha
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCenter

/-!
# Beli (2019), Remark 6.13: right alphas from the central equality

The reverse-dual argument only needs the target central alpha to be one.
This formulation applies both to Lemma 7.8's nonoverlap branch and to the
central-gap-one overlap branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The type-III right-alpha formula from the target central alpha equality. -/
theorem beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (htargetCenter : b.alphaValue
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (k : Nat) (hright : D.outer.transition.firstTwo ≤ k)
    (hbeforeLast : k < D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨k, by rw [hlast] at hbeforeLast; omega⟩ = 1 := by
  rcases a.exists_reverseDual_typeIII b D horder hdefect htotal hlast with
    ⟨aDual, bDual, Ddual, _, _, _, hbAlpha, _, _, hdualFirst,
      hdualLeft, _⟩
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let dualCenter : Fin (n + 1) :=
    ⟨Ddual.outer.transition.lastZero, by
      have hbound := Ddual.outer.transition.firstTwo_le_rank
      rw [Ddual.adjacent] at hbound
      omega⟩
  have hreverseCenter : Fin.rev dualCenter = center := by
    apply Fin.ext
    simp only [dualCenter, center, Fin.rev]
    rw [hdualLeft, D.adjacent]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hdualCenterOne : bDual.alphaValue dualCenter = 1 := by
    rw [hbAlpha dualCenter, hreverseCenter]
    simpa only [center] using htargetCenter
  let target : Fin (n + 1) := ⟨k, by
    rw [hlast] at hbeforeLast
    omega⟩
  let dualTarget : Fin (n + 1) := Fin.rev target
  let iDual := dualTarget.val + 2
  have hiDualTwo : 2 ≤ iDual := by
    simp only [iDual]
    omega
  have hiDualLeft : iDual ≤ Ddual.outer.transition.lastZero := by
    simp only [iDual, dualTarget, target, Fin.rev]
    rw [hdualLeft]
    omega
  have hrightProfile := D.outer.rightProfile (by omega)
  have hiDualEven : Even iDual := by
    rcases hrightProfile.1 with ⟨e, he⟩
    rcases hodd with ⟨d, hd⟩
    refine ⟨e - d, ?_⟩
    simp only [iDual, dualTarget, target, Fin.rev]
    rw [hlast] at he hbeforeLast
    omega
  have hdualOne :=
    bDual.lemma78_typeIII_sourcePreviousAlpha_eq_one_of_center
      aDual Ddual hdualFirst hdualCenterOne iDual hiDualTwo hiDualLeft
        hiDualEven
  have hdualOneAt : bDual.alphaValue dualTarget = 1 := by
    convert hdualOne using 1
    apply congrArg bDual.alphaValue
    apply Fin.ext
    simp only [iDual]
    omega
  have hreverseTarget : Fin.rev dualTarget = target := by
    simp only [dualTarget, Fin.rev_rev]
  calc
    b.alphaValue ⟨k, by rw [hlast] at hbeforeLast; omega⟩ =
        b.alphaValue target := by rfl
    _ = b.alphaValue (Fin.rev dualTarget) := by rw [hreverseTarget]
    _ = bDual.alphaValue dualTarget := (hbAlpha dualTarget).symm
    _ = 1 := hdualOneAt

/-- Remark 6.13 on the overlapping type-II/III branch. -/
theorem beli2019Remark613_typeIII_overlap_targetRightAlpha_eq_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (k : Nat) (hright : D.outer.transition.firstTwo ≤ k)
    (hbeforeLast : k < D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨k, by rw [hlast] at hbeforeLast; omega⟩ = 1 := by
  apply a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center
    b D hlast horder hdefect htotal
  · exact a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one
      b D hlast horder hdefect htotal hoverlap
  · exact hright
  · exact hbeforeLast
  · exact hodd

end BONG.GoodBONG

end Bong
