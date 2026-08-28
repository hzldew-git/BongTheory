/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69SourceAlphaLocal
import Bong.Bong.Beli2019Lemma78AlphasLocal
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint

/-!
# Beli (2019), Remark 6.13: local type-III right alphas

After reverse duality, an odd right coordinate becomes the coordinate just
before an even left boundary.  Measuring parity from the actual first
unequal dual coordinate removes the former common-suffix normalization.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The type-III right-alpha formula from a target central equality, without
assuming that the last unequal coordinate has full rank. -/
theorem beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
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
    b.alphaValue ⟨k, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 1 := by
  rcases a.exists_reverseDual_typeIII_local b D horder hdefect htotal with
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
    have hlastBound := D.outer.lastDifference.bound
    omega⟩
  let dualTarget : Fin (n + 1) := Fin.rev target
  let iDual := dualTarget.val + 2
  have hdualTargetVal : dualTarget.val = n - k := by
    simp only [dualTarget, target, Fin.rev]
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hiFirst : Ddual.outer.first + 2 ≤ iDual := by
    simp only [iDual, hdualTargetVal]
    rw [hdualFirst]
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hiLeft : iDual ≤ Ddual.outer.transition.lastZero := by
    simp only [iDual, hdualTargetVal]
    rw [hdualLeft]
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hrightProfile := D.outer.rightProfile (by omega)
  have hiEven : Even (iDual - Ddual.outer.first) := by
    rcases hrightProfile.1 with ⟨e, he⟩
    rcases hodd with ⟨d, hd⟩
    refine ⟨e - d, ?_⟩
    simp only [iDual, hdualTargetVal]
    rw [hdualFirst]
    have hlastBound := D.outer.lastDifference.bound
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    omega
  have hdualOne := bDual.lemma69_sourcePreviousAlpha_eq_one_local
    aDual Ddual.outer Ddual.no_gap_two hdualCenterOne iDual hiFirst hiLeft
      hiEven
  have hdualOneAt : bDual.alphaValue dualTarget = 1 := by
    convert hdualOne using 1
    apply congrArg bDual.alphaValue
    apply Fin.ext
    simp only [iDual]
    omega
  have hreverseTarget : Fin.rev dualTarget = target := by
    simp only [dualTarget, Fin.rev_rev]
  calc
    b.alphaValue ⟨k, by
        have hlastBound := D.outer.lastDifference.bound
        omega⟩ = b.alphaValue target := by rfl
    _ = b.alphaValue (Fin.rev dualTarget) := by rw [hreverseTarget]
    _ = bDual.alphaValue dualTarget := (hbAlpha dualTarget).symm
    _ = 1 := hdualOneAt

/-- Remark 6.13 in the nonoverlapping type-III branch, locally. -/
theorem beli2019Remark613_typeIII_targetRightAlpha_eq_one_local
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
        omega⟩)
    (k : Nat) (hright : D.outer.transition.firstTwo ≤ k)
    (hbeforeLast : k < D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨k, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 1 := by
  apply a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
    b D horder hdefect htotal
  · exact (a.beli2019Lemma78_alphas_and_gap_local
      b D hfirst horder hdefect htotal hnotOverlap hinitial).2.1
  · exact hright
  · exact hbeforeLast
  · exact hodd

/-- Remark 6.13 in the overlapping type-III branch, locally. -/
theorem beli2019Remark613_typeIII_overlap_targetRightAlpha_eq_one_local
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
        omega⟩ = 1)
    (k : Nat) (hright : D.outer.transition.firstTwo ≤ k)
    (hbeforeLast : k < D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨k, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 1 := by
  apply a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
    b D horder hdefect htotal
  · exact a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horder hdefect htotal hoverlap
  · exact hright
  · exact hbeforeLast
  · exact hodd

end BONG.GoodBONG

end Bong
