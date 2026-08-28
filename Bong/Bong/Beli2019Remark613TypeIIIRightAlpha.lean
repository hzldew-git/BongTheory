/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78PreviousAlpha
import Bong.Bong.Beli2019Lemma78Dual

/-!
# Beli (2019), the right-alpha consequence following Lemma 6.11

The paper observes that the target alpha is one on the alternating right
interval.  Reverse duality turns such a target alpha into a source alpha on
the normalized left interval, where the result was proved in Lemma 6.9(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- On the alternating right interval of a normalized type-III pair, every
target alpha at odd distance from the right transition is exactly one. -/
theorem beli2019Remark613_typeIII_targetRightAlpha_eq_one
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
    b.alphaValue ⟨k, by rw [hlast] at hbeforeLast; omega⟩ = 1 := by
  have hdata := a.beli2019Lemma78_alphas_and_gap
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
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
    simpa only [center] using hdata.2.1
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

end BONG.GoodBONG

end Bong
