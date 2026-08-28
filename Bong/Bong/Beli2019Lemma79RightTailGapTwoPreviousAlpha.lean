/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoCoincidentAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the preceding alpha

The two branches `t < t' = u` and `t = t' = u` are assembled here.  In
both, a target gap at `u - 1` no larger than `2e` gives
`beta_(u-1) = alpha_(u-1) + 2`.  Source endpoint monotonicity and the
strict inequality `beta_u < alpha_u` then put the central coefficient
strictly below `beta_(u-1)`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The paper's identity `beta_(u-1) = alpha_(u-1) + 2`, including both
the positive-length and coincident-switch type-I branches. -/
theorem beli2019Lemma79_typeI_caseEight_previousAlpha_eq_add_two_of_gap_le
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hlastPos : 0 < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (hgapLe : b.orderGap ⟨D.profile.last - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨D.profile.last - 1, by omega⟩ =
      a.alphaValue ⟨D.profile.last - 1, by omega⟩ + 2 := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let C := I.canonical
  by_cases hcoincident : C.leftSwitch = D.profile.last
  · exact beli2019Lemma79_typeI_caseEight_coincidentPreviousAlpha_eq_add_two
      a b D C hfirst hcoincident hlastPos hgapTwo hdefect hgapLe
  · have hleftLe : C.leftSwitch ≤ D.profile.last :=
      C.left_le_anchor.trans C.anchor_le_right |>.trans
        I.rightSwitch_eq_last.le
    have hleftLast : C.leftSwitch < D.profile.last :=
      lt_of_le_of_ne hleftLe hcoincident
    exact beli2019Lemma79_typeI_caseEight_terminalPreviousAlpha_eq_add_two
      a b D C hfirst I.rightSwitch_eq_last hleftLast hgapTwo hlast
        horder hdefect H hfirstTail hstrictTail

/-- In the small preceding-gap branch, the central coefficient is strictly
smaller than `beta_(u-1)`. -/
theorem beli2019Lemma79_typeI_caseEight_centralCoefficient_lt_previousAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hlastPos : 0 < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (hgapLe : b.orderGap ⟨D.profile.last - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    ((b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).castSucc -
        b.order (⟨D.profile.last, hlast⟩ : Fin (n + 1)).succ : Int) : Rat) +
        b.alphaValue ⟨D.profile.last, hlast⟩ <
      b.alphaValue ⟨D.profile.last - 1, by omega⟩ := by
  let first : Fin (n + 1) := ⟨D.profile.last, hlast⟩
  let previous : Fin (n + 1) := ⟨D.profile.last - 1, by omega⟩
  have halphaShift :=
    beli2019Lemma79_typeI_caseEight_previousAlpha_eq_add_two_of_gap_le
      a b D hfirst hgapTwo hlast hlastPos horder hdefect H
        hfirstTail hstrictTail hgapLe
  have horders (j : Fin (n + 1)) (hfirstJ : first ≤ j)
      (hjTail : j ≤ tailLast) : a.order j.succ = b.order j.succ := by
    have hjLast : D.profile.last ≤ j.val := by
      change first.val ≤ j.val at hfirstJ
      simpa only [first] using hfirstJ
    have hentry := D.profile.lastDifference.after
      (j.val + 1) (by omega) (by omega)
    rw [a.orderSequence_entryOrZero_eq_order ⟨j.val + 1, by omega⟩,
      b.orderSequence_entryOrZero_eq_order ⟨j.val + 1, by omega⟩]
      at hentry
    have hidx : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) = j.succ := by
      apply Fin.ext
      rfl
    simpa only [hidx] using hentry
  have hstrictFirst : b.alphaValue first < a.alphaValue first :=
    H.targetAlpha_lt_sourceAlpha horders hstrictTail
      first le_rfl hfirstTail
  have hendpoint := a.alphaRightEndpoint_antitone
    (show previous ≤ first by
      change previous.val ≤ first.val
      simp only [previous, first]
      omega)
  have hpSucc : previous.succ = first.castSucc := by
    apply Fin.ext
    simp only [previous, first, Fin.val_succ, Fin.val_castSucc]
    omega
  have hcurrent : b.order first.castSucc = a.order first.castSucc + 2 := by
    have hfirstCast : first.castSucc =
        (⟨D.profile.last, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hfirstCast, ← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hgapTwo
  have hnext : b.order first.succ = a.order first.succ :=
    (horders first le_rfl hfirstTail).symm
  unfold alphaRightEndpoint at hendpoint
  rw [hpSucc] at hendpoint
  have hcurrentQ : (b.order first.castSucc : Rat) =
      (a.order first.castSucc : Rat) + 2 := by
    exact_mod_cast hcurrent
  have hnextQ : (b.order first.succ : Rat) =
      (a.order first.succ : Rat) := by
    exact_mod_cast hnext
  have halphaShift' : b.alphaValue previous =
      a.alphaValue previous + 2 := by
    simpa only [previous] using halphaShift
  push_cast at hendpoint ⊢
  rw [hcurrentQ, hnextQ, halphaShift']
  linarith

end BONG.GoodBONG

end Bong
