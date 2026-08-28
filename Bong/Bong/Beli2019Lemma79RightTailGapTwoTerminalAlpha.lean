/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIFromConditions
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEndpointWeight

/-!
# Beli (2019), Lemma 7.9(ii), case 8: terminal type-I alpha identity

The endpoint weight estimate from the strict case-8 branch replaces the
nonterminal right-tail estimate in Lemma 6.9(v).  Interval rigidity then
remains unchanged and yields the identity `beta_(u-1) = alpha_(u-1) + 2`
when the two canonical type-I switches are distinct.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Terminal case-8 form of Lemma 6.9(v), valid throughout the nonempty
canonical type-I interval ending at the last unequal coordinate. -/
theorem beli2019Lemma69_v_typeI_of_rightSwitch_eq_last_caseEight
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    a.alphaLeftEndpoint ⟨k, by omega⟩ =
      b.alphaLeftEndpoint ⟨k, by omega⟩ := by
  have hW := a.weightSequence_le_of_representationConditions
    b horder hdefect
  have hstrict : C.leftSwitch < C.rightSwitch := hleft.trans_lt hright
  have hleftNeighbor : 0 < C.leftSwitch →
      b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
        a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
    intro hleftPos
    exact beli2019Lemma69_v_typeI_leftNeighbor
      a b D C hfirst hleftPos hdefect
  have hrightNeighbor : C.rightSwitch < n + 1 →
      b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
        a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2 := by
    intro _
    simpa only [hrightLast] using
      beli2019Lemma79_typeI_caseEight_terminalRightNeighbor
        a b D hgapTwo hlast H hfirstTail hstrictTail
  have hleftBoundary := lemma69_v_typeI_leftBoundary_of_previous
    a b D C hfirst hstrict hW hleftNeighbor
  have hrightBoundary := lemma69_v_typeI_rightBoundary_of_next
    a b D C hfirst hstrict hW hrightNeighbor
  have hsum := lemma69_v_typeI_weightSegmentSum_eq a b D C hfirst
  exact beli2019Lemma69_v_typeI_of_interval a b D C hW
    hleftBoundary hrightBoundary hsum k hleft hright

/-- In the positive-length terminal type-I interval, the alpha immediately
before `u` satisfies the paper's identity `beta_(u-1) = alpha_(u-1) + 2`. -/
theorem beli2019Lemma79_typeI_caseEight_terminalPreviousAlpha_eq_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch = D.profile.last)
    (hleftLast : C.leftSwitch < D.profile.last)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.profile.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast) :
    b.alphaValue ⟨D.profile.last - 1, by omega⟩ =
      a.alphaValue ⟨D.profile.last - 1, by omega⟩ + 2 := by
  have hleftPrevious : C.leftSwitch ≤ D.profile.last - 1 := by
    rcases C.left_even with ⟨dl, hdl⟩
    have hlastEven : Even D.profile.last := by
      rw [← hrightLast]
      exact C.right_even
    rcases hlastEven with ⟨dr, hdr⟩
    omega
  have hweight :=
    beli2019Lemma69_v_typeI_of_rightSwitch_eq_last_caseEight
      a b D C hfirst hrightLast hgapTwo hlast horder hdefect
        H hfirstTail hstrictTail (D.profile.last - 1)
        hleftPrevious (by rw [hrightLast]; omega)
  have hpreviousOdd : Odd (D.profile.last - 1) := by
    have hlastEven : Even D.profile.last := by
      rw [← hrightLast]
      exact C.right_even
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hentry := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (D.profile.last - 1) hpreviousOdd
      hleftPrevious (by rw [hrightLast]; omega)
  let p : Fin (n + 1) := ⟨D.profile.last - 1, by omega⟩
  have horderShift : a.order p.castSucc = b.order p.castSucc + 2 := by
    have hpCast : p.castSucc =
        (⟨D.profile.last - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hpCast, ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have horderShiftQ : (a.order p.castSucc : Rat) =
      (b.order p.castSucc : Rat) + 2 := by
    exact_mod_cast horderShift
  have hweight' : a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
    simpa only [p] using hweight
  unfold alphaLeftEndpoint at hweight'
  rw [horderShiftQ] at hweight'
  simpa only [p] using (show b.alphaValue p = a.alphaValue p + 2 by
    linarith)

end BONG.GoodBONG

end Bong
