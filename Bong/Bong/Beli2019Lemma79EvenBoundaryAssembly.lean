/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenBoundarySecondary

/-!
# Beli (2019), Lemma 7.9(ii), case 3: transition assembly

This file assembles the transition secondary estimates with the common
half-gap, primary, cross-gap, alpha-shift, and capped-prefix arguments.  It
completes case 3 at the type-II and type-III left transition boundaries.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- The profile-specific input is isolated to the alpha shift and secondary
-- candidate; all remaining steps are common to types II and III.
/-- Common beta assembly at an even point of a normalized left profile. -/
theorem lemma79_even_leftOuter_beta_of_secondary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hleft : i.val ≤ O.transition.lastZero)
    (htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩)
    (hcurrentAlpha : b.alphaValue ⟨i.val, by omega⟩ ≤ 1)
    (halphaShift : b.orderGap ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ < 2 * (ramificationIndex K : Int) →
      b.alphaValue ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ =
        a.alphaValue ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ + 2)
    (hsecondary : ∀
      (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
      b.representationSecondaryDefect c i hi' ≤
        a.representationSecondaryDefect c i hi' +
          ((2 : ℚ) : WithTop ℚ)) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hsourceLe := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceLe
  by_cases hlarge : 2 * (ramificationIndex K : Int) ≤
      b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩
  · exact lemma79_even_beta_bound_of_large_sourceGap
      b c i hcross hlarge
  · have hsmall : b.orderGap ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ < 2 * (ramificationIndex K : Int) :=
      lt_of_not_ge hlarge
    have halpha := halphaShift hsmall
    have hhalf := lemma79_even_leftOuter_halfGap_le_add_two
      a b c O hfirst hnoTwo i hiEven hleft
    have hprimary := lemma79_even_leftOuter_primary_le_add_two
      a b c O hfirst hnoTwo i hi.2 hiEven hleft hcurrentAlpha
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- The beta estimate at the type-II left transition. -/
theorem beli2019Lemma79_typeII_even_leftBoundary_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hleft : i.val ≤ D.outer.transition.lastZero := hboundary.le
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val - 2) (by omega) hpreviousEven
  have hbCurrent := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two i.val hleft hiEven
  have htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hbPrevious.trans hbCurrent.symm
  have hcurrentAlpha := a.beli2019Lemma69_i_typeII_targetLeftTail
    b D hfirst i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeII_even_left_alphaShift
      a b D hfirst i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeII_even_leftBoundary_secondary
      a b c D hfirst i hi' hboundary

/-- Lemma 7.9(ii), case 3, at the type-II left transition. -/
theorem beli2019Lemma79_ii_typeII_even_leftBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeII_even_leftBoundary_beta
    a b c D hfirst hdefectAC horderBC i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven hboundary.le hbeta

set_option maxHeartbeats 4000000 in
-- Lemmas 7.8 and 6.9 provide the type-III alpha inputs.
/-- The beta estimate at the type-III left transition. -/
theorem beli2019Lemma79_typeIII_even_leftBoundary_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
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
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hleft : i.val ≤ D.outer.transition.lastZero := hboundary.le
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbPrevious := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two (i.val - 2) (by omega) hpreviousEven
  have hbCurrent := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two i.val hleft hiEven
  have htwo : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hbPrevious.trans hbCurrent.symm
  have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail
    b D hfirst horderAB hdefectAB htotal hlast i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeIII_even_left_alphaShift
      a b D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_even_leftBoundary_secondary
      a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial i hi' hiEven hboundary

/-- Lemma 7.9(ii), case 3, at the type-III left transition. -/
theorem beli2019Lemma79_ii_typeIII_even_leftBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
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
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeIII_even_leftBoundary_beta
    a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
      hinitial hdefectAC horderBC i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven hboundary.le hbeta

end BONG.GoodBONG

end Bong
