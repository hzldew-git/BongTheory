/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIIInterior

/-!
# Beli (2019), Lemma 7.9(ii), case 3: type-III interior assembly

This is the type-III counterpart of the type-II interior assembly.  The
additional hypotheses are precisely those used by Lemmas 7.8 and 6.9 to
identify the source representation alpha and the preceding alpha values.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- This is the complete scalar estimate in the strict type-III left interior.
/-- The representation alpha is bounded by the preceding type-III target
alpha at every strict even left-interior boundary. -/
theorem beli2019Lemma79_typeIII_even_left_beta
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
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ := by
  have hiTwo : 2 ≤ i.val := by omega
  have hleft : i.val ≤ D.outer.transition.lastZero := by omega
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
    have halpha := beli2019Lemma79_typeIII_even_left_alphaShift
      a b D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial i hiTwo hiEven hleft hsmall
    have hhalf := lemma79_even_leftOuter_halfGap_le_add_two
      a b c D.outer hfirst D.no_gap_two i hiEven hleft
    have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail
      b D hfirst horderAB hdefectAB htotal hlast i.val hleft hiEven
    have hprimary := lemma79_even_leftOuter_primary_le_add_two
      a b c D.outer hfirst D.no_gap_two i hi.2 hiEven hleft
        hcurrentAlpha
    have hsecondary : ∀
        (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
        b.representationSecondaryDefect c i hi' ≤
          a.representationSecondaryDefect c i hi' +
            ((2 : ℚ) : WithTop ℚ) := by
      intro hi'
      exact beli2019Lemma79_typeIII_even_left_secondary
        a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
          hinitial i hi' hiEven hfarLeft
    exact lemma79_even_beta_bound_of_candidate_shifts
      a b c hdefectAC i halpha hhalf hprimary hsecondary

/-- Lemma 7.9(ii), case 3, at every strict even type-III left-interior
boundary. -/
theorem beli2019Lemma79_ii_typeIII_even_left_interior
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
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta := beli2019Lemma79_typeIII_even_left_beta
    a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
      hinitial hdefectAC horderBC i hi hiEven hfarLeft
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven (by omega) hbeta

end BONG.GoodBONG

end Bong
