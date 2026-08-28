/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftComplete
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapLeftSecondary

/-!
# Beli (2019), Lemma 7.9(ii): complete overlapping type-III left interval

The generic left-profile beta assembly applies unchanged after supplying the
overlap-specific alpha and secondary estimates.  Parity then splits the full
even interval into its strict interior and transition endpoint.
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
/-- The beta estimate in the strict even left interior of an overlapping
type-III profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_interior_beta
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
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
  have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail
    b D hfirst horderAB hdefectAB htotal hlast i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeIII_overlap_even_left_alphaShift
      a b D hfirst hlast horderAB hdefectAB htotal hoverlap
        i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_overlap_even_left_secondary
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        i hi' hiEven hfarLeft

/-- Lemma 7.9(ii) in the strict even left interior of an overlapping
type-III profile. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_left_interior
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta :=
    beli2019Lemma79_typeIII_overlap_even_left_interior_beta
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC i hi hiEven hfarLeft
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven (by omega) hbeta

set_option maxHeartbeats 4000000 in
/-- The beta estimate at the even left transition of an overlapping
type-III profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_leftBoundary_beta
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
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
    exact beli2019Lemma79_typeIII_overlap_even_left_alphaShift
      a b D hfirst hlast horderAB hdefectAB htotal hoverlap
        i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_overlap_even_leftBoundary_secondary
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        i hi' hiEven hboundary

/-- Lemma 7.9(ii) at the even left transition of an overlapping type-III
profile. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_leftBoundary
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hbeta :=
    beli2019Lemma79_typeIII_overlap_even_leftBoundary_beta
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven hboundary.le hbeta

/-- Lemma 7.9(ii) on the complete even left interval of an overlapping
type-III profile. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_left
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := ⟨by omega, hiNext⟩
  by_cases hfar : i.val + 2 ≤ D.outer.transition.lastZero
  · exact beli2019Lemma79_ii_typeIII_overlap_even_left_interior
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC hnorm i hi hiEven hfar
  · have hlastEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    have hboundary : i.val = D.outer.transition.lastZero := by omega
    exact beli2019Lemma79_ii_typeIII_overlap_even_leftBoundary
      a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC hnorm i hi ⟨d, hd⟩ hboundary

end BONG.GoodBONG

end Bong
