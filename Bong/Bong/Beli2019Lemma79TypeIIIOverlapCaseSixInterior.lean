/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixInteriorAssembly
import Bong.Bong.Beli2019Lemma69TypeIIIRightValueOfCenter
import Bong.Bong.Beli2019Remark613TypeIIIRightAlphaOfCenter

/-!
# Beli (2019), Lemma 7.9(ii), overlapping type-III case 6

The central source gap is one in the overlap branch.  Consequently both
central alphas are one, and the right-hand Lemma 6.9 and Remark 6.13 formulas
give exactly the cap and candidate estimates used in the first parity branch
of case 6.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The target cap is one on the case-6 parity class in the overlapping
type-III profile, including its central boundary coordinate. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_beta_eq_one
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.alphaValue ⟨i.val - 1, by omega⟩ = 1 := by
  by_cases hboundary : i.val = D.outer.transition.firstTwo - 1
  · have hindex : i.val - 1 = D.outer.transition.lastZero := by
      rw [hboundary, D.adjacent]
      omega
    simpa only [hindex] using
      a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one
        b D hlast horder hdefect htotal hoverlap
  · rcases heven with ⟨d, hd⟩
    have hdPositive : 0 < d := by omega
    have hiInterior : D.outer.transition.firstTwo ≤ i.val - 1 := by
      omega
    have hoddPrevious : Odd
        ((i.val - 1) - (D.outer.transition.firstTwo - 1)) :=
      ⟨d - 1, by omega⟩
    exact beli2019Remark613_typeIII_overlap_targetRightAlpha_eq_one
      a b D hlast horder hdefect htotal hoverlap
        (i.val - 1) hiInterior (by omega) hoddPrevious

set_option maxHeartbeats 4000000 in
/-- The primary candidate comparison in overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_primary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hbeforeLast.le heven
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextBound : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hleftEven : Even D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hnextEven : Even nextIdx.val := by
    rcases hleftEven with ⟨p, hp⟩
    rcases heven with ⟨d, hd⟩
    refine ⟨p + d + 1, ?_⟩
    simp only [nextIdx]
    have hbase : D.outer.transition.firstTwo - 1 =
        D.outer.transition.lastZero + 1 := by
      rw [D.adjacent]
      omega
    have hiEq : i.val =
        (D.outer.transition.firstTwo - 1) + (d + d) := by
      omega
    omega
  have hnextStart : D.outer.transition.lastZero + 2 ≤ nextIdx.val := by
    simp only [nextIdx]
    rw [← D.adjacent]
    have hseparated := D.outer.transition.separated
    omega
  have hAlpha := a.beli2019Lemma69_ii_typeIII_targetRightValue_of_overlap
    b D hfirst hlast horder hdefect htotal hoverlap
      nextIdx.val hnextStart hnextEven nextIdx.lt_large
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i horderShift hprefix

set_option maxHeartbeats 4000000 in
/-- The secondary candidate comparison in nonterminal overlapping
type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondary_le_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hfarThrough : i.val + 2 ≤ D.outer.last := by
    rcases heven with ⟨d, hd⟩
    rcases D.outer.right_even_distance with ⟨e, he⟩
    omega
  have hfarBound : i.val + 2 < n + 2 := by
    rw [hlast] at hfarThrough
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarRight : D.outer.transition.firstTwo - 1 ≤ farIdx.val := by
    simp only [farIdx]
    omega
  have hfarEven : Even
      (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hbeta := beli2019Lemma79_typeIII_overlap_caseSix_beta_eq_one
    a b D hlast horder hdefect htotal hoverlap farIdx hfarRight
      (by simpa only [farIdx] using hfarThrough) hfarEven
  apply lemma79_caseSix_profile_secondary_le_add_one
    a b c D.outer D.no_gap_two i hi hright hfarThrough heven
  simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
    using hbeta

set_option maxHeartbeats 5000000 in
/-- The one-unit alpha comparison in nonterminal overlapping type-III
case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_alpha_le_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact lemma79_caseSix_profile_halfGap_le_add_one
      a b c D.outer D.no_gap_two i hright hbeforeLast heven
  · exact beli2019Lemma79_typeIII_overlap_caseSix_primary_le_add_one
      a b c D hfirst hlast horder hdefect htotal hoverlap
        i hright hbeforeLast heven
  · intro hi
    exact beli2019Lemma79_typeIII_overlap_caseSix_secondary_le_add_one
      a b c D hlast horder hdefect htotal hoverlap
        i hi hright hbeforeLast heven

set_option maxHeartbeats 6000000 in
/-- The positive-third-alpha part of the first parity branch in
nonterminal overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_ge_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hgamma : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hshift := beli2019Lemma79_typeIII_overlap_caseSix_alpha_le_add_one
    a b c D hfirst hlast horder hdefectAB htotal hoverlap
      i hright hbeforeLast heven
  have hbeta := beli2019Lemma79_typeIII_overlap_caseSix_beta_eq_one
    a b D hlast horder hdefectAB htotal hoverlap
      i hright hbeforeLast.le heven
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

end BONG.GoodBONG

end Bong
