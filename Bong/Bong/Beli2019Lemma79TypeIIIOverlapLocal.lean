/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIRightLocal
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapPointwiseComplete

/-!
# Beli (2019), Lemma 7.9(ii): local overlapping type III

The overlapping branch uses its two central alpha equalities in place of
Lemma 7.8's nonoverlap hypothesis.  The remaining left and right profile
arguments are the same local arguments as in nonoverlapping type III.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Local alpha shift on the left interval of an overlapping type-III
profile. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_alphaShift_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail_local
      b D hfirst horder hdefect htotal (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  · exact hsmall

/-- Local neighboring-alpha bound on the overlapping type-III left
interval. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_alphaClose_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail_local
      b D hfirst horder hdefect htotal (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

/-- Local shifted secondary comparison in the strict overlapping left
interior. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_secondary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    (hiEven : Even i.val)
    (hfarLeft : i.val + 2 ≤ D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hfarBound : i.val + 2 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hcenter :=
    a.beli2019Lemma79_typeIII_overlap_sourceCenterAlpha_eq_one
      b D hfirst hdefect hoverlap
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hb := farIdx.lt_large
        omega⟩ := by
    simpa only [farIdx] using
      (a.beli2019Lemma69_ii_typeIII_sourceLeftValue_of_center
        b D hfirst hcenter hdefect (i.val + 2) (by omega)
          hfarLeft hfarEven)
  have hclose :=
    beli2019Lemma79_typeIII_overlap_even_left_alphaClose_local
      a b D hfirst horder hdefect htotal hoverlap farIdx
        (by simp only [farIdx]; omega) hfarEven hfarLeft
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefect i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose)
  exact lemma79_even_leftOuter_secondary_le_add_two_of_prefix
    a b c D.outer hfirst i hi hiEven hfarLeft hprefix

set_option maxHeartbeats 5000000 in
/-- Local shifted secondary comparison at the overlapping type-III left
transition. -/
theorem beli2019Lemma79_typeIII_overlap_even_leftBoundary_secondary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    (hiEven : Even i.val)
    (hboundary : i.val = D.outer.transition.lastZero) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hleftRaw := D.outer.transition.leftBoundary
  have hrightRaw := D.outer.transition.rightBoundary
  have hleft : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1 := by
    simpa only [hboundary] using hleftRaw
  have hright : b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero (i.val + 1) + 1 := by
    rw [D.adjacent] at hrightRaw
    simpa only [hboundary,
      show D.outer.transition.lastZero + 2 - 1 =
        D.outer.transition.lastZero + 1 by omega] using hrightRaw
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero i.val +
        b.orderSequence.entryOrZero (i.val + 1) =
      a.orderSequence.entryOrZero i.val +
        a.orderSequence.entryOrZero (i.val + 1) + 2
    omega
  have hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤
    a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hfarStart : D.outer.transition.firstTwo ≤ farIdx.val := by
        simp only [farIdx]
        rw [D.adjacent, hboundary]
      have hfarParity :
          Odd (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
        exact ⟨0, by simp only [farIdx]; rw [D.adjacent, hboundary]; omega⟩
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            have hb := farIdx.lt_large
            omega⟩ := by
        by_cases hafter : D.outer.last < farIdx.val
        · exact a.beli2019Lemma63_sameRank_right_value
            b hdefect farIdx (by
              intro k hk hkn
              exact D.outer.lastDifference.after k (by omega) hkn)
        · have hfarLast : farIdx.val < D.outer.last := by
            have hfarLE : farIdx.val ≤ D.outer.last := Nat.le_of_not_gt hafter
            by_contra hnot
            have hlastLE : D.outer.last ≤ farIdx.val := Nat.le_of_not_gt hnot
            have hfarEq : farIdx.val = D.outer.transition.firstTwo := by
              simp only [farIdx]
              rw [D.adjacent, hboundary]
            rcases D.outer.right_even_distance with ⟨d, hd⟩
            have hseparated := D.outer.transition.separated
            omega
          have htargetCenter :=
            a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
              b D horder hdefect htotal hoverlap
          exact
            a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
              b D horder hdefect htotal htargetCenter farIdx.val
                hfarStart hfarParity hfarLast
      have hformula := beli2019Remark616_rightMixedPrefix_at
        a b c hdefect farIdx hAlpha 1 (i.val - 2)
      calc
        b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
            min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
              (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
          simpa only [farIdx,
            show i.val + 2 - 1 = i.val + 1 by omega] using hformula
        _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
          min_le_left _ _
  exact representationSecondaryDefect_le_add_two_of_orderSum_eq_add_two
    a b c i hi hsum hprefix

set_option maxHeartbeats 5000000 in
/-- Local beta estimate in the strict even overlapping left interior. -/
theorem beli2019Lemma79_typeIII_overlap_even_left_interior_beta_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst horderAB hdefectAB htotal i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeIII_overlap_even_left_alphaShift_local
      a b D hfirst horderAB hdefectAB htotal hoverlap
        i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_overlap_even_left_secondary_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        i hi' hiEven hfarLeft

/-- Lemma 7.9(ii) in the strict even overlapping left interior, locally. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_left_interior_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    beli2019Lemma79_typeIII_overlap_even_left_interior_beta_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC i hi hiEven hfarLeft
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven (by omega) hbeta

set_option maxHeartbeats 5000000 in
/-- Local beta estimate at the even overlapping type-III left transition. -/
theorem beli2019Lemma79_typeIII_overlap_even_leftBoundary_beta_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  have hcurrentAlpha := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst horderAB hdefectAB htotal i.val hleft hiEven
  apply lemma79_even_leftOuter_beta_of_secondary
    a b c D.outer hfirst D.no_gap_two hdefectAC horderBC
      i hi hiEven hleft htwo hcurrentAlpha
  · intro hsmall
    exact beli2019Lemma79_typeIII_overlap_even_left_alphaShift_local
      a b D hfirst horderAB hdefectAB htotal hoverlap
        i hiTwo hiEven hleft hsmall
  · intro hi'
    exact beli2019Lemma79_typeIII_overlap_even_leftBoundary_secondary_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        i hi' hiEven hboundary

/-- Lemma 7.9(ii) at the even overlapping type-III left transition,
locally. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_leftBoundary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    beli2019Lemma79_typeIII_overlap_even_leftBoundary_beta_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC i hi hiEven hboundary
  exact beli2019Lemma79_ii_typeIII_even_left_of_beta
    a b c D hfirst hnorm i (by omega) hi.2 hiEven hboundary.le hbeta

/-- Lemma 7.9(ii) on the complete even overlapping type-III left interval,
locally. -/
theorem beli2019Lemma79_ii_typeIII_overlap_even_left_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  · exact beli2019Lemma79_ii_typeIII_overlap_even_left_interior_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC hnorm i hi hiEven hfar
  · have hlastEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    have hboundary : i.val = D.outer.transition.lastZero := by omega
    exact beli2019Lemma79_ii_typeIII_overlap_even_leftBoundary_local
      a b c D hfirst horderAB hdefectAB htotal hoverlap
        hdefectAC horderBC hnorm i hi ⟨d, hd⟩ hboundary

set_option maxHeartbeats 4000000 in
/-- The primary candidate comparison in overlapping type-III case 6,
with an arbitrary common suffix. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_primary_le_add_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
      a.representationPrimaryDefect c i +
        ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hbeforeLast.le heven
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextLast : i.val + 1 < D.outer.last := by
    rcases heven with ⟨d, hd⟩
    rcases D.outer.right_even_distance with ⟨e, he⟩
    omega
  have hnextBound : i.val + 1 < n + 2 :=
    hnextLast.trans D.outer.lastDifference.bound
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hnextStart : D.outer.transition.firstTwo ≤ nextIdx.val := by
    simp only [nextIdx]
    have hseparated := D.outer.transition.separated
    omega
  have hnextOdd : Odd
      (nextIdx.val - (D.outer.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have htargetCenter :=
    a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horder hdefect htotal hoverlap
  have hAlpha :=
    a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
      b D horder hdefect htotal htargetCenter nextIdx.val hnextStart
        hnextOdd (by simpa only [nextIdx] using hnextLast)
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
/-- The secondary candidate comparison in local overlapping type-III
case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_secondary_le_add_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
  have htargetCenter :=
    a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horder hdefect htotal hoverlap
  have hbeta : b.alphaValue ⟨i.val + 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 1 := by
    have hrightAlpha : D.outer.transition.firstTwo ≤ i.val + 1 := by
      have hseparated := D.outer.transition.separated
      omega
    have hoddAlpha : Odd
        ((i.val + 1) - (D.outer.transition.firstTwo - 1)) := by
      rcases heven with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    exact
      a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
        b D horder hdefect htotal htargetCenter (i.val + 1)
          hrightAlpha (by omega) hoddAlpha
  apply lemma79_caseSix_profile_secondary_le_add_one
    a b c D.outer D.no_gap_two i hi hright hfarThrough heven hbeta

set_option maxHeartbeats 5000000 in
/-- The one-unit representation-alpha shift in local overlapping
type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_alpha_le_add_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  · exact beli2019Lemma79_typeIII_overlap_caseSix_primary_le_add_one_local
      a b c D hfirst horder hdefect htotal hoverlap
        i hright hbeforeLast heven
  · intro hi
    exact beli2019Lemma79_typeIII_overlap_caseSix_secondary_le_add_one_local
      a b c D horder hdefect htotal hoverlap
        i hi hright hbeforeLast heven

set_option maxHeartbeats 6000000 in
/-- The positive-third-alpha branch of local overlapping type-III
case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_ge_one_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
  have hshift :=
    beli2019Lemma79_typeIII_overlap_caseSix_alpha_le_add_one_local
      a b c D hfirst horder hdefectAB htotal hoverlap
        i hright hbeforeLast heven
  have hbeta :=
    beli2019Lemma79_typeIII_overlap_caseSix_beta_one_le_local
      a b D hoverlap i hright hbeforeLast.le heven
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd_of_beta_one_le
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

/-- The zero-third-alpha branch of local overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_eq_zero_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last)
    (hgamma : c.alphaValue ⟨i.val - 1, by
      have hlastBound := D.outer.lastDifference.bound
      omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiNext : i.val + 1 < n + 2 := by
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hcompare := a.beli2019Lemma79_i_typeIII_overlap_nonterminal
    b c D hfirst hac hdefectAC hoverlap hnorm
      i.val i.lt_large hiNext hbeforeLast.le
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

set_option maxHeartbeats 7000000 in
/-- The complete first-prefix-parity branch in local overlapping
type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hlastBound := D.outer.lastDifference.bound
    omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · exact
      beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_ge_one_local
        a b c D hfirst hab hdefectAB hdefectAC htotal hoverlap
          i hright hbeforeLast heven
            (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    exact
      beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_eq_zero_local
        a b c D hfirst hac hdefectAC hoverlap hnorm i hbeforeLast
          (by simpa only [previous] using hgammaZero)

set_option maxHeartbeats 8000000 in
/-- Complete overlapping type-III case 6 before the last unequal order,
with no full-span normalization. -/
theorem beli2019Lemma79_ii_typeIII_overlap_caseSix_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeIII_overlap_caseSix_prefix_opposite
    a b D hfirst hoverlap i hright hbeforeLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeIII_overlap_caseSix_firstParity_local
      a b c D hfirst hab hac hdefectAB hdefectAC htotal hoverlap
        hnorm i hright hbeforeLast heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeIII_overlap_caseSix_secondParity
      a b c D hfirst hoverlap hnorm i hright hbeforeLast.le heven
        hsecondParity.1

set_option maxHeartbeats 3000000 in
/-- The primary candidate comparison on the local overlapping type-III
case-7 interval. -/
theorem lemma79_typeIII_overlap_right_primary_le_sourcePrimary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i := by
  have horderEntry := D.outer.source_rightOdd_eq_target_add_one
    D.no_gap_two i.val (by omega) hbeforeLast.le hodd
  have hgapOrder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact horderEntry
  have htargetCenter :=
    a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horder hdefect htotal hoverlap
  have hnextAlpha :=
    a.beli2019Remark613_typeIII_targetRightAlpha_eq_one_of_center_local
      b D horder hdefect htotal htargetCenter i.val hright
        hbeforeLast hodd
  have hfarBound : i.val + 1 < n + 2 := by
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hprefixOne :
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
        ((1 : ℚ) : WithTop ℚ) := by
    calc
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
          b.prefixAlphaCap (i.val + 1) :=
        b.truncatedPrefixDefect_le_leftCap c (-1) (i.val + 1)
          (i.val - 1)
      _ = (b.alphaValue ⟨i.val, by omega⟩ : WithTop ℚ) :=
        b.prefixAlphaCap_of_internal (by omega) hfarBound
      _ = ((1 : ℚ) : WithTop ℚ) := by rw [hnextAlpha]
  have hsourceNonneg := a.truncatedPrefixDefect_nonneg
    c (-1) (i.val + 1) (i.val - 1)
  have hcoefficientInt :
      (b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) + 1 =
        a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((1 : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  calc
    _ ≤ (((b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := add_le_add_right hprefixOne _
    _ = (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) :=
      hcoefficient
    _ ≤ _ := le_add_of_nonneg_right hsourceNonneg

set_option maxHeartbeats 4000000 in
/-- The secondary candidate comparison on the local overlapping
type-III case-7 interval. -/
theorem lemma79_typeIII_overlap_right_secondary_le_sourceSecondary_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi := by
  have hpairEntries := D.outer.rightOdd_pair_eq i.val
    (by omega) hbeforeLast.le hodd
  have hsumOrders :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpairEntries
  have hprefix :
      b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) ≤
        a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) := by
    by_cases hfull : i.val + 2 = n + 2
    · simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change a b c 1 (i.val - 2)).le
    · have hfarBound : i.val + 2 < n + 2 := by omega
      let farIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
      have hfarStart : D.outer.transition.firstTwo ≤ farIdx.val := by
        simp only [farIdx]
        omega
      have hfarParity :
          Odd (farIdx.val - (D.outer.transition.firstTwo - 1)) := by
        rcases hodd with ⟨d, hd⟩
        refine ⟨d + 1, ?_⟩
        simp only [farIdx]
        omega
      have hAlpha : a.representationAlphaValue b farIdx =
          b.alphaValue ⟨farIdx.val - 1, by
            simp only [farIdx]
            omega⟩ := by
        by_cases hafter : D.outer.last < farIdx.val
        · exact a.beli2019Lemma63_sameRank_right_value b hdefect farIdx
            (by
              intro k hk hkn
              exact D.outer.lastDifference.after k (by omega) hkn)
        · have hfarLast : farIdx.val < D.outer.last := by
            rcases D.outer.right_even_distance with ⟨e, he⟩
            rcases hfarParity with ⟨d, hd⟩
            have hrightLast := D.outer.right_le_last
            simp only [farIdx] at hafter hfarStart hd ⊢
            omega
          have htargetCenter :=
            a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
              b D horder hdefect htotal hoverlap
          simpa only [farIdx] using
            (a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
              b D horder hdefect htotal htargetCenter farIdx.val
                hfarStart hfarParity hfarLast)
      have hformula := beli2019Remark616_rightMixedPrefix_at
        a b c hdefect farIdx hAlpha 1 (i.val - 2)
      calc
        b.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) =
            min (a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2))
              (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ) := by
          simpa only [farIdx, show i.val + 2 - 1 = i.val + 1 by omega]
            using hformula
        _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) :=
          min_le_left _ _
  have hcoefficientInt :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ := by
    omega
  have hcoefficient :
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
        c.order ⟨i.val - 2, by omega⟩ -
          c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((b.order ⟨i.val, i.lt_large⟩ + b.order ⟨i.val + 1, hi.2⟩ -
          c.order ⟨i.val - 2, by omega⟩ -
            c.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationSecondaryDefect
  rw [← hcoefficient]
  exact add_le_add_right hprefix _

set_option maxHeartbeats 4000000 in
/-- The complete source-alpha comparison on the local overlapping
type-III case-7 interval. -/
theorem lemma79_typeIII_overlap_right_alpha_le_sourceAlpha_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
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
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hhalf := lemma79_typeIII_right_halfGap_le_sourceHalfGap
    a b c D i hright hbeforeLast hodd
  have hprimary :=
    lemma79_typeIII_overlap_right_primary_le_sourcePrimary_local
      a b c D hfirst horder hdefect htotal hoverlap
        i hright hbeforeLast hodd
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeIII_overlap_right_secondary_le_sourceSecondary_local
        a b c D hfirst horder hdefect htotal hoverlap
          i hi hright hbeforeLast hodd)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

set_option maxHeartbeats 4000000 in
/-- Complete overlapping type-III case 7 before the last unequal order,
with no full-span normalization. -/
theorem beli2019Lemma79_ii_typeIII_overlap_caseSeven_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hpreviousBound : i.val - 1 < n + 1 := by
    have hiLarge := i.lt_large
    omega
  have hpreviousOrderBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  have htargetCenter :=
    a.beli2019Lemma79_typeIII_overlap_targetCenterAlpha_eq_one_local
      b D horderAB hdefectAB htotal hoverlap
  have hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, hpreviousBound⟩ := by
    simpa only using
      (a.beli2019Lemma69_ii_typeIII_targetRightValue_of_center_local
        b D horderAB hdefectAB htotal htargetCenter i.val hright
          hodd hbeforeLast)
  by_cases hcurrent : b.order ⟨i.val - 1, hpreviousOrderBound⟩ ≤
      c.order ⟨i.val - 1, hpreviousOrderBound⟩
  · apply lemma79_ii_of_rightMixedPrefix_branches
      a b c hdefectAB hdefectAC i hAlpha
    · intro _
      exact lemma79_typeIII_overlap_right_alpha_le_sourceAlpha_local
        a b c D hfirst horderAB hdefectAB htotal hoverlap
          i hright hbeforeLast hodd
    · intro _
      exact lemma79_rightProfile_beta_bound_of_target_le_comparison
        a b c D.outer i hright hbeforeLast hodd hcurrent
  · have hstrict : c.order ⟨i.val - 1, hpreviousOrderBound⟩ <
        b.order ⟨i.val - 1, hpreviousOrderBound⟩ :=
      lt_of_not_ge hcurrent
    have heq :=
      lemma79_typeIII_overlap_right_comparisonPrefixes_eq_of_comparison_lt_target
        a b c D hfirst hoverlap hnorm i hright hbeforeLast hodd hstrict
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) :=
        lemma79_typeIII_overlap_right_alpha_le_sourceAlpha_local
          a b c D hfirst horderAB hdefectAB htotal hoverlap
            i hright hbeforeLast hodd
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ = b.truncatedPrefixDefect c 1 i.val i.val := heq.symm

set_option maxHeartbeats 10000000 in
/-- Lemma 7.9(ii) at every coordinate before the last unequal order in
overlapping type III, without a full-span normalization. -/
theorem beli2019Lemma79_ii_typeIII_overlap_pointwise_beforeLast_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hleft : i.val ≤ D.outer.transition.lastZero
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiTwo : 2 ≤ i.val := by
        rcases hiEven with ⟨d, hd⟩
        have hiPos := i.pos
        omega
      have hiNext : i.val + 1 < n + 2 := by
        have hlastBound := D.outer.lastDifference.bound
        omega
      exact beli2019Lemma79_ii_typeIII_overlap_even_left_local
        a b c D hfirst horderAB hdefectAB htotal hoverlap
          hdefectAC horderBC hnorm i hiTwo hiNext hiEven hleft
    · exact beli2019Lemma79_ii_typeIII_odd_left_local
        a b c D hfirst horderAB horderAC hdefectAB htotal hnorm
          i hiOdd (by omega)
  · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [D.adjacent]
      omega
    rcases Nat.even_or_odd
        (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
    · exact beli2019Lemma79_ii_typeIII_overlap_caseSix_local
        a b c D hfirst horderAB horderAC hdefectAB hdefectAC
          htotal hoverlap hnorm i hright hbeforeLast hiEven
    · have hrightStrict : D.outer.transition.firstTwo ≤ i.val := by
        rcases hiOdd with ⟨d, hd⟩
        omega
      exact beli2019Lemma79_ii_typeIII_overlap_caseSeven_local
        a b c D hfirst horderAB hdefectAB hdefectAC htotal hoverlap
          hnorm i hrightStrict hbeforeLast hiOdd

end BONG.GoodBONG

end Bong
