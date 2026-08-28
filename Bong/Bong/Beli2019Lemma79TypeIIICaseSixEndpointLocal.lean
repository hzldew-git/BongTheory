/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78TargetLocal
import Bong.Bong.Beli2019Lemma79TypeIICaseSixEndpointLocal
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCaseSixComplete

/-!
# Beli (2019), Lemma 7.9(ii): the proper-suffix type-III endpoint

At a proper-suffix endpoint the coordinates immediately following the last
difference are common.  Lemma 6.3 and Remark 6.16 therefore give the two
candidate comparisons without a full-span assumption.  In the
nonoverlapping second-parity branch, the local first-common-coordinate form
of Lemma 7.8 supplies the exact target prefix needed by sharp
multiplication.  The overlapping branch was already local after the
candidate comparison was removed.
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
-- The first common-suffix coordinate controls the mixed primary prefix.
/-- The primary candidate comparison at a proper-suffix type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_primary_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hiLast.le heven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextBound : i.val + 1 < n + 2 := by omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hAlpha := a.beli2019Lemma63_sameRank_right_value
    b hdefect nextIdx (by
      intro k hk hkn
      exact D.outer.lastDifference.after k (by
        simp only [nextIdx] at hk
        omega) hkn)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i hcurrent hprefix

set_option maxHeartbeats 4000000 in
-- The next order is common and the far prefix is either full or starts in
-- the common suffix.
/-- The optional secondary candidate comparison at a proper-suffix
type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_secondary_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiLast : i.val = D.outer.last)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hcurrentRaw := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hiLast.le heven
  have hnextCommon : a.orderSequence.entryOrZero (i.val + 1) =
      b.orderSequence.entryOrZero (i.val + 1) :=
    D.outer.lastDifference.after (i.val + 1) (by omega) hi.2
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentRaw
  have hnext : b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val + 1, hi.2⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnextCommon.symm
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ + 1 := by
    rw [hcurrent, hnext]
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
      have hAlpha := a.beli2019Lemma63_sameRank_right_value
        b hdefect farIdx (by
          intro k hk hkn
          exact D.outer.lastDifference.after k (by
            simp only [farIdx] at hk
            omega) hkn)
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
  exact representationSecondaryDefect_le_add_one_of_orderSum_eq_add_one
    a b c i hi hsum hprefix

set_option maxHeartbeats 5000000 in
-- The representation-alpha value is the minimum of the three candidates.
/-- The one-unit representation-alpha comparison at a proper-suffix
type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_alpha_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact beli2019Lemma79_typeIII_caseSix_halfGap_le_add_one_complete
      a b c D i hright hiLast.le heven
  · exact
      beli2019Lemma79_typeIII_caseSix_primary_le_add_one_at_last_local
        a b c D hdefect i hiLast hproper hright heven
  · intro hi
    exact
      beli2019Lemma79_typeIII_caseSix_secondary_le_add_one_at_last_local
        a b c D hdefect i hi hiLast hright heven

set_option maxHeartbeats 6000000 in
-- The nonoverlapping beta bound is local; the zero-gamma branch uses only
-- the target/comparison order condition.
/-- The first comparison-prefix parity branch at a proper-suffix
nonoverlapping type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_firstParity_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · have hshift :=
      beli2019Lemma79_typeIII_caseSix_alpha_le_add_one_at_last_local
        a b c D hdefectAB i hiLast hproper hright heven
    have hbeta := beli2019Lemma79_typeIII_caseSix_beta_one_le_local
      a b D hfirst hinitial i hright hiLast.le heven
    exact
      lemma79_caseSix_of_alphaShift_even_and_sourceOdd_of_beta_one_le
        a b c hdefectAC i hshift hbeta
          (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    have hsequence :=
      (b.representationOrderCondition_iff c le_rfl).mp horderBC
    rcases hsequence.compare i.val i.lt_large with
      hcurrent | ⟨hi0, hiNext, hpair⟩
    · apply lemma79_caseSix_of_gamma_eq_zero_and_current_order b c i
      · simpa only [orderSequence_at] using hcurrent
      · simpa only [previous] using hgammaZero
    · exact lemma79_caseSix_of_gamma_eq_zero_and_compare
        b c i hiNext (Or.inr ⟨hi0, hiNext, hpair⟩)
          (by simpa only [previous] using hgammaZero)

set_option maxHeartbeats 6000000 in
-- In the overlap case the central gap itself gives the local beta bound.
/-- The first comparison-prefix parity branch at a proper-suffix
overlapping type-III endpoint. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · have hshift :=
      beli2019Lemma79_typeIII_caseSix_alpha_le_add_one_at_last_local
        a b c D hdefectAB i hiLast hproper hright heven
    have hbeta :=
      beli2019Lemma79_typeIII_overlap_caseSix_beta_one_le_local
        a b D hoverlap i hright hiLast.le heven
    exact
      lemma79_caseSix_of_alphaShift_even_and_sourceOdd_of_beta_one_le
        a b c hdefectAC i hshift hbeta
          (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    have hsequence :=
      (b.representationOrderCondition_iff c le_rfl).mp horderBC
    rcases hsequence.compare i.val i.lt_large with
      hcurrent | ⟨hi0, hiNext, hpair⟩
    · apply lemma79_caseSix_of_gamma_eq_zero_and_current_order b c i
      · simpa only [orderSequence_at] using hcurrent
      · simpa only [previous] using hgammaZero
    · exact lemma79_caseSix_of_gamma_eq_zero_and_compare
        b c i hiNext (Or.inr ⟨hi0, hiNext, hpair⟩)
          (by simpa only [previous] using hgammaZero)

set_option maxHeartbeats 6000000 in
-- Lemma 7.8 is invoked exactly at the first common-suffix coordinate.
/-- The strict mixed-defect branch at a proper-suffix type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_thirdPrefixDefect_eq_mixedShift_at_last_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hmixed :
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ) <
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :
    c.truncatedPrefixDefect c ((-1) ^ ((i.val - 1) / 2)) 0
        (i.val - 1) =
      ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
          a.orderSequence.entryOrZero
            (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
        WithTop ℚ) := by
  let central : Int :=
    b.orderSequence.entryOrZero D.outer.transition.lastZero -
      a.orderSequence.entryOrZero (D.outer.transition.lastZero + 1)
  have hiOdd := beli2019Lemma79_typeIII_caseSix_index_odd
    a b D hfirst i hright heven
  rcases hiOdd with ⟨d, hd⟩
  have hiEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hiEvenLast : Even (D.outer.last + 1) := by
    simpa only [← hiLast] using hiEven
  have htargetRaw :=
    a.beli2019Lemma78_targetPrefixDefect_firstCommon_local
      b D hfirst hdefect hnotOverlap hinitial hproper hiEvenLast
  have hleftBound : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : D.outer.transition.lastZero + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have htarget : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) =
        ((central : ℚ) : WithTop ℚ) := by
    rw [← b.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero, hleftBound⟩,
      ← a.orderSequence_entryOrZero_eq_order
        ⟨D.outer.transition.lastZero + 1, hrightBound⟩] at htargetRaw
    simpa only [hiLast, central] using htargetRaw
  have hseparation : b.truncatedPrefixDefect b
      ((-1) ^ ((i.val + 1) / 2)) 0 (i.val + 1) <
        b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    rw [htarget]
    simpa only [central] using hmixed
  have hsharp := b.truncatedPrefixDefect_mul_eq_left_of_lt_right
    b c ((-1) ^ ((i.val + 1) / 2)) (-1)
      0 (i.val + 1) (i.val - 1) hseparation
  have hexponent : (i.val + 1) / 2 = (i.val - 1) / 2 + 1 := by
    omega
  have hscalar : ((-1 : Kˣ) ^ ((i.val + 1) / 2)) * (-1) =
      (-1) ^ ((i.val - 1) / 2) := by
    rw [hexponent, pow_succ]
    rw [mul_assoc]
    norm_num
  have hzeroLeft := b.truncatedPrefixDefect_zero_left_eq_self
    c ((-1) ^ ((i.val - 1) / 2)) (i.val - 1)
  rw [hscalar, hzeroLeft, htarget] at hsharp
  simpa only [central] using hsharp

set_option maxHeartbeats 7000000 in
-- Only the strict-mixed branch differs from the already local profile proof.
/-- The opposite-current-parity branch at a proper-suffix nonoverlap
endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_opposite_at_last_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hmixed : b.truncatedPrefixDefect c (-1)
      (i.val + 1) (i.val - 1) ≤
    ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ)
  · exact beli2019Lemma79_typeIII_caseSix_secondParity_of_mixed_le
      a b c D hfirst hdefect hnotOverlap hnorm i hright hiLast.le
        heven horders hmixed
  · have hmixedStrict :
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) <
          b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) :=
      lt_of_not_ge hmixed
    have hthird :=
      beli2019Lemma79_typeIII_caseSix_thirdPrefixDefect_eq_mixedShift_at_last_local
        a b c D hfirst hdefect hnotOverlap hinitial i hiLast hproper
          hright heven hmixedStrict
    rcases beli2019Lemma79_typeIII_caseSix_secondParity_or_boundaryWitness
        a b c D hfirst hnorm i hright hiLast.le heven hthird with
      hdone | hboundary
    · exact hdone
    · exact beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryWitness
        a b c D hfirst hdefect hnotOverlap i hright hiLast.le heven
          horders hthird hboundary

set_option maxHeartbeats 8000000 in
-- The same-current-parity profile was already local; the opposite branch
-- now uses the preceding theorem.
/-- The complete second comparison-prefix parity branch at a proper-suffix
nonoverlap endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_at_last_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases modEq_two_or_add_one
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) with hsame | hopposite
  · exact beli2019Lemma79_typeIII_caseSix_secondParity_sameCurrentParity
      a b c D hfirst hdefect hnotOverlap hnorm i hright hiLast.le
        heven hcomparison hsame
  · exact
      beli2019Lemma79_typeIII_caseSix_secondParity_opposite_at_last_local
        a b c D hfirst hdefect hnotOverlap hinitial hnorm i hiLast
          hproper hright heven hopposite

set_option maxHeartbeats 9000000 in
-- Both comparison-prefix parity branches are now local at the endpoint.
/-- Lemma 7.9(ii), case 6, at a proper-suffix nonoverlapping type-III
endpoint. -/
theorem beli2019Lemma79_ii_typeIII_caseSix_at_last_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeIII_caseSix_prefix_opposite
    a b D hfirst hdefectAB hnotOverlap i hright hiLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeIII_caseSix_firstParity_at_last_local
      a b c D hfirst horderBC hdefectAB hdefectAC hinitial i hiLast
        hproper hright heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeIII_caseSix_secondParity_at_last_local
      a b c D hfirst hdefectAB hnotOverlap hinitial hnorm i hiLast
        hproper hright heven hsecondParity.1

set_option maxHeartbeats 8000000 in
-- The overlap second-parity theorem was already independent of full span.
/-- Lemma 7.9(ii), case 6, at a proper-suffix overlapping type-III
endpoint. -/
theorem beli2019Lemma79_ii_typeIII_overlap_caseSix_at_last_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeIII_overlap_caseSix_prefix_opposite
    a b D hfirst hoverlap i hright hiLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact
      beli2019Lemma79_typeIII_overlap_caseSix_firstParity_at_last_local
        a b c D horderBC hdefectAB hdefectAC hoverlap i hiLast hproper
          hright heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeIII_overlap_caseSix_secondParity
      a b c D hfirst hoverlap hnorm i hright hiLast.le heven
        hsecondParity.1

set_option maxHeartbeats 10000000 in
-- Split only on whether the last difference is the full-rank endpoint.
/-- Lemma 7.9(ii), case 6, at the last unequal nonoverlapping type-III
coordinate, with no full-span hypothesis. -/
theorem beli2019Lemma79_ii_typeIII_caseSix_at_last
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hfull : D.outer.last = n + 1
  · exact beli2019Lemma79_ii_typeIII_caseSix_endpointComplete
      a b c D hfirst hfull horderAB horderBC hdefectAB hdefectAC
        htotal hnotOverlap hinitial hnorm i hright hiLast.le heven
  · have hproper : D.outer.last < n + 1 := by
      have hlastBound := D.outer.lastDifference.bound
      omega
    exact beli2019Lemma79_ii_typeIII_caseSix_at_last_local
      a b c D hfirst horderBC hdefectAB hdefectAC hnotOverlap hinitial
        hnorm i hiLast hproper hright heven

set_option maxHeartbeats 10000000 in
-- The same full/proper split completes the overlap endpoint.
/-- Lemma 7.9(ii), case 6, at the last unequal overlapping type-III
coordinate, with no full-span hypothesis. -/
theorem beli2019Lemma79_ii_typeIII_overlap_caseSix_at_last
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
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
    (hiLast : i.val = D.outer.last)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hfull : D.outer.last = n + 1
  · exact beli2019Lemma79_ii_typeIII_overlap_caseSix_endpointComplete
      a b c D hfirst hfull horderAB horderBC hdefectAB hdefectAC
        htotal hoverlap hnorm i hright hiLast.le heven
  · have hproper : D.outer.last < n + 1 := by
      have hlastBound := D.outer.lastDifference.bound
      omega
    exact beli2019Lemma79_ii_typeIII_overlap_caseSix_at_last_local
      a b c D hfirst horderBC hdefectAB hdefectAC hoverlap hnorm i
        hiLast hproper hright heven

end BONG.GoodBONG

end Bong
