/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixBetaLocal
import Bong.Bong.Beli2019Lemma79TypeIICaseSixEndpointComplete

/-!
# Beli (2019), Lemma 7.9(ii): the proper-suffix type-II endpoint

When the last unequal coordinate is not the final coordinate of the whole
BONG, the next coordinate belongs to the common suffix.  Lemma 6.3 and
Remark 6.16 then replace the full-prefix argument used at the full-rank
endpoint.  This file also uses only the lower bound `1 ≤ beta_i` needed by
the defect-one closing argument.
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
/-- The primary candidate comparison at a proper-suffix type-II endpoint. -/
theorem beli2019Lemma79_typeII_caseSix_primary_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
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
type-II endpoint. -/
theorem beli2019Lemma79_typeII_caseSix_secondary_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
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
/-- The one-unit representation-alpha comparison at a proper-suffix
type-II endpoint. -/
theorem beli2019Lemma79_typeII_caseSix_alpha_le_add_one_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
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
  · exact beli2019Lemma79_typeII_caseSix_halfGap_le_add_one_complete
      a b c D i hright hiLast.le heven
  · exact
      beli2019Lemma79_typeII_caseSix_primary_le_add_one_at_last_local
        a b c D hdefect i hiLast hproper hright heven
  · intro hi
    exact
      beli2019Lemma79_typeII_caseSix_secondary_le_add_one_at_last_local
        a b c D hdefect i hi hiLast hright heven

/-- The first case-6 parity closing argument with the exact target-alpha
equality weakened to the lower bound actually used in the proof. -/
theorem lemma79_caseSix_of_alphaShift_even_and_sourceOdd_of_beta_one_le
    [Beli2006AlphaLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hshift : (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ))
    (hbeta : (1 : ℚ) ≤ b.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩)
    (hgamma : (1 : ℚ) ≤ c.alphaValue ⟨i.val - 1, by
      have hiBound := i.lt_large
      omega⟩)
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hsourceZero :=
    a.truncatedPrefixDefect_eq_zero_of_odd_order_general
      c 1 i.val i.val (by simpa only [one_mul] using hacOdd)
  have hsourceAlphaNonpos :
      (a.representationAlphaValue c i : WithTop ℚ) ≤ 0 := by
    exact (hdefectAC i).trans_eq hsourceZero
  have htargetAlphaOneTop :
      (b.representationAlphaValue c i : WithTop ℚ) ≤ 1 := by
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) + 1 := hshift
      _ ≤ 0 + 1 := by
        simpa only [add_comm] using
          add_le_add_right hsourceAlphaNonpos (1 : WithTop ℚ)
      _ = 1 := by norm_num
  have htargetAlphaOne : b.representationAlphaValue c i ≤ 1 := by
    exact WithTop.coe_le_coe.mp htargetAlphaOneTop
  exact b.lemma79_ii_of_alpha_le_one_and_even c i htargetAlphaOne
    hbeta hgamma hbcEven

set_option maxHeartbeats 6000000 in
/-- The first comparison-prefix parity branch at a proper-suffix type-II
endpoint. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
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
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · have hshift :=
      beli2019Lemma79_typeII_caseSix_alpha_le_add_one_at_last_local
        a b c D hdefectAB i hiLast hproper hright heven
    have hbeta := beli2019Lemma79_typeII_caseSix_beta_one_le_local
      a b D i hright hiLast.le heven
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
      hcurrent | ⟨i0, hiNext, hpair⟩
    · apply lemma79_caseSix_of_gamma_eq_zero_and_current_order b c i
      · simpa only [orderSequence_at] using hcurrent
      · simpa only [previous] using hgammaZero
    · exact lemma79_caseSix_of_gamma_eq_zero_and_compare
        b c i hiNext (Or.inr ⟨i0, hiNext, hpair⟩)
          (by simpa only [previous] using hgammaZero)

set_option maxHeartbeats 7000000 in
/-- Lemma 7.9(ii), case 6, at a proper-suffix type-II endpoint. -/
theorem beli2019Lemma79_ii_typeII_caseSix_at_last_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hproper : D.outer.last < n + 1)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeII_caseSix_prefix_opposite
    a b D hfirst i hright hiLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeII_caseSix_firstParity_at_last_local
      a b c D horderBC hdefectAB hdefectAC i hiLast hproper hright
        heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeII_caseSix_secondParity
      a b c D hfirst hnorm i hright hiLast.le heven hsecondParity.1

set_option maxHeartbeats 9000000 in
/-- Lemma 7.9(ii), case 6, at the last unequal type-II coordinate,
regardless of whether that coordinate is the full-rank endpoint. -/
theorem beli2019Lemma79_ii_typeII_caseSix_at_last
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiLast : i.val = D.outer.last)
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hfull : D.outer.last = n + 1
  · exact beli2019Lemma79_ii_typeII_caseSix_endpointComplete
      a b c D hfirst hfull horderAB horderBC hdefectAB hdefectAC
        htotal hnorm i hright hiLast.le heven
  · have hproper : D.outer.last < n + 1 := by
      have hlastBound := D.outer.lastDifference.bound
      omega
    exact beli2019Lemma79_ii_typeII_caseSix_at_last_local
      a b c D hfirst horderBC hdefectAB hdefectAC hnorm i hiLast
        hproper hright heven

end BONG.GoodBONG

end Bong
