/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIPointwiseNonterminal
import Bong.Bong.Beli2019Lemma69TypeIIRightValueLocal
import Bong.Bong.Beli2019Lemma79TypeIICaseSixEndpointLocal

/-!
# Beli (2019), Lemma 7.9(ii): local type-II pointwise assembly

This file replaces the full-span right-profile inputs in cases 6 and 7 by
their local forms.  The left outer interval and the type-II core were
already local; consequently the final pointwise theorem only assumes that
the selected coordinate lies before the last unequal order.
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
/-- The primary case-6 comparison for a type-II pair with an arbitrary
common suffix. -/
theorem beli2019Lemma79_typeII_caseSix_primary_le_add_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
  have hAlpha := a.beli2019Lemma69_ii_typeII_targetRightValue_local
    b D horder hdefect htotal nextIdx.val hnextStart hnextOdd
      (by simpa only [nextIdx] using hnextLast)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i horderShift hprefix

set_option maxHeartbeats 3000000 in
/-- The secondary case-6 comparison for a type-II pair with an arbitrary
common suffix. -/
theorem beli2019Lemma79_typeII_caseSix_secondary_le_add_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    exact a.beli2019Remark613_typeII_targetRightAlpha_eq_one_local
      b D horder hdefect htotal (i.val + 1) hrightAlpha
        (by omega) hoddAlpha
  apply lemma79_caseSix_profile_secondary_le_add_one
    a b c D.outer D.no_gap_two i hi hright hfarThrough heven hbeta

set_option maxHeartbeats 4000000 in
/-- The one-unit representation-alpha shift in type-II case 6, locally. -/
theorem beli2019Lemma79_typeII_caseSix_alpha_le_add_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
  · exact beli2019Lemma79_typeII_caseSix_primary_le_add_one_local
      a b c D horder hdefect htotal i hright hbeforeLast heven
  · intro hi
    exact beli2019Lemma79_typeII_caseSix_secondary_le_add_one_local
      a b c D horder hdefect htotal i hi hright hbeforeLast heven

set_option maxHeartbeats 5000000 in
/-- The positive-third-alpha branch of type-II case 6, locally. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_ge_one_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
  have hshift := beli2019Lemma79_typeII_caseSix_alpha_le_add_one_local
    a b c D horder hdefectAB htotal i hright hbeforeLast heven
  have hbeta := beli2019Lemma79_typeII_caseSix_beta_one_le_local
    a b D i hright hbeforeLast.le heven
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd_of_beta_one_le
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

/-- The zero-third-alpha branch of type-II case 6, locally. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_eq_zero_local
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
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
  have hcompare := a.beli2019Lemma79_i_typeII
    b c D hfirst hac hdefectAC hnorm i.val i.lt_large hbeforeLast.le
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

set_option maxHeartbeats 6000000 in
/-- The first prefix-parity branch of type-II case 6, locally. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
      beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_ge_one_local
        a b c D hab hdefectAB hdefectAC htotal i hright hbeforeLast
          heven (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    exact beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_eq_zero_local
      a b c D hfirst hac hdefectAC hnorm i hbeforeLast
        (by simpa only [previous] using hgammaZero)

/-- Complete type-II case 6 before the last unequal order, locally. -/
theorem beli2019Lemma79_ii_typeII_caseSix_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeII_caseSix_prefix_opposite
    a b D hfirst i hright hbeforeLast.le heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeII_caseSix_firstParity_local
      a b c D hfirst hab hac hdefectAB hdefectAC htotal hnorm
        i hright hbeforeLast heven hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeII_caseSix_secondParity
      a b c D hfirst hnorm i hright hbeforeLast.le heven hsecondParity.1

set_option maxHeartbeats 2000000 in
/-- The primary candidate comparison on the type-II case-7 interval,
without a full-span hypothesis. -/
theorem lemma79_typeII_right_primary_le_sourcePrimary_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
  have hnextAlpha :=
    a.beli2019Remark613_typeII_targetRightAlpha_eq_one_local
      b D horder hdefect htotal i.val hright hbeforeLast hodd
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

set_option maxHeartbeats 3000000 in
/-- The secondary candidate comparison on the local type-II case-7
interval.  If the two-step boundary lies in the common suffix, Lemma 6.3
replaces the right-profile induction. -/
theorem lemma79_typeII_right_secondary_le_sourceSecondary_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
          simpa only [farIdx] using
            (a.beli2019Lemma69_ii_typeII_targetRightValue_local
              b D horder hdefect htotal farIdx.val hfarStart hfarParity
                hfarLast)
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

set_option maxHeartbeats 3000000 in
/-- The complete source-alpha comparison on the local type-II case-7
interval. -/
theorem lemma79_typeII_right_alpha_le_sourceAlpha_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) := by
  have hhalf := lemma79_typeII_right_halfGap_le_sourceHalfGap
    a b c D i hright hbeforeLast hodd
  have hprimary := lemma79_typeII_right_primary_le_sourcePrimary_local
    a b c D horder hdefect htotal i hright hbeforeLast hodd
  rw [b.coe_representationAlphaValue c i,
    a.coe_representationAlphaValue c i,
    b.representationAlpha_eq_min_halfGap_prime c i,
    a.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min hhalf
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 2
  · rw [b.representationAlphaPrime_eq_min_primary_secondary c i hi,
      a.representationAlphaPrime_eq_min_primary_secondary c i hi]
    exact min_le_min hprimary
      (lemma79_typeII_right_secondary_le_sourceSecondary_local
        a b c D horder hdefect htotal i hi hright hbeforeLast hodd)
  · rw [b.representationAlphaPrime_eq_primary_of_not_interior c i hi,
      a.representationAlphaPrime_eq_primary_of_not_interior c i hi]
    exact hprimary

set_option maxHeartbeats 3000000 in
/-- Complete type-II case 7 before the last unequal order, locally. -/
theorem beli2019Lemma79_ii_typeII_caseSeven_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (hodd : Odd (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hpreviousBound : i.val - 1 < n + 1 := by
    have hlastBound := D.outer.lastDifference.bound
    omega
  have hpreviousOrderBound : i.val - 1 < n + 2 := by omega
  have hAlpha : a.representationAlphaValue b i =
      b.alphaValue ⟨i.val - 1, hpreviousBound⟩ := by
    simpa only using
      (a.beli2019Lemma69_ii_typeII_targetRightValue_local
        b D horderAB hdefectAB htotal i.val hright hodd hbeforeLast)
  by_cases hcurrent : b.order ⟨i.val - 1, hpreviousOrderBound⟩ ≤
      c.order ⟨i.val - 1, hpreviousOrderBound⟩
  · apply lemma79_ii_of_rightMixedPrefix_branches
      a b c hdefectAB hdefectAC i hAlpha
    · intro _
      exact lemma79_typeII_right_alpha_le_sourceAlpha_local
        a b c D horderAB hdefectAB htotal i hright hbeforeLast hodd
    · intro _
      exact lemma79_rightProfile_beta_bound_of_target_le_comparison
        a b c D.outer i hright hbeforeLast hodd hcurrent
  · have hstrict : c.order ⟨i.val - 1, hpreviousOrderBound⟩ <
        b.order ⟨i.val - 1, hpreviousOrderBound⟩ :=
      lt_of_not_ge hcurrent
    have heq :=
      lemma79_typeII_right_comparisonPrefixes_eq_of_comparison_lt_target
        a b c D hfirst hnorm i hright hbeforeLast hodd hstrict
    calc
      (b.representationAlphaValue c i : WithTop ℚ) ≤
          (a.representationAlphaValue c i : WithTop ℚ) :=
        lemma79_typeII_right_alpha_le_sourceAlpha_local
          a b c D horderAB hdefectAB htotal i hright hbeforeLast hodd
      _ ≤ a.truncatedPrefixDefect c 1 i.val i.val := hdefectAC i
      _ = b.truncatedPrefixDefect c 1 i.val i.val := heq.symm

set_option maxHeartbeats 9000000 in
/-- Lemma 7.9(ii) at every type-II coordinate strictly before the last
unequal order, with no full-span normalization. -/
theorem beli2019Lemma79_ii_typeII_pointwise_beforeLast_local
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
      exact beli2019Lemma79_ii_typeII_even_left
        a b c D hfirst hdefectAB hdefectAC horderBC hnorm
          i hiTwo hiNext hiEven hleft
    · exact beli2019Lemma79_ii_typeII_odd_left
        a b c D hfirst horderAC hnorm i hiOdd (by omega)
  · have hafterLeft : D.outer.transition.lastZero < i.val := by omega
    by_cases hcore : i.val + 1 < D.outer.transition.firstTwo
    · exact beli2019Lemma79_ii_typeII_core
        a b c D hfirst horderAC hdefectAC hnorm i hafterLeft hcore
    · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
      rcases Nat.even_or_odd
          (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
      · exact beli2019Lemma79_ii_typeII_caseSix_local
          a b c D hfirst horderAB horderAC hdefectAB hdefectAC
            htotal hnorm i hright hbeforeLast hiEven
      · have hrightStrict : D.outer.transition.firstTwo ≤ i.val := by
          rcases hiOdd with ⟨d, hd⟩
          omega
        exact beli2019Lemma79_ii_typeII_caseSeven_local
          a b c D hfirst horderAB hdefectAB hdefectAC htotal
            hnorm i hrightStrict hbeforeLast hiOdd

end BONG.GoodBONG

end Bong
