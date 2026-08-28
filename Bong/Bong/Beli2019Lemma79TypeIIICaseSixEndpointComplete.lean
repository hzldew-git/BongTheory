/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixAssembly
import Bong.Bong.Beli2019Lemma79TypeIRightSourceSecondary

/-!
# Beli (2019), Lemma 7.9(ii): terminal-complete type-III case 6

This is the type-III analogue of the full-prefix repair for type II.  At the
last representation coordinate the primary mixed prefix has full left rank,
and the secondary candidate is absent.  The nonoverlap data remain necessary
for the type-III alpha and parity identities used by the published argument.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The half-gap comparison on the complete type-III case-6 parity class. -/
theorem beli2019Lemma79_typeIII_caseSix_halfGap_le_add_one_complete
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hthroughLast heven
  have horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  exact representationHalfGap_le_add_one_of_order_eq_add_one
    a b c i horder

set_option maxHeartbeats 5000000 in
-- The endpoint mixed prefix is invariant under the full BONG change.
/-- The primary candidate comparison through the last type-III difference. -/
theorem beli2019Lemma79_typeIII_caseSix_primary_le_add_one_complete
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((1 : ℚ) : WithTop ℚ) := by
  by_cases hbeforeLast : i.val < D.outer.last
  · exact beli2019Lemma79_typeIII_caseSix_primary_le_add_one
      a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i hright hbeforeLast heven
  · have hentry := D.outer.target_rightEven_eq_source_add_one
      D.no_gap_two i.val hright hthroughLast heven
    have horderShift : b.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.val, i.lt_large⟩ + 1 := by
      rw [← a.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hentry
    have hfull : i.val + 1 = n + 2 := by omega
    have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
        (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
      simpa only [hfull] using
        (truncatedPrefixDefect_fullLeft_change
          a b c (-1) (i.val - 1)).le
    exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
      a b c i horderShift hprefix

set_option maxHeartbeats 6000000 in
-- An actual secondary candidate supplies the missing strict endpoint bound.
/-- The one-unit alpha comparison on the complete type-III case-6 interval. -/
theorem beli2019Lemma79_typeIII_caseSix_alpha_le_add_one_complete
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact beli2019Lemma79_typeIII_caseSix_halfGap_le_add_one_complete
      a b c D i hright hthroughLast heven
  · exact beli2019Lemma79_typeIII_caseSix_primary_le_add_one_complete
      a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i hright hthroughLast heven
  · intro hi
    have hbeforeLast : i.val < D.outer.last := by omega
    exact beli2019Lemma79_typeIII_caseSix_secondary_le_add_one
      a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i hi hright hbeforeLast heven

set_option maxHeartbeats 7000000 in
-- The terminal zero-alpha alternative follows directly from condition (i)
-- for the target and comparison BONGs.
/-- The first comparison-parity branch through the type-III endpoint. -/
theorem beli2019Lemma79_typeIII_caseSix_firstParity_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
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
  · have hshift := beli2019Lemma79_typeIII_caseSix_alpha_le_add_one_complete
      a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial i hright hthroughLast heven
    have hbeta := beli2019Lemma79_typeIII_caseSix_beta_eq_one
      a b D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial i hright hthroughLast heven
    exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
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

set_option maxHeartbeats 8000000 in
-- The parity dichotomy and both branches now permit equality with `last`.
/-- Lemma 7.9(ii), case 6, on the complete nonoverlapping type-III interval. -/
theorem beli2019Lemma79_ii_typeIII_caseSix_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hprefix := beli2019Lemma79_typeIII_caseSix_prefix_opposite
    a b D hfirst hdefectAB hnotOverlap i hright hthroughLast heven
  rcases caseSix_comparisonPrefix_parity_dichotomy a b c i hprefix with
      hfirstParity | hsecondParity
  · exact beli2019Lemma79_typeIII_caseSix_firstParity_complete
      a b c D hfirst hlast horderAB horderBC hdefectAB hdefectAC
        htotal hnotOverlap hinitial i hright hthroughLast heven
          hfirstParity.1 hfirstParity.2
  · exact beli2019Lemma79_typeIII_caseSix_secondParity
      a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial hnorm i hright hthroughLast heven hsecondParity.1

end BONG.GoodBONG

end Bong
