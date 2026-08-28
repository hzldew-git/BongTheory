/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondaryInterior

/-!
# Beli (2019), Lemma 7.9(ii), case 6: nonterminal assembly

The half-gap, primary, and secondary comparisons now assemble to
`B_i <= C_i + 1`.  In the parity branch where the old comparison defect
vanishes, positivity of the third alpha then proves condition (ii).
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
-- Three dependent candidate comparisons are instantiated simultaneously.
/-- The one-unit comparison `B_i <= C_i + 1` in the type-II
case-6 interval. -/
theorem beli2019Lemma79_typeII_caseSix_alpha_le_add_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
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
  · exact beli2019Lemma79_typeII_caseSix_primary_le_add_one
      a b c D hlast horder hdefect htotal i hright hbeforeLast heven
  · intro hi
    exact beli2019Lemma79_typeII_caseSix_secondary_le_add_one
      a b c D hlast horder hdefect htotal i hi hright hbeforeLast heven

set_option maxHeartbeats 5000000 in
-- Type III carries the additional nonoverlap and initial-gap data.
/-- The one-unit comparison `B_i <= C_i + 1` in the
nonoverlapping type-III case-6 interval. -/
theorem beli2019Lemma79_typeIII_caseSix_alpha_le_add_one
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
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact lemma79_caseSix_profile_halfGap_le_add_one
      a b c D.outer D.no_gap_two i hright hbeforeLast heven
  · exact beli2019Lemma79_typeIII_caseSix_primary_le_add_one
      a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i hright hbeforeLast heven
  · intro hi
    exact beli2019Lemma79_typeIII_caseSix_secondary_le_add_one
      a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i hi hright hbeforeLast heven

set_option maxHeartbeats 5000000 in
-- The candidate assembly is followed by the defect-one closing argument.
/-- The first parity branch of nonterminal type-II case 6, with
positive third alpha. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_ge_one
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
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
  have hshift := beli2019Lemma79_typeII_caseSix_alpha_le_add_one
    a b c D hlast horder hdefectAB htotal i hright hbeforeLast heven
  have hbeta := beli2019Lemma79_typeII_caseSix_beta_eq_one
    a b D hlast horder hdefectAB htotal i hright hbeforeLast.le heven
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

set_option maxHeartbeats 6000000 in
-- The type-III closure retains all data needed by Lemmas 6.9 and 7.8.
/-- The first parity branch of nonterminal nonoverlapping type-III
case 6, with positive third alpha. -/
theorem beli2019Lemma79_typeIII_caseSix_firstParity_of_gamma_ge_one
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
  have hshift := beli2019Lemma79_typeIII_caseSix_alpha_le_add_one
    a b c D hfirst hlast horder hdefectAB htotal hnotOverlap hinitial
      i hright hbeforeLast heven
  have hbeta := beli2019Lemma79_typeIII_caseSix_beta_eq_one
    a b D hfirst hlast horder hdefectAB htotal hnotOverlap hinitial
      i hright hbeforeLast.le heven
  exact lemma79_caseSix_of_alphaShift_even_and_sourceOdd
    a b c hdefectAC i hshift hbeta hgamma hbcEven hacOdd

end BONG.GoodBONG

end Bong
