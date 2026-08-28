/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapLocal
import Bong.Bong.Beli2019Lemma79TypeIIICaseSixEndpointLocal
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIComplete

/-!
# Beli (2019), Lemma 7.9(ii): complete local type-III assembly

Before the last unequal order, the local nonoverlap/overlap dispatchers apply.
At the last unequal order, the endpoint theorems cover both a proper suffix and
the full-rank endpoint.  On the common right suffix, case 8 applies.  Hence the
assembled statement has no full-span normalization.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 12000000 in
/-- Lemma 7.9(ii) at every coordinate of a normalized type-III pair,
without assuming that the last unequal order is the final coordinate. -/
theorem beli2019Lemma79_ii_typeIII_pointwise_complete_local
    [Beli2006AlphaLaws.{u, v} K]
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
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases lt_trichotomy i.val D.outer.last with hbefore | hat | hafter
  · by_cases hoverlap : a.orderGap
        ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ = 1
    · exact beli2019Lemma79_ii_typeIII_overlap_pointwise_beforeLast_local
        a b c D hfirst horderAB horderAC horderBC hdefectAB hdefectAC
          htotal hoverlap hnorm i hbefore
    · exact
        beli2019Lemma79_ii_typeIII_pointwise_beforeLast_of_nonoverlap_local
          a b c D hfirst horderAB horderAC horderBC hdefectAB hdefectAC
            htotal hoverlap hinitial hnorm i hbefore
  · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [hat]
      exact D.outer.right_le_last
    have hiEven : Even
        (i.val - (D.outer.transition.firstTwo - 1)) := by
      simpa only [hat] using D.outer.right_even_distance
    by_cases hoverlap : a.orderGap
        ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ = 1
    · exact beli2019Lemma79_ii_typeIII_overlap_caseSix_at_last
        a b c D hfirst horderAB horderBC hdefectAB hdefectAC htotal
          hoverlap hnorm i hat hright hiEven
    · exact beli2019Lemma79_ii_typeIII_caseSix_at_last
        a b c D hfirst horderAB horderBC hdefectAB hdefectAC htotal
          hoverlap hinitial hnorm i hat hright hiEven
  · exact beli2019Lemma79_ii_typeIII_caseEight_gapOne
      a b c D hfirst hinitial hnorm horderAB horderBC hdefectAB
        hdefectAC htotal i (by omega)

end BONG.GoodBONG

end Bong
