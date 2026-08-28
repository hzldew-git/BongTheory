/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIPointwiseNonterminal
import Bong.Bong.Beli2019Lemma79TypeIIICaseSixEndpointComplete

/-!
# Beli (2019), Lemma 7.9(ii): complete nonoverlapping type III

This combines the interval dispatcher with the full-prefix repair at the last
representation coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 10000000 in
-- The final difference always lies in the even right-profile class.
/-- Lemma 7.9(ii) at every coordinate in normalized nonoverlapping type III. -/
theorem beli2019Lemma79_ii_typeIII_pointwise_complete_of_nonoverlap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
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
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hbeforeLast : i.val < D.outer.last
  · exact beli2019Lemma79_ii_typeIII_pointwise_beforeLast_of_nonoverlap
      a b c D hfirst hlast horderAB horderAC horderBC hdefectAB
        hdefectAC htotal hnotOverlap hinitial hnorm i hbeforeLast
  · have hiLast : i.val = D.outer.last := by
      have hiBound := i.lt_large
      omega
    have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [hiLast]
      exact D.outer.right_le_last
    have hiEven : Even
        (i.val - (D.outer.transition.firstTwo - 1)) := by
      simpa only [hiLast] using D.outer.right_even_distance
    exact beli2019Lemma79_ii_typeIII_caseSix_endpointComplete
      a b c D hfirst hlast horderAB horderBC hdefectAB hdefectAC
        htotal hnotOverlap hinitial hnorm i hright hiLast.le hiEven

end BONG.GoodBONG

end Bong
