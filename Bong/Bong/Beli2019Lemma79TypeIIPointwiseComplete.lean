/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIPointwiseNonterminal
import Bong.Bong.Beli2019Lemma79TypeIICaseSixEndpointComplete

/-!
# Beli (2019), Lemma 7.9(ii): complete pointwise type-II assembly

The normalized type-II profile spans from the first to the last order
coordinate.  All coordinates before the last difference are covered by the
five published interval cases, while the last coordinate belongs to the even
case-6 parity class and is handled by the full-prefix endpoint theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 9000000 in
-- The endpoint parity is part of the outer-profile consequences.
/-- Lemma 7.9(ii) at every representation coordinate in normalized type II. -/
theorem beli2019Lemma79_ii_typeII_pointwise_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hbeforeLast : i.val < D.outer.last
  · exact beli2019Lemma79_ii_typeII_pointwise_beforeLast
      a b c D hfirst hlast horderAB horderAC horderBC hdefectAB
        hdefectAC htotal hnorm i hbeforeLast
  · have hiLast : i.val = D.outer.last := by
      have hiBound := i.lt_large
      omega
    have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [hiLast]
      exact D.outer.right_le_last
    have hiEven : Even
        (i.val - (D.outer.transition.firstTwo - 1)) := by
      simpa only [hiLast] using D.outer.right_even_distance
    exact beli2019Lemma79_ii_typeII_caseSix_endpointComplete
      a b c D hfirst hlast horderAB horderBC hdefectAB hdefectAC
        htotal hnorm i hright hiLast.le hiEven

end BONG.GoodBONG

end Bong
