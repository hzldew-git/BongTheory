/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapLeftComplete
import Bong.Bong.Beli2019Lemma79DefectTypeIIIOdd
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCaseSixComplete
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapRight

/-!
# Beli (2019), Lemma 7.9(ii): complete overlapping type III

The dispatcher covers the even and odd left classes and the two alternating
right classes.  The final unequal coordinate always belongs to complete
case 6.
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
-- Adjacency leaves only the two left and two right parity classes.
/-- Lemma 7.9(ii) before the final coordinate in overlapping type III. -/
theorem beli2019Lemma79_ii_typeIII_overlap_pointwise_beforeLast
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
      have hiNext : i.val + 1 < n + 2 := by omega
      exact beli2019Lemma79_ii_typeIII_overlap_even_left
        a b c D hfirst hlast horderAB hdefectAB htotal hoverlap
          hdefectAC horderBC hnorm i hiTwo hiNext hiEven hleft
    · exact beli2019Lemma79_ii_typeIII_odd_left
        a b c D hfirst hlast horderAB horderAC hdefectAB htotal hnorm
          i hiOdd (by omega)
  · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [D.adjacent]
      omega
    rcases Nat.even_or_odd
        (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
    · exact beli2019Lemma79_ii_typeIII_overlap_caseSix
        a b c D hfirst hlast horderAB horderAC hdefectAB hdefectAC
          htotal hoverlap hnorm i hright hbeforeLast hiEven
    · have hrightStrict : D.outer.transition.firstTwo ≤ i.val := by
        rcases hiOdd with ⟨d, hd⟩
        omega
      exact beli2019Lemma79_ii_typeIII_overlap_caseSeven
        a b c D hfirst hlast horderAB hdefectAB hdefectAC htotal
          hoverlap hnorm i hrightStrict hbeforeLast hiOdd

set_option maxHeartbeats 11000000 in
-- The final difference is in the even right-profile class.
/-- Lemma 7.9(ii) at every coordinate of normalized overlapping type III. -/
theorem beli2019Lemma79_ii_typeIII_overlap_pointwise_complete
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
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hbeforeLast : i.val < D.outer.last
  · exact beli2019Lemma79_ii_typeIII_overlap_pointwise_beforeLast
      a b c D hfirst hlast horderAB horderAC horderBC hdefectAB
        hdefectAC htotal hoverlap hnorm i hbeforeLast
  · have hiLast : i.val = D.outer.last := by
      have hiBound := i.lt_large
      omega
    have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [hiLast]
      exact D.outer.right_le_last
    have hiEven : Even
        (i.val - (D.outer.transition.firstTwo - 1)) := by
      simpa only [hiLast] using D.outer.right_even_distance
    exact beli2019Lemma79_ii_typeIII_overlap_caseSix_endpointComplete
      a b c D hfirst hlast horderAB horderBC hdefectAB hdefectAC
        htotal hoverlap hnorm i hright hiLast.le hiEven

end BONG.GoodBONG

end Bong
