/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIPointwiseLocal
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIComplete

/-!
# Beli (2019), Lemma 7.9(ii): complete local type-II assembly

The changed interval is handled by the local pointwise theorem and its
endpoint version.  On the common right suffix, case 8 applies because the
last type-II order gap is exactly one.  Thus no full-span normalization is
needed anywhere in the resulting theorem.
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
/-- Lemma 7.9(ii) at every coordinate of a normalized type-II pair,
without assuming that the last unequal order is the final coordinate. -/
theorem beli2019Lemma79_ii_typeII_pointwise_complete_local
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
    (i : RepresentationIndex (n + 2) (n + 2)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases lt_trichotomy i.val D.outer.last with hbefore | hat | hafter
  · exact beli2019Lemma79_ii_typeII_pointwise_beforeLast_local
      a b c D hfirst horderAB horderAC horderBC hdefectAB hdefectAC
        htotal hnorm i hbefore
  · exact beli2019Lemma79_ii_typeII_caseSix_at_last
      a b c D hfirst horderAB horderBC hdefectAB hdefectAC htotal
        hnorm i hat (by simpa only [hat] using D.outer.right_le_last)
          (by simpa only [hat] using D.outer.right_even_distance)
  · exact beli2019Lemma79_ii_typeII_caseEight_gapOne
      a b c D hfirst hnorm horderAB horderBC hdefectAB hdefectAC
        htotal i (by omega)

end BONG.GoodBONG

end Bong
