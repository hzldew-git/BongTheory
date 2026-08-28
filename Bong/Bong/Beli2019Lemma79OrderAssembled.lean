/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79PointwiseComplete
import Bong.Bong.Beli2019Lemma79OrderTypeIAssembled
import Bong.Bong.Beli2019Lemma79OrderTypeIIAssembled
import Bong.Bong.Beli2019Lemma79TypeIIIOrderComplete

/-!
# Beli (2019), Lemma 7.9(i): three-type assembly

The normalized classification from Section 7 is exhaustive.  The completed
type-I, type-II, and type-III coordinate arguments therefore assemble into
Condition 2.1(i), with no full-span restriction on the last unequal
coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(i), assembled from the normalized three-type classification. -/
theorem beli2019Lemma79_i_of_normalizedClassification
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩)
    (hnormAC : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  cases D with
  | typeI E hfirst =>
      rcases lemma67TypeICanonicalData a b E hfirst with ⟨C⟩
      exact beli2019Lemma79_i_typeI_orderCondition
        a b c E C hfirst horderAB horderAC hdefectAB hdefectAC
          (by simpa using hinitial) hnormAC
  | typeII E hfirst =>
      exact a.beli2019Lemma79_i_typeII_orderCondition
        b c E hfirst horderAC hdefectAC hnormAC
  | typeIII E hfirst htypeInitial =>
      exact a.beli2019Lemma79_i_typeIII_orderCondition
        b c E hfirst horderAC hdefectAB hdefectAC htypeInitial hnormAC

/-- Lemma 7.9(i) directly from the hypotheses that construct Section 7's
normalized classification. -/
theorem beli2019Lemma79_i
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnormAB : Lattice.normIdeal q M < Lattice.normIdeal q L)
    (hnormAC : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩) :
    b.RepresentationOrderCondition c le_rfl := by
  have D := beli2019Lemma79_normalizedClassification
    a b horderAB hdefectAB htotal hnormAB hinitial
  exact beli2019Lemma79_i_of_normalizedClassification
    a b c D horderAB horderAC hdefectAB hdefectAC hinitial hnormAC

end BONG.GoodBONG

end Bong
