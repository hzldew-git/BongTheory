/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIINonoverlapOrderComplete
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrderComplete

/-!
# Beli (2019), Lemma 7.9(i): complete type III

The central source gap is either one, handled by the overlapping branch, or
different from one, handled by the nonoverlapping defect argument.  This file
packages the exhaustive split as a single order-condition theorem, including
profiles with an unchanged suffix after the last difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) for every normalized type-III profile. -/
theorem beli2019Lemma79_i_typeIII_orderCondition
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  by_cases hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1
  · exact a.beli2019Lemma79_i_typeIII_overlap_orderCondition
      b c D hfirst horderAC hdefectAC hoverlap hnorm
  · exact a.beli2019Lemma79_i_typeIII_nonoverlap_orderCondition
      b c D hfirst horderAC hdefectAB hdefectAC hoverlap hinitial hnorm

/-- Condition 2.1(i) for every normalized full-span type-III profile. -/
theorem beli2019Lemma79_i_typeIII_fullSpan_orderCondition
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (_hlast : D.outer.last = n + 1)
    (_horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (_htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  exact a.beli2019Lemma79_i_typeIII_orderCondition
    b c D hfirst horderAC hdefectAB hdefectAC hinitial hnorm

end BONG.GoodBONG

end Bong
