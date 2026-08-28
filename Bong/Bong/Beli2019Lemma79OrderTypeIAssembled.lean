/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIComplete

/-!
# Beli (2019), Lemma 7.9(i): assembled type-I order condition

The coordinate theorem through the last changed entry combines with the
unchanged suffix to give condition 2.1(i) for the complete type-I branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) for the full type-I branch of Lemma 7.9. -/
theorem beli2019Lemma79_i_typeI_orderCondition
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have _ := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp horderAC
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  exact BeliOrderLE.of_compare_through_lastDifference
    hacSequence D.profile.lastDifference
      (beli2019Lemma79_i_typeI a b c D C hfirst horderAB horderAC
        hdefectAB hdefectAC hinitial hnorm)

end BONG.GoodBONG

end Bong
