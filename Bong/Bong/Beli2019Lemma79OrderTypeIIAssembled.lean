/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIComplete

/-!
# Beli (2019), Lemma 7.9(i): assembled type-II order condition

The coordinate theorem through the last changed entry combines with the
unchanged suffix to give condition 2.1(i) for the complete type-II branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) for the full type-II branch of Lemma 7.9. -/
theorem beli2019Lemma79_i_typeII_orderCondition
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefect : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  exact BeliOrderLE.of_compare_through_lastDifference
    hacSequence D.outer.lastDifference
      (a.beli2019Lemma79_i_typeII b c D hfirst hac hdefect hnorm)

end BONG.GoodBONG

end Bong
