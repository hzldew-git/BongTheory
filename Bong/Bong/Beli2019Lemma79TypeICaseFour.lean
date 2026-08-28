/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeISourceCentral
import Bong.Bong.Beli2019Lemma79TypeIRightSource

/-!
# Beli (2019), Lemma 7.9(ii): complete type-I case 4

The central interval and right tail partition the odd boundaries from the
canonical left switch up to the last unequal order. This file combines the
two proofs into the complete case 4 of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 4: type I and an odd boundary in the complete
interval from the left transition through the right tail. -/
theorem beli2019Lemma79_ii_typeI_caseFour
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hlast : i.val < D.profile.last) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hcentral : i.val - 1 < C.rightSwitch
  · exact beli2019Lemma79_ii_typeI_centralOdd
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        horderBC hnorm i hodd hleft hcentral
  · have hipos := i.pos
    have hright : C.rightSwitch < i.val := by omega
    exact beli2019Lemma79_ii_typeI_rightOdd
      a b c D C hfirst hrightLast hdefectAB hdefectAC horderBC
        hnorm i hright hlast hodd

end BONG.GoodBONG

end Bong
