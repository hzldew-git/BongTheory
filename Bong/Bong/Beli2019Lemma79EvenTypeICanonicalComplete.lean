/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneReduction
import Bong.Bong.Beli2019Lemma79TypeICaseOneComplete

/-!
# Beli (2019), Lemma 7.9(ii): the complete nonterminal even type-I interval

Condition 2.1(i) normally bounds the cross gap and activates case 3.  Its
unique failure is the first-switch configuration of case 1, now proved for
positive, coincident, and terminal switch intervals.  This theorem performs
that dichotomy internally.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 7000000 in
-- The automatic split elaborates the complete case-one exclusion branch.
/-- Lemma 7.9(ii) at every even coordinate of a nonterminal canonical
type-I interval, without an externally supplied cross-gap bound. -/
theorem beli2019Lemma79_ii_typeI_even_canonical_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hcentralAB : a.CentralRepresentationConditions b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases beli2019Lemma79_typeI_canonical_crossGap_or_caseOne
      a b c D C hfirst horderBC i hiEven hiLeft hiRight with
    hcross | ⟨hleft, hgap, hprevious⟩
  · exact beli2019Lemma79_ii_typeI_even_canonical
      a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
        horderBC hnorm i hi hiEven hiLeft hiRight hcross
  · exact beli2019Lemma79_ii_typeI_caseOne
      a b c D C hfirst horderAB hdefectAB hcentralAB horderAC hdefectAC
        hcentralAC horderBC hnorm i hleft hi.2 hgap hprevious

end BONG.GoodBONG

end Bong
