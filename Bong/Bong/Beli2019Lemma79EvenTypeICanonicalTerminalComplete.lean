/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitchTerminal
import Bong.Bong.Beli2019Lemma79TypeICaseOneComplete
import Bong.Bong.Beli2019Lemma79TypeICaseOneReduction

/-!
# Beli (2019), Lemma 7.9(ii): terminal-complete even type-I interval

The left switch, strict central interval, and right switch now all include
the case in which the canonical right switch is the last unequal order.
This removes the last profile-terminal assumption from the nonterminal even
type-I dispatcher.  The exceptional cross-gap failure is discharged by the
complete case-one theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- The split transports dependent indices through all three complete branches.
/-- Lemma 7.9(ii) at every nonterminal even coordinate in the canonical
type-I interval, assuming the ordinary cross-gap bound. -/
theorem beli2019Lemma79_ii_typeI_even_canonical_from_crossGap_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hrightEq : i.val = C.rightSwitch
  · exact beli2019Lemma79_ii_typeI_even_rightSwitch_complete
      a b c D C hfirst horderAB hdefectAB hdefectAC hnorm
        i hi hiEven hrightEq hcross
  · have hfarRight : i.val + 2 ≤ C.rightSwitch := by
      rcases hiEven with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      omega
    by_cases hleftEq : i.val = C.leftSwitch
    · exact beli2019Lemma79_ii_typeI_even_leftSwitch_complete
        a b c D C hfirst horderAB hdefectAB hdefectAC hnorm
          i hi hiEven hleftEq hfarRight hcross
    · have hiLeftStrict : C.leftSwitch < i.val := by omega
      exact beli2019Lemma79_ii_typeI_even_central_complete
        a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
          hnorm i hi hiEven hiLeftStrict hfarRight

set_option maxHeartbeats 7000000 in
-- The automatic split elaborates the complete case-one exclusion branch.
/-- Lemma 7.9(ii) at every nonterminal even coordinate in the canonical
type-I interval, with no right-profile or cross-gap side condition. -/
theorem beli2019Lemma79_ii_typeI_even_canonical_terminalComplete
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
  · exact
      beli2019Lemma79_ii_typeI_even_canonical_from_crossGap_complete
        a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
          hnorm i hi hiEven hiLeft hiRight hcross
  · exact beli2019Lemma79_ii_typeI_caseOne
      a b c D C hfirst horderAB hdefectAB hcentralAB horderAC hdefectAC
        hcentralAC horderBC hnorm i hleft hi.2 hgap hprevious

end BONG.GoodBONG

end Bong
