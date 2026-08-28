/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICanonicalTerminalComplete
import Bong.Bong.Beli2019Lemma79EvenTypeIRightSwitchEndpointComplete
import Bong.Bong.Beli2019Lemma79TypeICaseOneEndpointComplete

/-!
# Beli (2019), Lemma 7.9(ii): endpoint-complete even type-I interval

The only canonical coordinate that can lack a successor order is the right
switch itself.  The endpoint-complete right-switch and case-one theorems
therefore remove the final coordinate restriction from the canonical
dispatcher.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 6000000 in
-- Away from the right switch, its strict upper bound supplies the successor
-- coordinate required by the earlier canonical theorem.
/-- Lemma 7.9(ii) on the complete even canonical type-I interval under the
ordinary cross-gap bound. -/
theorem beli2019Lemma79_ii_typeI_even_canonical_from_crossGap_endpointComplete
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
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch)
    (hcross : b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hiBound : i.val < n + 2 := i.lt_large
          omega⟩ ≤
      2 * (ramificationIndex K : Int)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hrightEq : i.val = C.rightSwitch
  · exact beli2019Lemma79_ii_typeI_even_rightSwitch_endpointComplete
      a b c D C hfirst horderAB hdefectAB hdefectAC hnorm
        i hiEven hrightEq hcross
  · have hiNext : i.val + 1 < n + 2 := by
      have hrightBound :=
        C.right_le_last.trans_lt D.profile.lastDifference.bound
      omega
    exact beli2019Lemma79_ii_typeI_even_canonical_from_crossGap_complete
      a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
        hnorm i ⟨by
          rcases hiEven with ⟨d, hd⟩
          have hiPos := i.pos
          omega, hiNext⟩ hiEven hiLeft hiRight hcross

set_option maxHeartbeats 8000000 in
-- The cross-gap reduction and exceptional case-one proof both include the
-- final internal coordinate.
/-- Lemma 7.9(ii) at every even coordinate in the canonical type-I interval,
with no successor-coordinate or cross-gap side condition. -/
theorem beli2019Lemma79_ii_typeI_even_canonical_endpointComplete
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
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases beli2019Lemma79_typeI_canonical_crossGap_or_caseOne
      a b c D C hfirst horderBC i hiEven hiLeft hiRight with
    hcross | ⟨hleft, hgap, hprevious⟩
  · exact
      beli2019Lemma79_ii_typeI_even_canonical_from_crossGap_endpointComplete
        a b c D C hfirst horderAB hdefectAB hdefectAC horderBC
          hnorm i hiEven hiLeft hiRight hcross
  · exact beli2019Lemma79_ii_typeI_caseOne_endpointComplete
      a b c D C hfirst horderAB hdefectAB hcentralAB horderAC hdefectAC
        hcentralAC horderBC hnorm i hleft hgap hprevious

end BONG.GoodBONG

end Bong
