/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneComplete
import Bong.Bong.Beli2019CanonicalApproximation

/-!
# Beli (2019), Lemma 7.9(ii), case 1: endpoint completion

If the exceptional coordinate is final, its `i + 1` target prefix is the
whole ambient quadratic space.  The required source and comparison prefixes
then represent into that full prefix by the ordinary prefix inclusion followed
by a change of complete BONG.  Thus condition (iii) is only needed in the
proper-prefix branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The exceptional source prefix is represented also when its target is the
complete source BONG. -/
theorem beli2019Lemma79_typeI_caseOne_sourcePrefixRepresentation_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hcentral : a.CentralRepresentationConditions b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1) :
    DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  by_cases hnextBound : i.val + 1 < n + 2
  · exact beli2019Lemma79_typeI_caseOne_sourcePrefixRepresentation
      a b D C hfirst horder hdefect hcentral i hleft hnextBound hgap
  · have hfull : i.val + 1 = n + 2 := by
      have hiBound : i.val < n + 2 := i.lt_large
      omega
    have hprefix := b.prefixValues_represents_of_le
      i.val (n + 2) i.lt_large.le le_rfl
    have hrepresented := hprefix.trans (b.fullPrefix_represents a)
    exact prefixRepresents_cast b a rfl hfull.symm hrepresented

/-- The exceptional comparison prefix is represented also when its target is
the complete source BONG. -/
theorem beli2019Lemma79_typeI_caseOne_targetPrefixRepresentation_endpointComplete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hcentralAC : a.CentralRepresentationConditions c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩) :
    DiagonalRepresents
      (c.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
  by_cases hnextBound : i.val + 1 < n + 2
  · exact beli2019Lemma79_typeI_caseOne_targetPrefixRepresentation
      a b c D C hfirst horderAB hdefectAB horderAC hdefectAC hcentralAC
        horderBC hnorm i hleft hnextBound hgap hprevious
  · have hfull : i.val + 1 = n + 2 := by
      have hiBound : i.val < n + 2 := i.lt_large
      omega
    have hprefix := c.prefixValues_represents_of_le
      i.val (n + 2) i.lt_large.le le_rfl
    have hrepresented := hprefix.trans (c.fullPrefix_represents a)
    exact prefixRepresents_cast c a rfl hfull.symm hrepresented

set_option maxHeartbeats 6000000 in
-- The proper-prefix branch uses condition (iii); the full-prefix branch uses
-- the ambient-space representation proved above.
/-- Lemma 7.9(ii), case 1, including the final internal representation
coordinate. -/
theorem beli2019Lemma79_ii_typeI_caseOne_endpointComplete
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
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound : i.val < n + 2 := i.lt_large
        omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hrepB :=
    beli2019Lemma79_typeI_caseOne_sourcePrefixRepresentation_endpointComplete
      a b D C hfirst horderAB hdefectAB hcentralAB i hleft hgap
  have hrepC :=
    beli2019Lemma79_typeI_caseOne_targetPrefixRepresentation_endpointComplete
      a b c D C hfirst horderAB hdefectAB horderAC hdefectAC hcentralAC
        horderBC hnorm i hleft hgap hprevious
  have hsquare := beli2019Lemma79_typeI_caseOne_prefixProduct_isSquare
    a b c D C hfirst hnorm i hleft hgap hprevious hrepB hrepC
  exact beli2019Lemma79_ii_typeI_caseOne_of_prefixProduct_isSquare
    b c horderBC i hgap hprevious hsquare

end BONG.GoodBONG

end Bong
