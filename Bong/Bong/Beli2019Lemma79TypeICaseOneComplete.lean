/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneTargetRepresentation
import Bong.Bong.Beli2019Lemma79TypeICaseOneExclusion
import Bong.Bong.Beli2019Lemma79TypeICaseOneAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 1: complete exceptional boundary

The two central representation conditions supply the exceptional source and
comparison prefix representations.  The unramified exclusion argument then
forces their determinants into the same square class, and the prefix caps
give condition 2.1(ii) at the boundary.
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
-- The assembly unfolds both central representation triggers and the exclusion proof.
/-- Lemma 7.9(ii), case 1, including the exceptional prefix representations
and the resulting condition 2.1(ii) inequality. -/
theorem beli2019Lemma79_ii_typeI_caseOne
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
    (hnextBound : i.val + 1 < n + 2)
    (hgap : b.orderGap ⟨i.val - 1, by omega⟩ =
      2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hrepB :=
    beli2019Lemma79_typeI_caseOne_sourcePrefixRepresentation
      a b D C hfirst horderAB hdefectAB hcentralAB i hleft hnextBound hgap
  have hrepC :=
    beli2019Lemma79_typeI_caseOne_targetPrefixRepresentation
      a b c D C hfirst horderAB hdefectAB horderAC hdefectAC hcentralAC
        horderBC hnorm i hleft hnextBound hgap hprevious
  have hsquare := beli2019Lemma79_typeI_caseOne_prefixProduct_isSquare
    a b c D C hfirst hnorm i hleft hgap hprevious hrepB hrepC
  exact beli2019Lemma79_ii_typeI_caseOne_of_prefixProduct_isSquare
    b c horderBC i hgap hprevious hsquare

end BONG.GoodBONG

end Bong
