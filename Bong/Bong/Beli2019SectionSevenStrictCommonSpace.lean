/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SameRankCommonSpace
import Bong.Bong.Beli2019SectionSevenStrictCore

/-!
# Section 7: returning the strict-gap reduction to the original spaces

The strict first-gap construction is carried out after identifying the two
equal-rank quadratic spaces.  This file transports its resulting index-`p`
reduction back to the original source space.  No representation condition is
assumed during the transport: the source BONGs have literally the same scalar
sequence under the chosen ambient isometry.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

section Laws

variable
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]

/-- The strict-first-gap Section 7 construction for an arbitrary equal-rank
ambient representation.  Its target sublattice remains in the original
target space, while its conditions are transported from the mapped source
BONG back to the original source BONG. -/
noncomputable def sectionSevenStrictIndexPReduction_of_ambient
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hgap : a.order (1 : Fin (n + 2)) -
      a.order (0 : Fin (n + 2)) ≠
        -(2 * (ramificationIndex K : Int)))
    (hnorm : Lattice.normIdeal r M < Lattice.normIdeal q L) :
    Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a b le_rfl ambient conditions) := by
  let D : Beli2019SameRankCommonSpace a b :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  have conditionsImage : RepresentationConditions a D.sourceImageBONG
      le_rfl := D.conditions conditions
  have hnormImage : Lattice.normIdeal q D.sourceImage <
      Lattice.normIdeal q L := by
    change Lattice.normIdeal q
        (Lattice.map D.ambientIsometry.toLinearEquiv M) <
      Lattice.normIdeal q L
    rw [Lattice.normIdeal_map_isometry]
    exact hnorm
  let P := Beli2019RepresentationProblem.ofData
    a D.sourceImageBONG le_rfl (QuadraticSpace.represents_refl q)
      conditionsImage
  letI : AddCommGroup P.Target := P.targetAddCommGroup
  letI : Module K P.Target := P.targetModule
  letI : AddCommGroup P.Source := P.sourceAddCommGroup
  letI : Module K P.Source := P.sourceModule
  let E := beli2019SectionSevenStrictCore a D.sourceImageBONG
    conditionsImage hgap hnormImage
  let R : Beli2019RepresentationProblem.IndexPReduction P := by
    dsimp only [P]
    exact E.indexPReduction conditionsImage
  have conditionsOriginal : RepresentationConditions R.targetBONG b
      le_rfl :=
    (ScalarAgreement.refl R.targetBONG).representationConditions_transport
      D.source_scalarAgreement.symm R.conditions
  exact {
    index_eq := R.index_eq
    lattice := R.lattice
    inclusion := R.inclusion
    targetBONG := R.targetBONG
    conditions := conditionsOriginal }

end Laws

end BONG.GoodBONG

end Bong
