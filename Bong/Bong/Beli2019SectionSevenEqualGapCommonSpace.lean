/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SameRankCommonSpace
import Bong.Bong.Beli2019SectionSevenEqualGap

/-!
# Section 7: returning the equal-gap reduction to the original spaces

The constructive proof of the equal-first-gap branch is most naturally
carried out after the equal-rank source has been mapped into the target
quadratic space.  This file performs that map, invokes the same-space
construction, and transports the resulting four conditions back to the
original source BONG.  The recursive problem therefore keeps its original
source and target carrier types.
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
    [defect : QuadraticDefectLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [unramified : DyadicUnramifiedNormLaws K]
    [residueDefect : DyadicResidueDefectProductLaws K]
    [hilbertChoice : DyadicHilbertDefectChoiceLaws K]
    [unitParity : UnitQuadraticDefectParityLaws K]
    [unitSpectrum : DyadicUnitDefectSpectrumLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [constructionModel : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoModel : Beli2006SectionTwoLaws.{u, u} K]
    [classificationModel : GoodBONGClassificationLaws.{u, u, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [binaryLocal : BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [towerRepresentation :
      DyadicAlternatingEndpointTowerRepresentationLaws K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [lemma310 : Beli2019Lemma310RepresentationLaws.{u, v, v} K]

/-- The equal-first-gap Section 7 construction for an arbitrary equal-rank
ambient representation.  The proof temporarily maps the source into the
target space, but the returned recursive reduction still uses the original
source BONG and quadratic space. -/
theorem exists_sectionSevenEqualGapSublatticeReduction_of_ambient
    (a : GoodBONG q L (n + 3)) (b : GoodBONG r M (n + 3))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hgap : a.order (1 : Fin (n + 3)) -
      a.order (0 : Fin (n + 3)) =
        -(2 * (ramificationIndex K : Int)))
    (hnorm : Lattice.normIdeal r M < Lattice.normIdeal q L) :
    Nonempty (Beli2019RepresentationProblem.SublatticeReduction
      (Beli2019RepresentationProblem.ofData
        a b le_rfl ambient conditions)) := by
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
  have reductionImage : Nonempty
      (Beli2019RepresentationProblem.SublatticeReduction P) := by
    dsimp only [P]
    exact exists_sectionSevenEqualGapSublatticeReduction
      (alphaModel := alphaModel) (alphaV := alphaV)
      (constructionModel := constructionModel)
      (constructionV := constructionV)
      (sectionTwoModel := sectionTwoModel)
      (sectionTwoV := sectionTwoV)
      (classificationModel := classificationModel)
      (classificationV := classificationV)
      a D.sourceImageBONG conditionsImage hgap hnormImage
  rcases reductionImage with ⟨E⟩
  letI : AddCommGroup P.Target := P.targetAddCommGroup
  letI : Module K P.Target := P.targetModule
  letI : AddCommGroup P.Source := P.sourceAddCommGroup
  letI : Module K P.Source := P.sourceModule
  have conditionsOriginal : RepresentationConditions E.targetBONG b
      le_rfl :=
    (ScalarAgreement.refl E.targetBONG).representationConditions_transport
      D.source_scalarAgreement.symm E.conditions
  exact ⟨{
    index_eq := E.index_eq
    lattice := E.lattice
    lattice_le := E.lattice_le
    volumeOrder_lt := E.volumeOrder_lt
    targetBONG := E.targetBONG
    conditions := conditionsOriginal }⟩

end Laws

end BONG.GoodBONG

end Bong
