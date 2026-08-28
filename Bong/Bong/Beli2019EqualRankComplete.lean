/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019RankTwoComplete
import Bong.Bong.Beli2019EqualRankInduction
import Bong.Bong.Beli2019LowRank

/-!
# Beli (2019): complete equal-rank sufficiency

The unary and binary boundary theorems, the complete Section 7 reduction,
and Section 9 in every rank at least three are substituted into the abstract
rank-volume induction.  No theorem-level final-step law is used.
-/

namespace Bong

open Dyadic BONG

universe u v w

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section Laws

variable
    [defect : QuadraticDefectLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [unramified : DyadicUnramifiedNormLaws K]
    [residueDefect : DyadicResidueDefectProductLaws K]
    [hilbertChoice : DyadicHilbertDefectChoiceLaws K]
    [unitParity : UnitQuadraticDefectParityLaws K]
    [unitSpectrum : DyadicUnitDefectSpectrumLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [goodExistenceModel : BONGGoodExistenceLaws.{u, u} K]
    [scaledModel : ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [scaledV : ScaledHyperbolicMaximalLaws.{u, v, v} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [constructionModel : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoModel : Beli2006SectionTwoLaws.{u, u} K]
    [classificationBase : GoodBONGClassificationLaws.{u, u, u} K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    [localizationV : Beli2009AlphaLocalizationLaws.{u, v} K]
    [localizationW : Beli2009AlphaLocalizationLaws.{u, w} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [constructionW : BeliLemma43ConstructionLaws.{u, w} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionTwoW : Beli2006SectionTwoLaws.{u, w} K]
    [sectionFourOldV : BONGReverseDualLaws.{u, v} K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [binaryLocal : BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma49V : BeliLemma49Laws.{u, v} K]
    [lemma49W : BeliLemma49Laws.{u, w} K]
    [lemma47V : BeliLemma47Laws.{u, v} K]
    [lemma47W : BeliLemma47Laws.{u, w} K]
    [towerRepresentation :
      DyadicAlternatingEndpointTowerRepresentationLaws K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [lemma310VV : Beli2019Lemma310RepresentationLaws.{u, v, v} K]
    [lemma310VW : Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveV : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [binaryScalingV : DyadicBinaryFirstScalingLaws.{u, v} K]
    [binaryScalingW : DyadicBinaryFirstScalingLaws.{u, w} K]
    [quaternaryScalingV : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [quaternaryScalingW : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]

set_option maxHeartbeats 24000000 in
-- The concrete low-rank and Section 7--9 packages are combined once here.
/-- No equal-rank representation problem satisfying the four conditions is a
counterexample. -/
theorem not_counterexample_of_equalRank_complete
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex) : ¬p.Counterexample := by
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  letI : BONGStructuralLaws.{u, v} K := structuralV
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  letI : Beli2019SectionFiveLaws.{u, v} K := sectionFiveV
  letI : Beli2019SectionFourLaws.{u, v} K := sectionFourV
  letI : ScaledHyperbolicMaximalLaws.{u, u, u} K := scaledModel
  letI : ScaledHyperbolicMaximalLaws.{u, v, v} K := scaledV
  apply not_counterexample_of_equalRank_reductions
  · intro current hcurrentIndex hlow
    by_cases hzero : current.sourceIndex = 0
    · exact not_counterexample_of_sourceIndex_eq_zero
        current hcurrentIndex hzero
    · have hone : current.sourceIndex = 1 := by omega
      exact not_counterexample_of_sourceIndex_eq_one
        (alphaV := alphaV) (structuralV := structuralV)
        current hcurrentIndex hone
  · intro current hcurrentIndex hrank hcounterexample
    exact BONG.GoodBONG.sectionSeven_equalNorm_or_counterexampleDescent_of_problem
      (defect := defect) (perfect := perfect) (disc := disc)
      (unramified := unramified) (residueDefect := residueDefect)
      (hilbertChoice := hilbertChoice) (unitParity := unitParity)
      (unitSpectrum := unitSpectrum) (hilbert := hilbert)
      (diagonal := diagonal) (structuralModel := structuralModel)
      (structuralV := structuralV)
      (goodExistenceModel := goodExistenceModel)
      (weight := weight) (unaryBinary := unaryBinary)
      (jordanOrder := jordanOrder) (alphaModel := alphaModel)
      (constructionModel := constructionModel)
      (sectionTwoModel := sectionTwoModel)
      (classificationModel := classificationBase)
      (alphaV := alphaV) (parityV := parityV)
      (constructionV := constructionV) (sectionTwoV := sectionTwoV)
      (sectionFourV := sectionFourOldV) (corollary44V := corollary44V)
      (binaryLocal := binaryLocal) (lemma49 := lemma49V)
      (towerRepresentation := towerRepresentation)
      (classificationV := classificationV) (lemma310 := lemma310VV)
      current hcurrentIndex hrank hcounterexample
  · intro current hcurrentIndex hrank hcounterexample hequal
    exact BONG.GoodBONG.beli2019SectionNine_counterexampleDescent_complete_of_problem
      (disc := disc)
      (scaledModel := scaledModel)
      (constructionV := constructionV) (constructionW := constructionW)
      (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
      (structuralV := structuralV) (structuralW := structuralW)
      (structuralModel := structuralModel)
      (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
      (parityV := parityV) (parityW := parityW)
      (localizationV := localizationV) (localizationW := localizationW)
      (classificationModel := classificationModel)
      (classificationV := classificationV) (classificationW := classificationW)
      (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
      (quaternaryScalingV := quaternaryScalingV)
      (quaternaryScalingW := quaternaryScalingW)
      (lemma49V := lemma49V) (lemma49W := lemma49W)
      (lemma47V := lemma47V) (lemma47W := lemma47W)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
      (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
      (deepWW := deepWW)
      current hcurrentIndex hrank hcounterexample hequal
  · exact hindex

end Laws

end Beli2019RepresentationProblem

end Bong
