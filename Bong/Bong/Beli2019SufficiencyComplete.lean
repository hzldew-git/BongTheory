/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019EqualRankComplete
import Bong.Bong.Beli2019SufficiencyCompletion

/-!
# Beli (2019): complete sufficiency in arbitrary rank

The complete equal-rank Sections 7--9 theorem is used directly when the
ranks agree.  In strict unequal rank, Lemmas 2.20--2.21 construct a deep
same-rank completion, to which that same theorem applies.  No theorem-level
`Beli2019FinalStepLaws` assumption occurs here.
-/

namespace Bong

open Dyadic BONG

universe u v w

section Laws

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
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

local instance structuralModelGoodExistence :
    BONGGoodExistenceLaws.{u, u} K :=
  BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralModel)

variable
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
    [deepVV : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K]
    [deepVW : GoodBONGDeepIntegralExtensionLaws.{u, v, w} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]

set_option maxHeartbeats 24000000 in
-- The proof combines the full equal-rank induction with strict-rank completion.
/-- Beli (2019), Theorem 2.1, sufficiency, for every permitted rank pair. -/
theorem beli2019_sufficiency_complete
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (ambient : q.Represents r)
    (conditions : RepresentationConditions a b hRank) :
    Lattice.Represents q r L M := by
  by_cases hequal : n = m
  · let root : Beli2019RepresentationProblem.{u, v, w} K :=
      Beli2019RepresentationProblem.ofData a b hRank ambient conditions
    by_contra hnot
    have hroot : root.Counterexample := by
      change ¬Lattice.Represents q r L M
      exact hnot
    exact (Beli2019RepresentationProblem.not_counterexample_of_equalRank_complete
      (K := K) (defect := defect) (perfect := perfect) (disc := disc)
      (unramified := unramified) (residueDefect := residueDefect)
      (hilbertChoice := hilbertChoice) (unitParity := unitParity)
      (unitSpectrum := unitSpectrum) (hilbert := hilbert)
      (diagonal := diagonal) (structuralModel := structuralModel)
      (goodExistenceModel :=
        BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralModel))
      (structuralV := structuralV) (structuralW := structuralW)
      (scaledModel := scaledModel) (scaledV := scaledV)
      (weight := weight) (unaryBinary := unaryBinary)
      (jordanOrder := jordanOrder)
      (alphaModel := alphaModel) (alphaV := alphaV) (alphaW := alphaW)
      (constructionModel := constructionModel)
      (sectionTwoModel := sectionTwoModel)
      (classificationBase := classificationBase)
      (classificationModel := classificationModel)
      (parityV := parityV) (parityW := parityW)
      (localizationV := localizationV) (localizationW := localizationW)
      (constructionV := constructionV) (constructionW := constructionW)
      (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
      (sectionFourOldV := sectionFourOldV) (corollary44V := corollary44V)
      (binaryLocal := binaryLocal) (lemma49V := lemma49V)
      (lemma49W := lemma49W) (lemma47V := lemma47V)
      (lemma47W := lemma47W)
      (towerRepresentation := towerRepresentation)
      (classificationV := classificationV) (classificationW := classificationW)
      (lemma310VV := lemma310VV) (lemma310VW := lemma310VW)
      (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
      (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
      (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
      (quaternaryScalingV := quaternaryScalingV)
      (quaternaryScalingW := quaternaryScalingW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (deepWW := deepWW)
      root hequal) hroot
  · have hStrict : n < m := by omega
    apply beli2019_strictRank_sufficiency_of_equalRank
      (alphaV := alphaV) (alphaW := alphaW)
      (goodV := BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralV))
      (deepVW := deepVW)
      a b hStrict ambient conditions
    intro C c completedConditions
    let completed : Beli2019RepresentationProblem.{u, v, v} K :=
      Beli2019RepresentationProblem.ofData a c (Nat.le_refl m)
        (QuadraticSpace.represents_refl q) completedConditions
    by_contra hnot
    have hcompleted : completed.Counterexample := by
      change ¬Lattice.Represents q q L C
      exact hnot
    exact (Beli2019RepresentationProblem.not_counterexample_of_equalRank_complete
      (K := K) (defect := defect) (perfect := perfect) (disc := disc)
      (unramified := unramified) (residueDefect := residueDefect)
      (hilbertChoice := hilbertChoice) (unitParity := unitParity)
      (unitSpectrum := unitSpectrum) (hilbert := hilbert)
      (diagonal := diagonal) (structuralModel := structuralModel)
      (goodExistenceModel :=
        BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralModel))
      (structuralV := structuralV) (structuralW := structuralV)
      (scaledModel := scaledModel) (scaledV := scaledV)
      (weight := weight) (unaryBinary := unaryBinary)
      (jordanOrder := jordanOrder)
      (alphaModel := alphaModel) (alphaV := alphaV) (alphaW := alphaV)
      (constructionModel := constructionModel)
      (sectionTwoModel := sectionTwoModel)
      (classificationBase := classificationBase)
      (classificationModel := classificationModel)
      (parityV := parityV) (parityW := parityV)
      (localizationV := localizationV) (localizationW := localizationV)
      (constructionV := constructionV) (constructionW := constructionV)
      (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoV)
      (sectionFourOldV := sectionFourOldV) (corollary44V := corollary44V)
      (binaryLocal := binaryLocal) (lemma49V := lemma49V)
      (lemma49W := lemma49V) (lemma47V := lemma47V)
      (lemma47W := lemma47V)
      (towerRepresentation := towerRepresentation)
      (classificationV := classificationV) (classificationW := classificationV)
      (lemma310VV := lemma310VV) (lemma310VW := lemma310VV)
      (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveV)
      (sectionFourV := sectionFourV) (sectionFourW := sectionFourV)
      (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingV)
      (quaternaryScalingV := quaternaryScalingV)
      (quaternaryScalingW := quaternaryScalingV)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeV)
      (deepWW := deepVV)
      completed rfl) hcompleted

end Laws

end Bong
