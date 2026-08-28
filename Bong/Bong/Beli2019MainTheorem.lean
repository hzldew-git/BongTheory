/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019NecessityComplete
import Bong.Bong.Beli2019SufficiencyComplete
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.Beli2019UnaryBinaryJordanProof
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Bong.Beli2019SectionFourLaws
import Bong.Bong.Beli2019SectionFiveComplete
import Bong.Bong.Beli2019Lemma310Approximation
import Bong.Bong.Beli2006AlphaP2P3Proof
import Bong.Bong.GoodBONGDeepIntegralExtensionProof
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Bong.Beli2019UnitDefectSpectrumProof
import Bong.Bong.DiagonalCodimensionOneCancellationProof
import Bong.Bong.Beli2009BinaryNormContainmentProof
import Bong.Bong.Beli2019BinaryFirstScalingProof
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof
import Bong.Bong.DiagonalRepresentationParityProof
import Bong.Bong.Beli2019QuaternaryFirstScalingProof
import Bong.Bong.HilbertDefectChoiceProof
import Bong.Bong.MaximalDefectClassProof
import Bong.Bong.ResidueDefectProductProof
import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.UnramifiedNormProof
import Bong.Dyadic.UnramifiedNormDirectProof
import Bong.Bong.AlternatingEndpointTowerRepresentationProof
import Bong.Bong.BeliLemma49Proof
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.BeliCorollary44LawsProof
import Bong.Bong.StructuralProof
import Bong.Bong.BeliLemma43MaximalNormProof
import Bong.Bong.BeliLemma47Proof
import Bong.Lattice.ScaledHyperbolicMaximalProof
import Bong.Bong.Beli2009WeightIdealProof

/-!
# Beli (2019), Theorem 2.1

Necessity is the Sections 4--6 and rank-completion argument.  Sufficiency is
the concrete Sections 7--9 equal-rank induction followed, in strict unequal
rank, by Lemmas 2.20--2.21.  Lemma 2.16 converts between the displayed
condition (iii) and the revised arXiv-v2 condition (iii').

The theorem below does not assume `GoodBONGRepresentationLaws` or any
theorem-level final-step interface.
-/

namespace Bong

open Dyadic BONG

universe u v w

section Laws

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]

noncomputable local instance disc : DyadicDiscriminantClassLaws K :=
  Dyadic.dyadicDiscriminantClassLawsProved

noncomputable local instance hilbert : HilbertSymbolLaws K :=
  Dyadic.hilbertSymbolLawsProved

noncomputable local instance hilbertChoice :
    DyadicHilbertDefectChoiceLaws K :=
  BONG.dyadicHilbertDefectChoiceLawsProved

noncomputable local instance unramified : DyadicUnramifiedNormLaws K :=
  Dyadic.dyadicUnramifiedNormLawsProvedDirect

noncomputable local instance diagonal : DyadicDiagonalClassificationLaws K :=
  dyadicDiagonalClassificationLawsProved

noncomputable local instance structuralModel :
    BONGStructuralLaws.{u, u} K := bongStructuralLawsProved K

noncomputable local instance structuralV :
    BONGStructuralLaws.{u, v} K := bongStructuralLawsProved K

noncomputable local instance structuralW :
    BONGStructuralLaws.{u, w} K := bongStructuralLawsProved K

local instance mainDefect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

local instance mainStructuralModelGoodExistence :
    BONGGoodExistenceLaws.{u, u} K :=
  BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralModel)

noncomputable local instance constructionModel :
    BeliLemma43ConstructionLaws.{u, u} K :=
  beliLemma43ConstructionLawsProved K

noncomputable local instance constructionV :
    BeliLemma43ConstructionLaws.{u, v} K :=
  beliLemma43ConstructionLawsProved K

noncomputable local instance constructionW :
    BeliLemma43ConstructionLaws.{u, w} K :=
  beliLemma43ConstructionLawsProved K

noncomputable local instance lemma47V : BeliLemma47Laws.{u, v} K :=
  beliLemma47LawsProved K

noncomputable local instance lemma47W : BeliLemma47Laws.{u, w} K :=
  beliLemma47LawsProved K

set_option maxHeartbeats 24000000 in
-- The concrete Section 7--9 induction is large, but no proof search is hidden.
/-- Beli (2019), Theorem 2.1, with the four originally displayed
conditions. -/
theorem beli2019Theorem21
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank := by
  letI : BinaryNormGeneratorLocalLaws.{u, v} K :=
    binaryNormGeneratorLocalLawsProved
  letI : BONGReverseDualLaws.{u, v} K :=
    BONGStructuralLaws.toBONGReverseDualLaws (self := structuralV)
  let lemma49V : BeliLemma49Laws.{u, v} K :=
    @BONG.beliLemma49LawsOfReverseDual.{u, v} K _ _ _ _ _ lemma47V
      (BONGStructuralLaws.toBONGReverseDualLaws (self := structuralV))
  let lemma49W : BeliLemma49Laws.{u, w} K :=
    @BONG.beliLemma49LawsOfReverseDual.{u, w} K _ _ _ _ _ lemma47W
      (BONGStructuralLaws.toBONGReverseDualLaws (self := structuralW))
  let alphaModel : Beli2006AlphaLaws.{u, u} K :=
    @beli2006AlphaLaws_proved.{u, u} K _ _ _ _ _ _ _ _
  let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
    @beli2006AlphaLaws_proved.{u, v} K _ _ _ _ _ _ _ _
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    @beli2006AlphaLaws_proved.{u, w} K _ _ _ _ _ _ _ _
  let classificationBase : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  let classificationModel : GoodBONGClassificationLaws.{u, v, u} K :=
    goodBONGClassificationLawsProved K
  let classificationV : GoodBONGClassificationLaws.{u, v, v} K :=
    goodBONGClassificationLawsProved K
  let classificationW : GoodBONGClassificationLaws.{u, w, w} K :=
    goodBONGClassificationLawsProved K
  let sectionFiveVConcrete : Beli2019SectionFiveLaws.{u, v} K := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    letI : BONGStructuralLaws.{u, v} K := structuralV
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact inferInstance
  let sectionFiveWConcrete : Beli2019SectionFiveLaws.{u, w} K := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    letI : BONGStructuralLaws.{u, w} K := structuralW
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    exact @beli2019SectionFiveLawsProved.{u, w} K
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance disc unramified hilbert inferInstance inferInstance
      targetLaws inferInstance structuralW lemma47W inferInstance classificationW
  let lemma310VVConcrete :
      Beli2019Lemma310RepresentationLaws.{u, v, v} K := by
    let prefixLaws : Beli2019Lemma310PrefixLaws.{u, v, v} K :=
      @lemma310PrefixLawsOfApproximationLaws.{u, v, v} K
        inferInstance inferInstance inferInstance inferInstance inferInstance
        classificationV classificationV hilbert inferInstance sourceLaws sourceLaws
        inferInstance
    exact @lemma310RepresentationLawsOfPrefixLaws.{u, v, v} K
      inferInstance inferInstance inferInstance inferInstance inferInstance
      classificationV classificationV prefixLaws
  let lemma310VWConcrete :
      Beli2019Lemma310RepresentationLaws.{u, v, w} K := by
    let prefixLaws : Beli2019Lemma310PrefixLaws.{u, v, w} K :=
      @lemma310PrefixLawsOfApproximationLaws.{u, v, w} K
        inferInstance inferInstance inferInstance inferInstance inferInstance
        classificationV classificationW hilbert inferInstance sourceLaws targetLaws
        inferInstance
    exact @lemma310RepresentationLawsOfPrefixLaws.{u, v, w} K
      inferInstance inferInstance inferInstance inferInstance inferInstance
      classificationV classificationW prefixLaws
  let deepVVConcrete : GoodBONGDeepIntegralExtensionLaws.{u, v, v} K := by
    letI : BONGGoodExistenceLaws.{u, v} K :=
      BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralV)
    exact goodBONGDeepIntegralExtensionLaws K
  let deepVWConcrete : GoodBONGDeepIntegralExtensionLaws.{u, v, w} K := by
    letI : BONGGoodExistenceLaws.{u, v} K :=
      BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralV)
    exact goodBONGDeepIntegralExtensionLaws K
  let deepWWConcrete : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K := by
    letI : BONGGoodExistenceLaws.{u, w} K :=
      BONGStructuralLaws.toBONGGoodExistenceLaws (self := structuralW)
    exact goodBONGDeepIntegralExtensionLaws K
  let quaternaryVConcrete :
      DyadicQuaternaryFirstScalingLaws.{u, v} K := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact BONG.GoodBONG.dyadicQuaternaryFirstScalingLawsProved
  let quaternaryWConcrete :
      DyadicQuaternaryFirstScalingLaws.{u, w} K := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    exact BONG.GoodBONG.dyadicQuaternaryFirstScalingLawsProved
  constructor
  · letI : BONGStructuralLaws.{u, v} K := structuralV
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : Beli2019SectionFiveLaws.{u, v} K := sectionFiveVConcrete
    letI : Beli2019SectionFourLaws.{u, v} K :=
      @beli2019SectionFourLaws.{u, v} K
        inferInstance inferInstance inferInstance inferInstance inferInstance
        sourceLaws structuralV hilbert inferInstance mainDefect inferInstance inferInstance
    letI : GoodBONGDeepIntegralExtensionLaws.{u, v, w} K := deepVWConcrete
    exact beli2019_necessity
      (sourceLaws := sourceLaws) (targetLaws := targetLaws) a b hRank
  · let prefixV : Beli2006PrefixChangeLaws.{u, v} K := by
      letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
      exact prefixChangeLawsOfClassification
    let prefixW : Beli2006PrefixChangeLaws.{u, w} K := by
      letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
      exact prefixChangeLawsOfClassification
    let sectionFourVConcrete : Beli2019SectionFourLaws.{u, v} K :=
      @beli2019SectionFourLaws.{u, v} K
        inferInstance inferInstance inferInstance inferInstance inferInstance
        sourceLaws structuralV hilbert inferInstance mainDefect inferInstance inferInstance
    let sectionFourWConcrete : Beli2019SectionFourLaws.{u, w} K :=
      @beli2019SectionFourLaws.{u, w} K
        inferInstance inferInstance inferInstance inferInstance inferInstance
        targetLaws structuralW hilbert inferInstance mainDefect inferInstance inferInstance
    exact beli2019_sufficiency_complete
      (disc := disc)
      (unramified := unramified)
      (hilbertChoice := hilbertChoice) (hilbert := hilbert)
      (diagonal := diagonal) (structuralModel := structuralModel)
      (structuralV := structuralV) (structuralW := structuralW)
      (alphaModel := alphaModel)
      (constructionModel := constructionModel)
      (classificationBase := classificationBase)
      (classificationModel := classificationModel)
      (alphaV := sourceLaws) (alphaW := targetLaws)
      (constructionV := constructionV) (constructionW := constructionW)
      (lemma49V := lemma49V)
      (lemma49W := lemma49W) (lemma47V := lemma47V)
      (lemma47W := lemma47W)
      (classificationV := classificationV) (classificationW := classificationW)
      (lemma310VV := lemma310VVConcrete) (lemma310VW := lemma310VWConcrete)
      (sectionFiveV := sectionFiveVConcrete)
      (sectionFiveW := sectionFiveWConcrete)
      (sectionFourV := sectionFourVConcrete)
      (sectionFourW := sectionFourWConcrete)
      (quaternaryScalingV := quaternaryVConcrete)
      (quaternaryScalingW := quaternaryWConcrete)
      (prefixChangeV := prefixV) (prefixChangeW := prefixW)
      (deepVV := deepVVConcrete) (deepVW := deepVWConcrete)
      (deepWW := deepWWConcrete)
      a b hRank ambient

set_option maxHeartbeats 24000000 in
-- This corollary additionally invokes Lemma 2.16 in both directions.
/-- Beli (2019), Theorem 2.1 in the revised arXiv-v2 formulation, with
condition (iii') in place of (iii). -/
theorem beli2019Theorem21_prime
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔
      RepresentationConditionsPrime a b hRank := by
  let alphaModel : Beli2006AlphaLaws.{u, u} K :=
    @beli2006AlphaLaws_proved.{u, u} K _ _ _ _ _ _ _ _
  let sourceLaws : Beli2006AlphaLaws.{u, v} K :=
    @beli2006AlphaLaws_proved.{u, v} K _ _ _ _ _ _ _ _
  let targetLaws : Beli2006AlphaLaws.{u, w} K :=
    @beli2006AlphaLaws_proved.{u, w} K _ _ _ _ _ _ _ _
  have hmain :
      Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
    beli2019Theorem21 hRank ambient a b
  constructor
  · intro representation
    exact RepresentationConditions.toPrime
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      (hmain.mp representation)
  · intro conditionsPrime
    have htrigger := a.beli2019Lemma216
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b hRank conditionsPrime.orderCondition conditionsPrime.defectCondition
    exact hmain.mpr
      ((representationConditions_iff_prime a b hRank htrigger).mpr conditionsPrime)

end Laws

end Bong
