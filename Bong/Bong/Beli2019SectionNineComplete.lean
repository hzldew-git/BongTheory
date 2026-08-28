/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019SectionNineRankThree
import Bong.Bong.Beli2019SectionNineRankFour
import Bong.Bong.Beli2019SectionNineReduction

/-!
# Beli (2019), Section 9 in every rank at least three

This module dispatches the two literal low-rank endpoints and the uniform
rank-at-least-five theorem.  It is the Section 9 input used by the final
equal-rank well-founded induction.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

section Laws

variable
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [constructionW : BeliLemma43ConstructionLaws.{u, w} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionTwoW : Beli2006SectionTwoLaws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [scaledModel : ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    [localizationV : Beli2009AlphaLocalizationLaws.{u, v} K]
    [localizationW : Beli2009AlphaLocalizationLaws.{u, w} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [binaryScalingV : DyadicBinaryFirstScalingLaws.{u, v} K]
    [binaryScalingW : DyadicBinaryFirstScalingLaws.{u, w} K]
    [quaternaryScalingV : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [quaternaryScalingW : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [lemma49V : BeliLemma49Laws.{u, v} K]
    [lemma49W : BeliLemma49Laws.{u, w} K]
    [lemma47V : BeliLemma47Laws.{u, v} K]
    [lemma47W : BeliLemma47Laws.{u, w} K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [sectionFiveV : Beli2019SectionFiveLaws.{u, v} K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]

set_option maxHeartbeats 18000000 in
-- Reindexing isolates ranks three and four before invoking the uniform theorem.
/-- Bundled Section 9 descent in every common rank at least three. -/
theorem beli2019SectionNine_counterexampleDescent_complete_of_problem
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hrank : 2 ≤ p.sourceIndex) (hp : p.Counterexample)
    (hequal : p.EqualNorm) :
    ∃ next, next.Counterexample ∧
      next.sourceIndex = next.targetIndex ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure
        next p := by
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  by_cases htwo : p.sourceIndex = 2
  · have htarget : p.targetIndex = 2 := by omega
    let a := p.targetBONG.castLength
      (show p.targetIndex + 1 = 3 by omega)
    let c := p.sourceBONG.castLength
      (show p.sourceIndex + 1 = 3 by omega)
    let conditions' :=
      Beli2019RepresentationProblem.representationConditions_castIndices
        p.targetBONG p.sourceBONG p.rankBound p.conditions htarget htwo
    let p' := Beli2019RepresentationProblem.ofData a c
      (Nat.le_refl 2) p.ambient conditions'
    have hproblem : p' = p := by
      dsimp only [p', a, c, conditions']
      exact (Beli2019RepresentationProblem.ofData_castIndices_eq
        p.targetBONG p.sourceBONG p.rankBound p.ambient p.conditions
          htarget htwo).trans
        (Beli2019RepresentationProblem.ofData_self p)
    have hp' : p'.Counterexample := by rwa [hproblem]
    have hequal' : p'.EqualNorm := by rwa [hproblem]
    have H := beli2019SectionNine_counterexampleDescent_rankThree
      (K := K) (V := p.Target) (W := p.Source)
      (q := p.targetQ) (r := p.sourceQ)
      (L := p.targetLattice) (M := p.sourceLattice)
      (disc := disc)
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
      a c p.ambient conditions' hp' hequal'
    simpa only [p', hproblem] using H
  · by_cases hthree : p.sourceIndex = 3
    · have htarget : p.targetIndex = 3 := by omega
      let a := p.targetBONG.castLength
        (show p.targetIndex + 1 = 4 by omega)
      let c := p.sourceBONG.castLength
        (show p.sourceIndex + 1 = 4 by omega)
      let conditions' :=
        Beli2019RepresentationProblem.representationConditions_castIndices
          p.targetBONG p.sourceBONG p.rankBound p.conditions htarget hthree
      let p' := Beli2019RepresentationProblem.ofData a c
        (Nat.le_refl 3) p.ambient conditions'
      have hproblem : p' = p := by
        dsimp only [p', a, c, conditions']
        exact (Beli2019RepresentationProblem.ofData_castIndices_eq
          p.targetBONG p.sourceBONG p.rankBound p.ambient p.conditions
            htarget hthree).trans
          (Beli2019RepresentationProblem.ofData_self p)
      have hp' : p'.Counterexample := by rwa [hproblem]
      have hequal' : p'.EqualNorm := by rwa [hproblem]
      have H := beli2019SectionNine_counterexampleDescent_rankFour
        (K := K) (V := p.Target) (W := p.Source)
        (q := p.targetQ) (r := p.sourceQ)
        (L := p.targetLattice) (M := p.sourceLattice)
        (disc := disc)
        (constructionV := constructionV) (constructionW := constructionW)
        (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
        (structuralV := structuralV) (structuralW := structuralW)
        (structuralModel := structuralModel)
        (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
        (parityV := parityV) (parityW := parityW)
        (localizationV := localizationV) (localizationW := localizationW)
        (classificationModel := classificationModel)
        (classificationV := classificationV)
        (classificationW := classificationW)
        (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
        (quaternaryScalingV := quaternaryScalingV)
        (quaternaryScalingW := quaternaryScalingW)
        (lemma49V := lemma49V) (lemma49W := lemma49W)
        (lemma47V := lemma47V) (lemma47W := lemma47W)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
        (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
        (deepWW := deepWW)
        a c p.ambient conditions' hp' hequal'
      simpa only [p', hproblem] using H
    · have hhigh : 4 ≤ p.sourceIndex := by omega
      exact beli2019SectionNine_counterexampleDescent_of_problem
        (disc := disc)
        (constructionV := constructionV) (constructionW := constructionW)
        (sectionTwoV := sectionTwoV) (sectionTwoW := sectionTwoW)
        (structuralV := structuralV) (structuralW := structuralW)
        (structuralModel := structuralModel)
        (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
        (parityV := parityV) (parityW := parityW)
        (localizationV := localizationV) (localizationW := localizationW)
        (classificationModel := classificationModel)
        (classificationV := classificationV)
        (classificationW := classificationW)
        (binaryScalingV := binaryScalingV) (binaryScalingW := binaryScalingW)
        (quaternaryScalingV := quaternaryScalingV)
        (quaternaryScalingW := quaternaryScalingW)
        (lemma49V := lemma49V) (lemma49W := lemma49W)
        (lemma47V := lemma47V) (lemma47W := lemma47W)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveV := sectionFiveV) (sectionFiveW := sectionFiveW)
        (sectionFourV := sectionFourV) (sectionFourW := sectionFourW)
        (deepWW := deepWW)
        p hindex hhigh hp hequal

end Laws

end BONG.GoodBONG

end Bong
