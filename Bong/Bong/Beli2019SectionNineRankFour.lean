/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912SectionNineRankFour
import Bong.Bong.Beli2019RepresentationProblemReindex

/-!
# Beli (2019), Section 9 in rank four

The ordinary and exceptional branches use the literal head reductions of
Lemmas 9.3 and 9.6.  The residual branch uses the complete quaternary form of
Lemma 9.12.  Hence every equal-norm rank-four counterexample has a strictly
smaller equal-rank successor.
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
  {L : Lattice K V} {M : Lattice K W}

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
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
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

set_option maxHeartbeats 14000000 in
-- The three concrete Section 9 branches are assembled at the rank-four boundary.
/-- Every equal-norm rank-four counterexample has a strictly smaller concrete
equal-rank counterexample. -/
theorem beli2019SectionNine_counterexampleDescent_rankFour
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl 3))
    (hp : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl 3) ambient conditions).Counterexample)
    (hequal : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl 3) ambient conditions).EqualNorm) :
    ∃ next, next.Counterexample ∧
      next.sourceIndex = next.targetIndex ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 3) ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData
    a c (Nat.le_refl 3) ambient conditions
  have hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4) := by
    exact (Beli2019RepresentationProblem.equalNorm_iff_firstOrder_eq p).mp
      hequal
  cases beli2019SectionNine_cases p with
  | lemma93 ordinary =>
      rcases ordinary with ⟨input⟩
      let reduction := input.headReduction
        (targetLaws := alphaW) (sourceLaws := alphaV)
      exact ⟨reduction.next,
        Beli2019RepresentationProblem.HeadReduction.nextCounterexample
          p reduction hp,
        rfl,
        Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
  | lemma96 exceptional =>
      rcases exceptional with ⟨input⟩
      let reduction := input.headReduction
        (targetLaws := alphaV) (sourceLaws := alphaW)
      exact ⟨reduction.next,
        Beli2019RepresentationProblem.HeadReduction.nextCounterexample
          p reduction hp,
        rfl,
        Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
  | lemma912 residual =>
      rcases a.exists_beli2019Lemma912_indexPReduction_of_sectionNineResidual_rankFour
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
          c hfirst ambient conditions residual with ⟨reduction⟩
      exact ⟨reduction.next,
        reduction.nextCounterexample p hp,
        rfl,
        reduction.smaller⟩

end Laws

end BONG.GoodBONG

end Bong
