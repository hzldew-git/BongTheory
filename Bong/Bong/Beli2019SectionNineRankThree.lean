/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma93RankThree
import Bong.Bong.Beli2019Lemma912RankThreeAssembly
import Bong.Bong.Beli2019Lemma912LowBranches
import Bong.Bong.Beli2019RepresentationProblemReindex

/-!
# Beli (2019), Section 9 in rank three

The ordinary Lemma 9.1 branch is discharged by the ternary form of Lemma
9.3.  Its negation gives the initial profile of Lemma 9.12 with `T = 0`;
the ternary branch assembly then produces either a head reduction or an
index-uniformizer reduction.  Thus every equal-norm ternary counterexample
has a strictly smaller successor.
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

set_option maxHeartbeats 24000000 in
-- The proof elaborates the complete Lemmas 9.3, 9.6, 9.10, and 9.12
-- constructions together at the ternary endpoint.
/-- Every equal-norm ternary counterexample has a strictly smaller concrete
counterexample. -/
theorem beli2019SectionNine_counterexampleDescent_rankThree
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl 2))
    (hp : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl 2) ambient conditions).Counterexample)
    (hequal : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl 2) ambient conditions).EqualNorm) :
    ∃ next, next.Counterexample ∧
      next.sourceIndex = next.targetIndex ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 2) ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData
    a c (Nat.le_refl 2) ambient conditions
  have hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3) := by
    exact (Beli2019RepresentationProblem.equalNorm_iff_firstOrder_eq p).mp
      hequal
  by_cases hlemma91 : a.Lemma91Alternative c
  · rcases a.exists_beli2019Lemma93Input_rankThree
        (targetLaws := alphaV) (sourceLaws := alphaW)
        (targetParity := parityV) (sourceParity := parityW)
        (targetLocalization := localizationV)
        (sourceLocalization := localizationW)
        (targetConstruction := constructionV)
        (sourceConstruction := constructionW)
        (targetSectionTwo := sectionTwoV) (sourceSectionTwo := sectionTwoW)
        (classificationV := classificationV)
        (classificationW := classificationW)
        (targetBinaryScaling := binaryScalingV)
        (sourceBinaryScaling := binaryScalingW)
        (targetQuaternaryScaling := quaternaryScalingV)
        (sourceQuaternaryScaling := quaternaryScalingW)
        (targetLemma49 := lemma49V) (sourceLemma49 := lemma49W)
        (targetLemma47 := lemma47V) (sourceLemma47 := lemma47W)
        (structuralV := structuralV) (structuralW := structuralW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        (sectionFiveW := sectionFiveW)
        (sectionFourW := sectionFourW) (sectionFourV := sectionFourV)
        (deepWW := deepWW)
        c hfirst ambient conditions hlemma91 with ⟨input⟩
    let reduction := input.headReduction
      (targetLaws := alphaW) (sourceLaws := alphaV)
    exact ⟨reduction.next,
      Beli2019RepresentationProblem.HeadReduction.nextCounterexample
        p reduction hp,
      rfl,
      Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
  · have profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c :=
      by
        letI : Beli2006AlphaLaws.{u, v} K := alphaV
        exact a.beli2019Lemma912_initialProfile_allRanks
          c hfirst conditions hlemma91
            (by intro hT; omega) (by intro hT; omega)
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    letI : Beli2009AlphaLocalizationLaws.{u, v} K := localizationV
    letI : BeliLemma43ConstructionLaws.{u, v} K := constructionV
    letI : Beli2006SectionTwoLaws.{u, v} K := sectionTwoV
    letI : BONGStructuralLaws.{u, v} K := structuralV
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    letI : DyadicBinaryFirstScalingLaws.{u, v} K := binaryScalingV
    letI : DyadicQuaternaryFirstScalingLaws.{u, v} K := quaternaryScalingV
    letI : BeliLemma49Laws.{u, v} K := lemma49V
    letI : BeliLemma47Laws.{u, v} K := lemma47V
    letI : Beli2019SectionFiveLaws.{u, v} K := sectionFiveV
    letI : Beli2019SectionFourLaws.{u, v} K := sectionFourV
    letI : Beli2019InclusionConditionsLaws.{u, v} K := inferInstance
    rcases a.beli2019Lemma912_rankThree_typeIII_or_headReduction_or_reduction
        (disc := disc)
        (constructionV := constructionV) (sectionTwoV := sectionTwoV)
        (structuralV := structuralV) (structuralModel := structuralModel)
        (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
        (parityV := parityV) (parityW := parityW)
        (classificationModel := classificationModel)
        c profile hfirst ambient conditions with
      htypeIII | hhead | hindex
    · rcases exists_beli2019Lemma912_typeIIIIndexPReduction_of_profile_allRanks
          (sourceAlpha := alphaV) (comparisonAlpha := alphaW)
          (sourceParity := parityV) (comparisonParity := parityW)
          (classificationV := classificationV)
          (classificationW := classificationW)
          (structural := structuralV)
          a c profile htypeIII hfirst ambient conditions with ⟨reduction⟩
      exact ⟨reduction.next, reduction.nextCounterexample p hp,
        rfl, reduction.smaller⟩
    · rcases hhead with ⟨reduction⟩
      exact ⟨reduction.next,
        Beli2019RepresentationProblem.HeadReduction.nextCounterexample
          p reduction hp,
        rfl,
        Beli2019RepresentationProblem.HeadReduction.smaller p reduction⟩
    · rcases hindex with ⟨reduction⟩
      exact ⟨reduction.next, reduction.nextCounterexample p hp,
        rfl, reduction.smaller⟩

end Laws

end BONG.GoodBONG

end Bong
