/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93CaseTwoLowRank

/-!
# Beli (2019), Lemma 9.3 in rank at least four

The two ordinary cases in the proof of Lemma 9.3 are already constructive in
rank `N + 4`.  The later Section 9 assembly used a rank-five wrapper because
the additional exceptional branch mentions the fifth BONG value.  This file
records the literal lower-rank boundary: under the printed Lemma 9.1
alternative, Case 1 and Case 2 still exhaust all possibilities and produce
the recursive head-reduction input.
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

section Laws

variable
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [targetParity : Beli2009AlphaParityLaws.{u, v} K]
    [sourceParity : Beli2009AlphaParityLaws.{u, w} K]
    [targetLocalization : Beli2009AlphaLocalizationLaws.{u, v} K]
    [sourceLocalization : Beli2009AlphaLocalizationLaws.{u, w} K]
    [targetConstruction : BeliLemma43ConstructionLaws.{u, v} K]
    [sourceConstruction : BeliLemma43ConstructionLaws.{u, w} K]
    [targetSectionTwo : Beli2006SectionTwoLaws.{u, v} K]
    [sourceSectionTwo : Beli2006SectionTwoLaws.{u, w} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [targetBinaryScaling : DyadicBinaryFirstScalingLaws.{u, v} K]
    [sourceBinaryScaling : DyadicBinaryFirstScalingLaws.{u, w} K]
    [targetQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [sourceQuaternaryScaling : DyadicQuaternaryFirstScalingLaws.{u, w} K]
    [targetLemma49 : BeliLemma49Laws.{u, v} K]
    [sourceLemma49 : BeliLemma49Laws.{u, w} K]
    [targetLemma47 : BeliLemma47Laws.{u, v} K]
    [sourceLemma47 : BeliLemma47Laws.{u, w} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [structuralW : BONGStructuralLaws.{u, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    [DyadicTernaryRepresentationObstructionLaws K]
    [sectionFiveW : Beli2019SectionFiveLaws.{u, w} K]
    [sectionFourW : Beli2019SectionFourLaws.{u, w} K]
    [sectionFourV : Beli2019SectionFourLaws.{u, v} K]
    [deepWW : GoodBONGDeepIntegralExtensionLaws.{u, w, w} K]

set_option maxHeartbeats 2400000 in
-- The rank-four dispatcher elaborates both complete Section 9 branches.
/-- The ordinary Lemma 9.3 head reduction is valid in every rank `N + 4`.
The case distinction is exactly the one used in the paper. -/
theorem exists_beli2019Lemma93Input_rankFour
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hfirst : a.order (0 : Fin (N + 4)) =
      b.order (0 : Fin (N + 4)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hlemma91 : a.Lemma91Alternative b) :
    Nonempty (Beli2019RepresentationProblem.Lemma93Input
      (Beli2019RepresentationProblem.ofData a b (Nat.le_refl (N + 3))
        ambient conditions)) := by
  by_cases hcase : a.Beli2019Lemma93CaseOneCondition b
  · exact a.exists_beli2019Lemma93Input_caseOne
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      b hfirst ambient conditions hlemma91 hcase
  · have hcaseTwo : a.Beli2019Lemma93CaseTwoCondition b :=
      (a.beli2019Lemma93CaseTwoCondition_iff_not_caseOneCondition b).2 hcase
    exact exists_beli2019Lemma93Input_caseTwo
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      (targetParity := targetParity) (sourceParity := sourceParity)
      (targetLocalization := targetLocalization)
      (sourceLocalization := sourceLocalization)
      (targetConstruction := targetConstruction)
      (sourceConstruction := sourceConstruction)
      (targetSectionTwo := targetSectionTwo)
      (sourceSectionTwo := sourceSectionTwo)
      (classificationV := classificationV) (classificationW := classificationW)
      (targetBinaryScaling := targetBinaryScaling)
      (sourceBinaryScaling := sourceBinaryScaling)
      (targetQuaternaryScaling := targetQuaternaryScaling)
      (sourceQuaternaryScaling := sourceQuaternaryScaling)
      (targetLemma49 := targetLemma49) (sourceLemma49 := sourceLemma49)
      (targetLemma47 := targetLemma47) (sourceLemma47 := sourceLemma47)
      (structuralV := structuralV) (structuralW := structuralW)
      (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      a b hfirst ambient conditions hlemma91 hcaseTwo

end Laws

end BONG.GoodBONG

end Bong
