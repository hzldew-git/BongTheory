/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionNineCases
import Bong.Bong.Beli2019Lemma912SegmentAssembly
import Bong.Bong.Beli2019Lemma96V2Assembly
import Bong.Bong.Beli2019RepresentationProblemBONGChange

/-!
# Beli (2019), Lemma 9.12 from the literal Section 9 residual

Corollary 8.11 first changes the target good BONG so that its initial literal
binary alpha realizes the invariant first alpha.  Corollary 3.11 transports
the four conditions to this BONG.  The absence of actual Lemma 9.3 and Lemma
9.6 inputs then excludes their printed v2 hypotheses, because the realization
theorems for those lemmas would otherwise construct the forbidden inputs.

The resulting initial profile feeds the complete Lemma 9.12 construction.
Finally, the index-`p` certificate is repackaged for the original root BONG.
Thus the theorem below consumes precisely `Beli2019SectionNineResidual`; it
does not assume the numerical profile or a normalized binary segment.
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

set_option maxHeartbeats 20000000 in
-- The proof elaborates Corollary 8.11, both excluded head lemmas, and both
-- construction branches of Lemma 9.12 in one certificate-producing term.
/-- In common rank at least five, the literal residual branch of Section 9
produces the index-`p` reduction asserted by Lemma 9.12. -/
theorem exists_beli2019Lemma912_indexPReduction_of_sectionNineResidual
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (residual : Beli2019SectionNineResidual
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient conditions)) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient conditions)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
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
  rcases a.beli2019Corollary811 (0 : Fin (N + 4)) with ⟨C⟩
  have horders : a.SameOrders C.transformed := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.order_invariant C.transformed
  have hfirstC : C.transformed.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)) :=
    (horders (0 : Fin (N + 5))).symm.trans hfirst
  have conditionsC : RepresentationConditions C.transformed c
      (Nat.le_refl (N + 4)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      C.transformed c c (Nat.le_refl (N + 4))).mp conditions
  have hbinary : C.transformed.firstBinaryAlpha =
      (C.transformed.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) := by
    calc
      C.transformed.firstBinaryAlpha =
          C.transformed.adjacentBinaryAlpha (0 : Fin (N + 4)) :=
        (C.transformed.adjacentBinaryAlpha_zero).symm
      _ = (C.transformed.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) :=
        C.adjacentBinaryAlpha_eq
  have hnot93 : ¬C.transformed.Beli2019Lemma93V2Hypothesis c := by
    intro hlemma93
    rcases exists_beli2019Lemma93Input_v2Strengthened
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
        (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
        (sectionFourV := sectionFourV) (deepWW := deepWW)
        C.transformed c hfirstC ambient conditionsC hlemma93 with ⟨D⟩
    apply residual.1
    exact ⟨Beli2019RepresentationProblem.Lemma93Input.transport_ofData_targetBONG
        a C.transformed c (Nat.le_refl (N + 4)) ambient
          conditions conditionsC D⟩
  have hnot96 : ¬C.transformed.Beli2019Lemma96V2Hypothesis c := by
    intro hlemma96
    letI : BONGStructuralLaws.{u, u} K := structuralModel
    rcases C.transformed.exists_beli2019Lemma96Input_v2Hypothesis
        (laws := disc) (targetAlpha := alphaV) (sourceAlpha := alphaW)
        (modelAlpha := alphaModel)
        (modelClassification := classificationModel)
        (targetClassification := classificationV)
        (sourceClassification := classificationW)
        c ambient conditionsC hlemma96 with ⟨D⟩
    apply residual.2
    exact ⟨Beli2019RepresentationProblem.Lemma96Input.transport_ofData_targetBONG
        a C.transformed c (Nat.le_refl (N + 4)) ambient
          conditions conditionsC D⟩
  have profile : Beli2019Lemma912InitialProfile C.transformed c :=
    C.transformed.beli2019Lemma912_initialProfile
      c hfirstC conditionsC hnot93 hnot96
  rcases C.transformed.exists_beli2019Lemma912_indexPReduction_of_initialThree
      (disc := disc) (constructionV := constructionV)
      (sectionTwoV := sectionTwoV) (structuralV := structuralV)
      (structuralModel := structuralModel) (alphaV := alphaV)
      (alphaW := alphaW) (alphaModel := alphaModel)
      (parityV := parityV) (parityW := parityW)
      (classificationModel := classificationModel)
      (classificationV := classificationV)
      (classificationW := classificationW)
      c profile hbinary hfirstC ambient conditionsC with ⟨D⟩
  exact ⟨Beli2019RepresentationProblem.IndexPReduction.transport_ofData_targetBONG
      a C.transformed c (Nat.le_refl (N + 4)) ambient
        conditions conditionsC D⟩

set_option maxHeartbeats 22000000 in
-- This theorem reuses the full residual construction and then computes the
-- strict volume descent of its concrete index-`p` sublattice.
/-- Counterexample-descent form of Lemma 9.12 for the Section 9 induction. -/
theorem beli2019Lemma912_counterexampleDescent_of_sectionNineResidual
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (residual : Beli2019SectionNineResidual
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient conditions))
    (hp : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient conditions).Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl (N + 4)) ambient conditions) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
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
  rcases a.exists_beli2019Lemma912_indexPReduction_of_sectionNineResidual
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
      (sectionFiveW := sectionFiveW) (sectionFourW := sectionFourW)
      (sectionFourV := sectionFourV) (deepWW := deepWW)
      c hfirst ambient conditions residual with ⟨D⟩
  exact Beli2019RepresentationProblem.IndexPReduction.counterexampleDescent
    (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient conditions) D hp

end Laws

end BONG.GoodBONG

end Bong
