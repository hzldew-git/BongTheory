/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIAssembly
import Bong.Bong.Beli2019Lemma912TypeIIIAssembly

/-!
# Beli (2019), Lemma 9.12

The parameter analysis first separates the four type-I cases from the
remaining type-III case.  The two construction theorems are combined here,
so every input satisfying the hypotheses of Lemma 9.12 admits a literal
index-`p` target sublattice satisfying all four representation conditions.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {r : QuadraticSpace K W}
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W} {N : Nat}

set_option maxHeartbeats 12000000 in
-- The proof elaborates both construction branches and their law packages.
/-- Complete fixed-rank form of Beli (2019), Lemma 9.12. -/
theorem exists_beli2019Lemma912_indexPReduction
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
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
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i)
    (hsourceFirstAlpha : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i =
        a.valueUnit (⟨i.1, by omega⟩ : Fin (N + 5)))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic)
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4))) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient hsource)) := by
  rcases beli2019Lemma912_typeIIIParameters_or_typeIReduction
      (disc := disc) (constructionV := constructionV)
      (sectionTwoV := sectionTwoV) (structuralV := structuralV)
      (structuralModel := structuralModel) (alphaV := alphaV)
      (alphaW := alphaW) (alphaModel := alphaModel)
      (parityV := parityV) (parityW := parityW)
      (classificationModel := classificationModel)
      (representationLaws := representationLaws)
      reference a c profile R₁ R₂ A₁ hrefOrders hrefFirstAlpha
        hsourceOrders hsourceFirstAlpha hprefix hfirst
          hrefIsotropy ambient hsource with hparams | reduction
  · exact exists_beli2019Lemma912_typeIIIIndexPReduction
      (sourceAlpha := alphaV) (comparisonAlpha := alphaW)
      (sourceParity := parityV) (comparisonParity := parityW)
      (classificationV := classificationV)
      (classificationW := classificationW)
      (structural := structuralV) (representationLaws := representationLaws)
      a c profile hparams hfirst ambient hsource
  · exact reduction

/-- Lemma 9.12 in the counterexample-descent form consumed by Section 9. -/
theorem beli2019Lemma912_counterexampleDescent
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
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
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i)
    (hsourceFirstAlpha : a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i =
        a.valueUnit (⟨i.1, by omega⟩ : Fin (N + 5)))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic)
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (hp : (Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient hsource).Counterexample) :
    ∃ next, next.Counterexample ∧
      Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl (N + 4)) ambient hsource) := by
  rcases exists_beli2019Lemma912_indexPReduction
      (disc := disc) (constructionV := constructionV)
      (sectionTwoV := sectionTwoV) (structuralV := structuralV)
      (structuralModel := structuralModel) (alphaV := alphaV)
      (alphaW := alphaW) (alphaModel := alphaModel)
      (parityV := parityV) (parityW := parityW)
      (classificationModel := classificationModel)
      (classificationV := classificationV)
      (classificationW := classificationW)
      (representationLaws := representationLaws)
      reference a c profile R₁ R₂ A₁ hrefOrders hrefFirstAlpha
        hsourceOrders hsourceFirstAlpha hprefix hfirst
          hrefIsotropy ambient hsource with ⟨D⟩
  exact D.counterexampleDescent _ hp

end BONG.GoodBONG

end Bong
