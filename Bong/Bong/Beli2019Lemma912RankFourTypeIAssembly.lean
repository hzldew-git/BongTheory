/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankFourLemma910
import Bong.Bong.Beli2019Lemma912RankFourTypeIReduction

/-!
# Beli (2019), Lemma 9.12: quaternary type-I realization

This module isolates the expensive common construction shared by the four
quaternary type-I branches.  A shifted Lemma 9.9 package and proved scalar
conditions are converted into a literal index-`p` reduction.
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
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W}

set_option maxHeartbeats 5000000 in
-- Lemma 9.10, inclusion conditions, and the scalar characterization are composed here.
/-- A complete quaternary type-I scalar package yields the literal reduction. -/
theorem exists_indexPReduction_of_rankFourTypeIScalar
    [QuadraticDefectLaws K]
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
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (data : Beli2019Lemma912TypeIBetaDataRankFour a c A₁ β₁)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd 1 i))
    (shifted : Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl 3))
    (scalar : ∀
      (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁)
      (E : Beli2019Lemma910Data (N := 1) a D),
        (a.castLength (show 3 + 1 = 1 + 3 from rfl)).RepresentationDefectCondition
            (E.bong.castLength (show 3 + 1 = 1 + 3 from rfl)) →
        (E.bong.castLength
          (show 3 + 1 = 1 + 3 from rfl)).RepresentationOrderCondition c le_rfl →
        E.TypeIScalarConditions a c D (show 3 + 1 = 1 + 3 from rfl)) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl 3) ambient hsource)) := by
  have hR₂ : a.order (1 : Fin 4) = R₂ := by
    simpa using horders (1 : Fin 3)
  have hfourth : R₂ + 2 ≤ a.order (3 : Fin 4) := by
    simpa only [hR₂] using data.fourthOrder
  rcases exists_beli2019Lemma910Data_rankFour
      (disc := disc)
      (constructionV := constructionV)
      (sectionTwoV := sectionTwoV)
      (structuralV := structuralV)
      (structuralModel := structuralModel)
      (alphaV := alphaV)
      (alphaModel := alphaModel)
      (classificationModel := classificationModel)
      reference a hrefOrders hrefFirstAlpha horders hprefix shifted
        hfourth data.betaLower data.betaUpper data.betaThird with ⟨D, ⟨E⟩⟩
  have constructed := E.rankFourConstructedConditions
    a c data D horders hfirst hsource
  have hscalar := scalar D E constructed.defect constructed.order
  letI : BONGStructuralLaws.{u, v} K := structuralV
  exact ⟨E.indexPReduction_of_rankFourScalar
    (sourceLaws := alphaV) (targetLaws := alphaW)
    a c D horders hfirst ambient hsource constructed hscalar⟩

end BONG.GoodBONG

end Bong
