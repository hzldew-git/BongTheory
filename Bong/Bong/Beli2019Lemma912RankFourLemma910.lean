/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankFourScalar

/-!
# Beli (2019), Lemma 9.12: invoking Lemma 9.10 at rank four

This file only constructs the modified good BONG.  The later conversion to
representation conditions is deliberately kept in a separate module.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {L : Lattice K V} {P : Lattice K X}

set_option maxHeartbeats 5000000 in
-- The ternary realization is glued to the single unchanged fourth coefficient.
/-- Feed quaternary type-I beta data into Lemma 9.10. -/
theorem exists_beli2019Lemma910Data_rankFour
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
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    {R₁ R₂ A₁ β₁ : Int}
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L 4)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd 1 i))
    (shifted : Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
    (hfourth : R₂ + 2 ≤ a.order (3 : Fin 4))
    (hLower : A₁ ≤ β₁) (hUpper : β₁ ≤ A₁ + 2)
    (hThird : (β₁ : ℚ) ≤ a.alphaValue (2 : Fin 3)) :
    ∃ D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁,
      Nonempty (Beli2019Lemma910Data (N := 1) a D) := by
  let hlength : 3 + 1 = 1 + 3 := by omega
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hfourth' : ∀ hN : 0 < 1,
      R₂ + 2 ≤ a.order (Fin.natAdd 3 (⟨0, hN⟩ : Fin 1)) := by
    intro hN
    have hindex : Fin.natAdd 3 (⟨0, hN⟩ : Fin 1) = (3 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hfourth
  have hthird' : ∀ hN : 0 < 1,
      (β₁ : ℚ) ≤ (a.castLength hlength).alphaValue (2 : Fin 3) := by
    intro _
    simpa only [haCast] using hThird
  exact beli2019Lemma910 (N := 1)
    (disc := disc)
    (constructionAmbient := constructionV)
    (sectionTwoAmbient := sectionTwoV)
    (constructionPrefix := constructionV)
    (sectionTwoPrefix := sectionTwoV)
    (structuralAmbient := structuralV)
    (structuralPrefix := structuralV)
    (structuralModel := structuralModel)
    (alphaAmbient := alphaV)
    (alphaPrefix := alphaV)
    (alphaModel := alphaModel)
    (classificationModel := classificationModel)
    reference a hrefOrders hrefFirstAlpha horders hprefix shifted
      hfourth' hLower hUpper hthird'

end BONG.GoodBONG

end Bong
