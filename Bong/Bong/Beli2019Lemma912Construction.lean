/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912Lemma910

/-!
# Beli (2019), Lemma 9.12: type-I construction

This file combines the exact parameter split, Lemma 9.9 conditions, and
Lemma 9.10 construction.  The only remaining branch is the paper's separate
type-III case.
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

/-- The residual profile produces either the exact type-III parameters or
literal Lemma 9.10 output data for one of the four type-I branches. -/
theorem beli2019Lemma912_typeIIIParameters_or_exists_lemma910Data
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
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (R₁ R₂ A₁ : Int)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha :
      reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) =
        ![R₁, R₂, R₁] i)
    (hsourceFirstAlpha :
      a.alphaValue (0 : Fin (N + 4)) = (A₁ : ℚ))
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i =
        a.valueUnit (⟨i.1, by omega⟩ : Fin (N + 5)))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic) :
    let hlength : N + 5 = 3 + (N + 2) := by omega
    Beli2019Lemma912TypeIIIParameters a c ∨
      ∃ β₁ : Int,
        Beli2019Lemma912TypeIBetaData a c A₁ β₁ ∧
          ∃ D : Beli2019Lemma99Realization
              (q := s) R₁ (R₂ + 2) R₁ β₁,
            Nonempty (Beli2019Lemma910Data (a.castLength hlength) D) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  have C := Beli2019Lemma99Conditions.ofReferenceInvariants
    reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  rcases beli2019Lemma912_typeIIIParameters_or_exists_typeIBetaConditions
      (alphaV := alphaV) (parityV := parityV)
      (alphaW := alphaW) (parityW := parityW)
      reference a c profile R₁ R₂ A₁ C hfirst hR₁ hR₂
        hsourceFirstAlpha hrefIsotropy with htypeIII | htypeI
  · exact Or.inl htypeIII
  · rcases htypeI with ⟨β₁, data, conditions⟩
    right
    refine ⟨β₁, data, ?_⟩
    exact beli2019Lemma912_exists_lemma910Data_of_typeIBetaData
      (disc := disc)
      (constructionV := constructionV)
      (sectionTwoV := sectionTwoV)
      (structuralV := structuralV)
      (structuralModel := structuralModel)
      (alphaV := alphaV)
      (alphaModel := alphaModel)
      (classificationModel := classificationModel)
      reference a c data hrefOrders hrefFirstAlpha hsourceOrders hprefix
        conditions

end BONG.GoodBONG

end Bong
