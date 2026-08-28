/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912BranchConditions
import Bong.Bong.Beli2019Lemma912TypeIReduction

/-!
# Beli (2019), Lemma 9.12: invoking Lemma 9.10

This file transports the rank convention of Lemma 9.12 to the input format
of Lemma 9.10 and constructs its literal index-uniformizer lattice data.
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

@[simp]
theorem castLength_castLength
    {m n : Nat} (a : GoodBONG q L m) (h : m = n) (h' : n = m) :
    (a.castLength h).castLength h' = a := by
  subst n
  rfl

/-- Feed the numerical data of a type-I branch into Lemma 9.10. -/
theorem beli2019Lemma912_exists_lemma910Data_of_typeIBetaData
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
    (reference : GoodBONG s P 3)
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    {R₁ R₂ A₁ β₁ : Int}
    (data : Beli2019Lemma912TypeIBetaData a c A₁ β₁)
    (hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i)
    (hrefFirstAlpha :
      reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) =
        ![R₁, R₂, R₁] i)
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i =
        a.valueUnit (⟨i.1, by omega⟩ : Fin (N + 5)))
    (conditions :
      Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁) :
    let hlength : N + 5 = 3 + (N + 2) := by omega
    ∃ D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁,
      Nonempty (Beli2019Lemma910Data (a.castLength hlength) D) := by
  let hlength : N + 5 = 3 + (N + 2) := by omega
  let ambient := a.castLength hlength
  have hambientOrders : ∀ i : Fin 3,
      ambient.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show ambient = a.castLength hlength by rfl, order_castLength]
    exact hsourceOrders i
  have hambientPrefix : ∀ i : Fin 3,
      reference.valueUnit i =
        ambient.valueUnit (Fin.castAdd (N + 2) i) := by
    intro i
    rw [show ambient = a.castLength hlength by rfl, valueUnit_castLength]
    exact hprefix i
  have hfourth : ∀ hN : 0 < N + 2,
      R₂ + 2 ≤ ambient.order
        (Fin.natAdd 3 (⟨0, hN⟩ : Fin (N + 2))) := by
    intro hN
    rw [show ambient = a.castLength hlength by rfl, order_castLength]
    have hindex :
        (⟨(Fin.natAdd 3 (⟨0, hN⟩ : Fin (N + 2))).1, by omega⟩ :
          Fin (N + 5)) = (3 : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
      simpa using hsourceOrders (1 : Fin 3)
    simpa only [hR₂] using data.orderBounds.fourthOrder
  have hthird : ∀ hN : 0 < N + 2,
      (β₁ : ℚ) ≤
        (ambient.castLength (show 3 + (N + 2) = (N + 2) + 3 by omega)).alphaValue
          (⟨2, by omega⟩ : Fin (N + 4)) := by
    intro _
    rw [show ambient = a.castLength hlength by rfl]
    rw [castLength_castLength]
    exact data.betaThird
  exact beli2019Lemma910
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
    reference ambient hrefOrders hrefFirstAlpha hambientOrders
      hambientPrefix conditions hfourth data.betaLower data.betaUpper hthird

end BONG.GoodBONG

end Bong
