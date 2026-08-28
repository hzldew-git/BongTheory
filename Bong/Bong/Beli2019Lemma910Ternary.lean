/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma99Sufficiency

/-!
# Beli (2019), Lemma 9.10: the ternary core

This file formalizes the first half of Lemma 9.10.  Once Corollary 8.11 has
chosen a BONG for which the first global alpha is already the alpha of the
literal ternary prefix, Lemma 9.9 constructs the new ternary lattice and
Lemma 9.8 proves that it is represented by the old prefix.

The later full-rank assembly only has to append the unchanged coefficients
from index four onward and turn the resulting same-rank representation into
a literal index-`p` sublattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V}

/-- The output of the ternary part of Lemma 9.10.  Besides the realization
from Lemma 9.9, we retain the exact second-alpha formula used in the proof
and the integral representation supplied by Lemma 9.8. -/
structure Beli2019Lemma910TernaryData
    (reference : GoodBONG q M 3) (R₁ R₂ A₁ β₁ : Int) where
  realization :
    Beli2019Lemma99Realization (q := q) R₁ (R₂ + 2) R₁ β₁
  secondAlpha :
    realization.bong.alphaValue (1 : Fin 2) =
      (((R₁ - (R₂ + 2) : Int) : ℚ) + (β₁ : ℚ))
  represents :
    Lattice.Represents q q M realization.lattice

/-- The ternary construction in Beli (2019), Lemma 9.10.

The hypotheses `hLower` and `hUpper` are the part
`α₁ ≤ β₁ ≤ α₁ + 2` of the paper's bound.  The additional bound by `α₃`
is used only after the unchanged tail has been attached. -/
theorem beli2019Lemma910_ternary
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [ScaledHyperbolicMaximalLaws.{u, u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaSource : Beli2006AlphaLaws.{u, v} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    (reference : GoodBONG q M 3) (R₁ R₂ A₁ β₁ : Int)
    (horders : ∀ i, reference.order i = ![R₁, R₂, R₁] i)
    (hfirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ))
    (conditions :
      Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
    (hLower : A₁ ≤ β₁) (hUpper : β₁ ≤ A₁ + 2) :
    Nonempty (Beli2019Lemma910TernaryData reference R₁ R₂ A₁ β₁) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaSource
  rcases reference.beli2019Lemma99_sufficiency
      R₁ (R₂ + 2) β₁ conditions with ⟨D⟩
  have hrefZero : reference.order (0 : Fin 3) = R₁ := by
    simpa using horders (0 : Fin 3)
  have hrefOne : reference.order (1 : Fin 3) = R₂ := by
    simpa using horders (1 : Fin 3)
  have hrefTwo : reference.order (2 : Fin 3) = R₁ := by
    simpa using horders (2 : Fin 3)
  have hrefOuter :
      reference.order (0 : Fin 3) = reference.order (2 : Fin 3) := by
    rw [hrefZero, hrefTwo]
  have hDOuter :
      D.bong.order (0 : Fin 3) = D.bong.order (2 : Fin 3) :=
    D.outerOrders rfl
  have hfirstOrder :
      reference.order (0 : Fin 3) = D.bong.order (0 : Fin 3) := by
    rw [hrefZero, D.order_zero]
  have hrefSecond :=
    (reference.beli2019Remark87 (0 : Fin 1) hrefOuter).currentAlpha_eq
  change reference.alphaValue (1 : Fin 2) =
      ((reference.order (0 : Fin 3) - reference.order (1 : Fin 3) : Int) : ℚ) +
        reference.alphaValue (0 : Fin 2) at hrefSecond
  rw [hrefZero, hrefOne, hfirstAlpha] at hrefSecond
  have hDSecond :=
    (D.bong.beli2019Remark87 (0 : Fin 1) hDOuter).currentAlpha_eq
  change D.bong.alphaValue (1 : Fin 2) =
      ((D.bong.order (0 : Fin 3) - D.bong.order (1 : Fin 3) : Int) : ℚ) +
        D.bong.alphaValue (0 : Fin 2) at hDSecond
  rw [D.order_zero, D.order_one, D.firstAlpha] at hDSecond
  have hfirst : reference.alphaValue (0 : Fin 2) ≤
      D.bong.alphaValue (0 : Fin 2) := by
    rw [hfirstAlpha, D.firstAlpha]
    exact_mod_cast hLower
  have hsecond : D.bong.alphaValue (1 : Fin 2) ≤
      reference.alphaValue (1 : Fin 2) := by
    rw [hDSecond, hrefSecond]
    have hUpperQ : (β₁ : ℚ) ≤ (A₁ : ℚ) + 2 := by
      exact_mod_cast hUpper
    push_cast
    linarith
  have hrep : Lattice.Represents q q M D.lattice :=
    reference.beli2019Lemma98_sufficiency
      (alphaSource := alphaSource) (alphaModel := alphaModel)
      D.bong hrefOuter hDOuter hfirstOrder hfirst hsecond
  exact ⟨{
    realization := D
    secondAlpha := hDSecond
    represents := hrep
  }⟩

end BONG.GoodBONG

end Bong
