/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912Complete
import Bong.Bong.Beli2019Lemma814HigherRankUnequal

/-!
# Beli (2019), Lemma 9.12 with the literal initial ternary segment

The type-I construction uses a ternary reference lattice.  This file removes
that reference from the public interface: it is the actual first three vectors
of the target good BONG.  Consequently its orders, units, first alpha, and
isotropy status are witnessed by the original target rather than postulated.
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

set_option maxHeartbeats 12000000 in
-- The wrapper instantiates the complete type-I/type-III construction package.
/-- Fixed-rank Lemma 9.12 using the literal initial ternary segment of `a`. -/
theorem exists_beli2019Lemma912_indexPReduction_of_initialThree
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
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 4)) : WithTop ℚ))
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4))) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl (N + 4)) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  rcases a.beli2019Lemma912_firstAlpha_integral c profile with ⟨A₁, hA₁⟩
  let R₁ : Int := a.order (0 : Fin (N + 5))
  let R₂ : Int := a.order (1 : Fin (N + 5))
  have hrefOrders : ∀ i : Fin 3,
      a.lemma814InitialThree.order i = ![R₁, R₂, R₁] i := by
    intro i
    rw [a.lemma814InitialThree_order_eq]
    fin_cases i
    · rfl
    · rfl
    · exact profile.firstThird_eq.symm
  have hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · exact profile.firstThird_eq.symm
  have hrefFirstAlpha :
      a.lemma814InitialThree.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
    rw [a.lemma814InitialThree_firstAlpha_eq hbinary]
    exact hA₁
  have hprefix : ∀ i : Fin 3,
      a.lemma814InitialThree.valueUnit i =
        a.valueUnit (⟨i.1, by omega⟩ : Fin (N + 5)) :=
    a.lemma814InitialThree_valueUnit_eq
  exact exists_beli2019Lemma912_indexPReduction
    (disc := disc) (constructionV := constructionV)
    (sectionTwoV := sectionTwoV) (structuralV := structuralV)
    (structuralModel := structuralModel) (alphaV := alphaV)
    (alphaW := alphaW) (alphaModel := alphaModel)
    (parityV := parityV) (parityW := parityW)
    (classificationModel := classificationModel)
    (classificationV := classificationV) (classificationW := classificationW)
    (representationLaws := representationLaws)
    a.lemma814InitialThree a c profile R₁ R₂ A₁ hrefOrders
      hrefFirstAlpha hsourceOrders hA₁ hprefix hfirst
        a.lemma814InitialThree_firstThreeIsotropic_iff ambient hsource

end BONG.GoodBONG

end Bong
