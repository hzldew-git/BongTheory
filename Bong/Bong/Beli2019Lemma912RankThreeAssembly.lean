/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankThreeScalar
import Bong.Bong.Beli2019Lemma912RankThreeTypeI
import Bong.Bong.Beli2019Lemma96RankThree
import Bong.Bong.Beli2019Necessity

/-!
# Beli (2019), Lemma 9.12: ternary branch assembly

The equal-alpha, below-half-gap, and isotropic half-gap branches are assembled
here into literal index-uniformizer reductions.  The type-III branch is
returned in the form consumed by the all-rank type-III construction.  The
only branch left visible is the anisotropic half-gap branch, which contains
the separate Lemma 9.6 endpoint.
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

set_option maxHeartbeats 8000000 in
-- Lemma 9.10, the ternary scalar endpoint, and the three branches elaborate together.
/-- Every ternary residual parameter branch is type III, the anisotropic
half-gap residual branch, or a literal index-`p` reduction. -/
theorem beli2019Lemma912_rankThree_typeIII_or_anisotropic_or_reduction
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
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl 2)) :
    Beli2019Lemma912TypeIIIParametersAllRanks (T := 0) a c ∨
      Beli2019Lemma96BoundaryRankThree a c ∨
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 2) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  letI : BONGStructuralLaws.{u, v} K := structuralV
  let R₁ : Int := a.order (0 : Fin 3)
  let R₂ : Int := a.order (1 : Fin 3)
  let hlength : 3 + 0 = 0 + 3 := by omega
  have horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 0 i) = ![R₁, R₂, R₁] i := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · change a.order (2 : Fin 3) = a.order (0 : Fin 3)
      exact profile.firstThird_eq.symm
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hcCast : c.castLength hlength = c := by
    cases hlength
    rfl
  have finish (A₁ β₁ : Int)
      (data : Beli2019Lemma912TypeIBetaDataRankThree a c A₁ β₁)
      (shifted : Beli2019Lemma99Conditions a R₁ (R₂ + 2) β₁)
      (scalar : ∀
        (D : Beli2019Lemma99Realization (q := q) R₁ (R₂ + 2) R₁ β₁)
        (E : Beli2019Lemma910Data (N := 0) a D),
          (a.castLength hlength).RepresentationDefectCondition
              (E.bong.castLength hlength) →
          (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl →
          E.TypeIScalarConditions a c D hlength) :
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 2) ambient hsource)) := by
    have hprefix : ∀ i : Fin 3,
        a.valueUnit i = a.valueUnit (Fin.castAdd 0 i) := by
      intro i
      congr 1
    rcases beli2019Lemma910 (N := 0)
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
      a a horders data.firstAlpha horders hprefix shifted
        (by intro hzero; omega) data.betaLower data.betaUpper
        (by intro hzero; omega) with ⟨D, ⟨E⟩⟩
    let target := E.bong.castLength hlength
    have hsourceTargetRaw : RepresentationConditions a target le_rfl :=
      a.representationConditions_of_lattice_le_via_adapter
        target E.inclusion.lattice_le
    have hsourceTarget : RepresentationConditions
        (a.castLength hlength) target le_rfl := by
      simpa only [haCast] using hsourceTargetRaw
    have hcZero : (c.castLength hlength).order (0 : Fin 3) = R₁ := by
      rw [hcCast]
      exact hfirst.symm
    have hcOne : R₂ + 2 ≤
        (c.castLength hlength).order (1 : Fin 3) := by
      rw [hcCast]
      exact data.sourceSecondOrder
    have hsourceOrderCast : (a.castLength hlength).RepresentationOrderCondition
        (c.castLength hlength) le_rfl := by
      simpa only [haCast, hcCast] using hsource.orderCondition
    have horderRaw := beli2019Lemma912_typeI_orderCondition
      a c D E horders hlength hcZero hcOne hsourceOrderCast
    have horderTarget : target.RepresentationOrderCondition c le_rfl := by
      simpa only [target, hcCast] using horderRaw
    have hsourceNorm : RepresentationConditions
        (a.castLength hlength) c le_rfl := by
      simpa only [haCast] using hsource
    have hfirstNorm : (a.castLength hlength).order (0 : Fin 3) =
        c.order (0 : Fin 3) := by
      simpa only [haCast] using hfirst
    have hscalar := scalar D E hsourceTarget.defectCondition horderTarget
    have reduction :=
      E.indexPReduction_of_typeIScalarConditions_rankThree
        (sourceLaws := alphaV) (targetLaws := alphaW)
        a c D horders hlength hsourceTarget.defectCondition hsourceNorm
          hfirstNorm horderTarget ambient hscalar
    simpa only [haCast] using (show Nonempty _ from ⟨reduction⟩)
  rcases a.beli2019Lemma912_parameterBranches_rankThree c profile with
    ⟨hfull, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, hhalf, hisotropic⟩ |
    ⟨hstrict, hhalf, hanisotropic⟩
  · right
    right
    rcases exists_beli2019Lemma912TypeIBetaDataRankThree_of_equalSecondLarge
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hfirstAlpha hlarge with ⟨A₁, data⟩
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      a R₁ R₂ A₁ horders data.firstAlpha
    letI : Beli2009AlphaParityLaws.{u, w} K := parityW
    have shifted := C.ofEqualSecondLarge_rankThree
      (alphaV := alphaV) (alphaW := alphaW)
      a c profile R₁ R₂ A₁ hfirst rfl rfl data.firstAlpha
        hfirstAlpha hlarge
    exact finish A₁ A₁ data shifted (by
      intro D E hdefect _
      exact E.typeIScalarConditions_of_equalSecondLarge_rankThree
        (sourceLaws := alphaV) (targetLaws := alphaW)
        a c data D horders hlength hfull hfirstAlpha hdefect)
  · left
    exact ⟨hfull, hfirstAlpha, hone⟩
  · right
    right
    rcases exists_beli2019Lemma912TypeIBetaDataRankThree_of_belowHalfGap
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict with ⟨A₁, data⟩
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      a R₁ R₂ A₁ horders data.firstAlpha
    have shifted := C.ofBelowHalfGap_rankThree
      a c profile R₁ R₂ A₁ rfl rfl data.firstAlpha hbelow
    exact finish A₁ (A₁ + 2) data shifted (by
      intro D E hdefect _
      exact E.typeIScalarConditions_of_belowHalfGap_rankThree
        (sourceLaws := alphaV) (sourceParity := parityV)
        (targetLaws := alphaW) (targetParity := parityW)
        a c profile data D horders hlength hfirst hstrict hbelow
          hdefect (by simpa only [haCast] using hsource.defectCondition))
  · right
    right
    rcases exists_beli2019Lemma912TypeIBetaDataRankThree_of_halfGapIsotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict with ⟨A₁, data⟩
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      a R₁ R₂ A₁ horders data.firstAlpha
    have shifted := C.ofHalfGapIsotropic_rankThree
      a c profile R₁ R₂ A₁ rfl rfl data.firstAlpha hhalf hisotropic
    exact finish A₁ (A₁ + 1) data shifted (by
      intro D E _ horder
      exact E.typeIScalarConditions_of_halfGapIsotropic_rankThree
        (sourceLaws := alphaV) (targetLaws := alphaW)
        (targetParity := parityW) a c profile data D horders hlength
          hstrict hhalf horder)
  · right
    by_cases hboundary : a.orderGap (0 : Fin 2) =
        2 * (ramificationIndex K : Int) - 2
    · left
      rcases exists_beli2019Lemma912TypeIBetaDataRankThree_of_halfGapAnisotropic
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict with ⟨A₁, data⟩
      have hdefect :=
        Beli2019Lemma910Data.lemma96DefectBound_of_anisotropicBoundary_rankThree
          (targetLaws := alphaW) (targetParity := parityW)
          a c data hboundary hhalf hstrict
      exact ⟨profile.firstThird_eq, hfirst, hboundary, hdefect, hanisotropic⟩
    · right
      have hgapSharp : a.orderGap (0 : Fin 2) ≤
          2 * (ramificationIndex K : Int) - 4 := by
        rcases profile.firstGap_even with ⟨z, hz⟩
        have hbound := profile.firstGap_le_twoE_sub_two
        omega
      rcases exists_beli2019Lemma912TypeIBetaDataRankThree_of_halfGapAnisotropic
        (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
        a c profile hfirst hstrict with ⟨A₁, data⟩
      have C := Beli2019Lemma99Conditions.ofReferenceInvariants
        a R₁ R₂ A₁ horders data.firstAlpha
      have shifted := C.ofHalfGapAnisotropic_rankThree
        a R₁ R₂ A₁ rfl rfl data.firstAlpha hhalf hgapSharp hanisotropic
      exact finish A₁ A₁ data shifted (by
        intro D E hdefect horder
        exact E.typeIScalarConditions_of_halfGapAnisotropic_rankThree
          (sourceLaws := alphaV) (comparisonLaws := alphaW)
          (sourceParity := parityV) (comparisonParity := parityW)
          (structural := structuralV)
          a c C data D horders hlength hfirst hstrict hhalf hgapSharp
            ambient (by simpa only [haCast] using hsource) hdefect horder
              (by simpa only [haCast] using hanisotropic))

set_option maxHeartbeats 8000000 in
-- This theorem runs the full ternary case split and then constructs the
-- separate Lemma 9.6 normal form in its sole anisotropic endpoint.
/-- Every ternary residual branch is now either type III or a literal
rank-lowering reduction.  In particular, the former visible Lemma 9.6
boundary has been discharged constructively. -/
theorem beli2019Lemma912_rankThree_typeIII_or_headReduction_or_reduction
    [QuadraticDefectLaws K]
    [disc : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
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
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [classificationModel : GoodBONGClassificationLaws.{u, v, u} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L 3) (c : GoodBONG r M 3)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 0) a c)
    (hfirst : a.order (0 : Fin 3) = c.order (0 : Fin 3))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl 2)) :
    Beli2019Lemma912TypeIIIParametersAllRanks (T := 0) a c ∨
      Nonempty (Beli2019RepresentationProblem.HeadReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 2) ambient hsource)) ∨
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 2) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  letI : BONGStructuralLaws.{u, v} K := structuralV
  rcases a.beli2019Lemma912_rankThree_typeIII_or_anisotropic_or_reduction
      (disc := disc)
      (constructionV := constructionV) (sectionTwoV := sectionTwoV)
      (structuralV := structuralV) (structuralModel := structuralModel)
      (alphaV := alphaV) (alphaW := alphaW) (alphaModel := alphaModel)
      (parityV := parityV) (parityW := parityW)
      (classificationModel := classificationModel)
      (representationLaws := representationLaws)
      c profile hfirst ambient hsource with htypeIII | hboundary | hreduction
  · exact Or.inl htypeIII
  · letI : BONGStructuralLaws.{u, u} K := structuralModel
    exact Or.inr (Or.inl
      (a.exists_beli2019Lemma96_headReduction_rankThree
        (targetAlpha := alphaV) (sourceAlpha := alphaW)
        (modelAlpha := alphaModel) c hboundary ambient hsource))
  · exact Or.inr (Or.inr hreduction)

end BONG.GoodBONG

end Bong
