/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912RankFourTypeIAssembly

/-!
# Beli (2019), Lemma 9.12: quaternary assembly

The literal initial ternary segment supplies the reference lattice for
Lemma 9.9.  Each type-I branch is realized by Lemma 9.10 and converted into
an index-`p` reduction; the remaining type-III branch uses the all-rank
construction.
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

set_option maxHeartbeats 12000000 in
-- All four Lemma 9.10 branches and the all-rank type-III branch elaborate together.
/-- Complete literal-rank-four form of Beli (2019), Lemma 9.12. -/
theorem exists_beli2019Lemma912_indexPReduction_rankFour
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
    [localizationV : Beli2009AlphaLocalizationLaws.{u, v} K]
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
    (a : GoodBONG q L 4) (c : GoodBONG r M 4)
    (profile : Beli2019Lemma912InitialProfileAllRanks (T := 1) a c)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    (hfirst : a.order (0 : Fin 4) = c.order (0 : Fin 4))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl 3)) :
    Nonempty (Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData
        a c (Nat.le_refl 3) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  letI : BONGStructuralLaws.{u, v} K := structuralV
  let reference := a.lemma814InitialThree
  let R₁ : Int := a.order (0 : Fin 4)
  let R₂ : Int := a.order (1 : Fin 4)
  let hlength : 3 + 1 = 1 + 3 := rfl
  have horders : ∀ i : Fin 3,
      a.order (Fin.castAdd 1 i) = ![R₁, R₂, R₁] i := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · change a.order (2 : Fin 4) = a.order (0 : Fin 4)
      exact profile.firstThird_eq.symm
  have hrefOrders : ∀ i : Fin 3,
      reference.order i = ![R₁, R₂, R₁] i := by
    intro i
    rw [show reference = a.lemma814InitialThree by rfl,
      a.lemma814InitialThree_order_eq]
    fin_cases i
    · rfl
    · rfl
    · exact profile.firstThird_eq.symm
  have hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd 1 i) := by
    intro i
    rw [show reference = a.lemma814InitialThree by rfl,
      a.lemma814InitialThree_valueUnit_eq]
    congr 1
  have haCast : a.castLength hlength = a := by
    cases hlength
    rfl
  have hrefIsotropy : reference.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
    simpa only [reference] using a.lemma814InitialThree_firstThreeIsotropic_iff
  have finish (A₁ β₁ : Int)
      (data : Beli2019Lemma912TypeIBetaDataRankFour a c A₁ β₁)
      (shifted : Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
      (scalar : ∀
        (D : Beli2019Lemma99Realization
          (q := q.restrict a.lemma814InitialThreeSegment.carrier
            a.lemma814InitialThreeSegment.nondegenerate)
          R₁ (R₂ + 2) R₁ β₁)
        (E : Beli2019Lemma910Data (N := 1) a D),
          (a.castLength hlength).RepresentationDefectCondition
              (E.bong.castLength hlength) →
          (E.bong.castLength hlength).RepresentationOrderCondition c le_rfl →
          E.TypeIScalarConditions a c D hlength) :
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl 3) ambient hsource)) := by
    have hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
      calc
        reference.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
          simpa only [reference] using a.lemma814InitialThree_firstAlpha_eq hbinary
        _ = (A₁ : ℚ) := data.firstAlpha
    exact exists_indexPReduction_of_rankFourTypeIScalar
      (disc := disc)
      (constructionV := constructionV)
      (sectionTwoV := sectionTwoV)
      (structuralV := structuralV)
      (structuralModel := structuralModel)
      (alphaV := alphaV)
      (alphaW := alphaW)
      (alphaModel := alphaModel)
      (classificationModel := classificationModel)
      (representationLaws := representationLaws)
      reference a c data hrefOrders hrefFirstAlpha horders hprefix shifted
        hfirst ambient hsource scalar
  rcases a.beli2019Lemma912_parameterBranches_rankFour c profile with
    ⟨hfull, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, hhalf, hisotropic⟩ |
    ⟨hstrict, hhalf, hanisotropic⟩
  · rcases exists_beli2019Lemma912TypeIBetaDataRankFour_of_equalSecondLarge
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hfirstAlpha hlarge with ⟨A₁, data⟩
    have hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
      calc
        reference.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
          simpa only [reference] using a.lemma814InitialThree_firstAlpha_eq hbinary
        _ = (A₁ : ℚ) := data.firstAlpha
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
    letI : Beli2009AlphaParityLaws.{u, w} K := parityW
    have shifted := C.ofEqualSecondLarge_rankFour
      (alphaV := alphaV) (alphaW := alphaW)
      reference a c profile R₁ R₂ A₁ hfirst rfl rfl data.firstAlpha
        hfirstAlpha hlarge
    exact finish A₁ A₁ data shifted (by
      intro D E hdefect _
      exact E.typeIScalarConditions_of_equalSecondLarge_rankFour
        (sourceLaws := alphaV) (targetLaws := alphaW)
        a c data D horders hlength hfull hfirstAlpha hdefect)
  · have hparams : Beli2019Lemma912TypeIIIParametersAllRanks (T := 1) a c :=
      ⟨hfull, hfirstAlpha, hone⟩
    exact exists_beli2019Lemma912_typeIIIIndexPReduction_of_profile_allRanks
      (sourceAlpha := alphaV) (comparisonAlpha := alphaW)
      (sourceParity := parityV) (comparisonParity := parityW)
      (classificationV := classificationV) (classificationW := classificationW)
      (structural := structuralV) (representationLaws := representationLaws)
      a c profile hparams hfirst ambient hsource
  · rcases exists_beli2019Lemma912TypeIBetaDataRankFour_of_belowHalfGap
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict hbelow with ⟨A₁, data⟩
    have hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
      calc
        reference.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
          simpa only [reference] using a.lemma814InitialThree_firstAlpha_eq hbinary
        _ = (A₁ : ℚ) := data.firstAlpha
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
    have shifted := C.ofBelowHalfGap_rankFour
      reference a c profile R₁ R₂ A₁ rfl rfl data.firstAlpha hbelow
    exact finish A₁ (A₁ + 2) data shifted (by
      intro D E hdefect _
      exact E.typeIScalarConditions_of_belowHalfGap_rankFour
        (sourceLaws := alphaV) (sourceParity := parityV)
        (targetLaws := alphaW) (targetParity := parityW)
        a c profile data D horders hlength hfirst hstrict hbelow
          hdefect (by simpa only [haCast] using hsource.defectCondition))
  · rcases exists_beli2019Lemma912TypeIBetaDataRankFour_of_halfGapIsotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict hhalf with ⟨A₁, data⟩
    have hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
      calc
        reference.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
          simpa only [reference] using a.lemma814InitialThree_firstAlpha_eq hbinary
        _ = (A₁ : ℚ) := data.firstAlpha
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
    have hrefIso : reference.Lemma814FirstThreeIsotropic := hrefIsotropy.mpr hisotropic
    have shifted := C.ofHalfGapIsotropic_rankFour
      reference a c profile R₁ R₂ A₁ rfl rfl data.firstAlpha hhalf hrefIso
    exact finish A₁ (A₁ + 1) data shifted (by
      intro D E _ horder
      exact E.typeIScalarConditions_of_halfGapIsotropic_rankFour
        (sourceLaws := alphaV) (targetLaws := alphaW)
        (targetParity := parityW)
        a c profile data D horders hlength hstrict hhalf horder)
  · rcases exists_beli2019Lemma912TypeIBetaDataRankFour_of_halfGapAnisotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict with ⟨A₁, data⟩
    have hgapSharp :=
      Beli2019Lemma910Data.firstGap_le_twoE_sub_four_of_strict_anisotropic_rankFour
        (sourceLaws := alphaV) (sourceParity := parityV)
        (targetLaws := alphaW) (targetParity := parityW)
        a c profile data hstrict hhalf hanisotropic
    have hrefFirstAlpha : reference.alphaValue (0 : Fin 2) = (A₁ : ℚ) := by
      calc
        reference.alphaValue (0 : Fin 2) = a.alphaValue (0 : Fin 3) := by
          simpa only [reference] using a.lemma814InitialThree_firstAlpha_eq hbinary
        _ = (A₁ : ℚ) := data.firstAlpha
    have C := Beli2019Lemma99Conditions.ofReferenceInvariants
      reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
    have hrefAniso : reference.Lemma814FirstThreeAnisotropic := by
      apply (reference.not_firstThreeIsotropic_iff_anisotropic).mp
      intro hrefIso
      exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic
        (hrefIsotropy.mp hrefIso)
    have shifted := C.ofHalfGapAnisotropic_rankFour
      reference a R₁ R₂ A₁ rfl rfl data.firstAlpha hhalf hgapSharp hrefAniso
    exact finish A₁ A₁ data shifted (by
      intro D E hdefect horder
      exact E.typeIScalarConditions_of_halfGapAnisotropic_rankFour
        (sourceLaws := alphaV) (comparisonLaws := alphaW)
        (sourceParity := parityV) (comparisonParity := parityW)
        (structural := structuralV)
        reference C a c data D horders hlength hfirst hstrict hhalf hgapSharp
          hrefAniso ambient (by simpa only [haCast] using hsource)
            hdefect horder (by simpa only [haCast] using hanisotropic))

end BONG.GoodBONG

end Bong
