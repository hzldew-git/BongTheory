/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912AnisotropicAssembly
import Bong.Bong.Beli2019Necessity

/-!
# Beli (2019), Lemma 9.12: complete type-I reduction assembly

This file converts any proved type-I scalar package in the outer rank
convention of Lemma 9.12 into the literal index-uniformizer reduction used by
the Section 9 descent.  The defect condition between the original lattice and
the constructed sublattice follows from their actual inclusion via the
previous Beli (2006) representation theorem.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG.Beli2019Lemma910Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {r : QuadraticSpace K W}
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W} {N : Nat}

/-- The original target lattice satisfies condition (ii) relative to the
literal Lemma 9.10 sublattice because it represents that sublattice by
inclusion. -/
theorem representationDefectCondition_constructed
    [Beli2019InclusionConditionsLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q L (N + 5))
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D) :
    a.RepresentationDefectCondition
      (E.bong.castLength
        (show 3 + (N + 2) = (N + 2) + 3 by omega)) := by
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let target := E.bong.castLength hlength
  have hconditions : RepresentationConditions a target le_rfl :=
    a.representationConditions_of_lattice_le_via_adapter
      target E.inclusion.lattice_le
  simpa only [target] using hconditions.defectCondition

/-- The order bounds chosen in every type-I branch and the original order
condition imply condition (i) for the Lemma 9.10 output. -/
theorem representationOrderCondition_constructed
    {R₁ R₂ A₁ β₁ : Int}
    (a : GoodBONG q L (N + 5))
    (c : GoodBONG r M (N + 5))
    (data : Beli2019Lemma912TypeIBetaData a c A₁ β₁)
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4))) :
    (E.bong.castLength
      (show 3 + (N + 2) = (N + 2) + 3 by omega)).RepresentationOrderCondition
        c le_rfl := by
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let source := a.castLength hambient
  let comparison := c.castLength hambient
  have hsourceOrders' : ∀ i : Fin 3,
      source.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show source = a.castLength hambient by rfl, GoodBONG.order_castLength]
    exact hsourceOrders i
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  have hcomparisonZero : c.order (0 : Fin (N + 5)) = R₁ :=
    hfirst.symm.trans hR₁
  have hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 5)) := by
    simpa only [hR₂] using data.orderBounds.sourceSecondOrder
  have hsourceOrderCast :
      (source.castLength hlength).RepresentationOrderCondition
        (comparison.castLength hlength) le_rfl := by
    simpa only [source, comparison, castLength_castLength] using
      hsource.orderCondition
  have hcomparisonZeroCast :
      (comparison.castLength hlength).order (0 : Fin ((N + 2) + 3)) = R₁ := by
    simpa only [comparison, castLength_castLength] using hcomparisonZero
  have hcomparisonOneCast : R₂ + 2 ≤
      (comparison.castLength hlength).order (1 : Fin ((N + 2) + 3)) := by
    simpa only [comparison, castLength_castLength] using hcomparisonOne
  have horder := beli2019Lemma912_typeI_orderCondition
    source comparison D E hsourceOrders' hlength hcomparisonZeroCast
      hcomparisonOneCast hsourceOrderCast
  simpa only [comparison, castLength_castLength] using horder

/- A completed scalar package yields a reduction for the original, uncast
rank-`N+5` problem. -/
set_option maxHeartbeats 4000000 in
-- The proof normalizes two rank conventions and invokes the 2006 theorem once.
noncomputable def indexPReduction_of_outerTypeIScalarConditions
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [comparisonLaws : Beli2006AlphaLaws.{u, w} K]
    [structural : BONGStructuralLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    {R₁ R₂ A₁ β₁ : Int}
    (a : GoodBONG q L (N + 5))
    (c : GoodBONG r M (N + 5))
    (data : Beli2019Lemma912TypeIBetaData a c A₁ β₁)
    (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) D)
    (hsourceOrders : ∀ i : Fin 3,
      a.order (⟨i.1, by omega⟩ : Fin (N + 5)) = ![R₁, R₂, R₁] i)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (ambient : q.Represents r)
    (hsource : RepresentationConditions a c (Nat.le_refl (N + 4)))
    (hscalar : E.TypeIScalarConditions
      (a.castLength (show N + 5 = 3 + (N + 2) by omega)) c D
        (show 3 + (N + 2) = (N + 2) + 3 by omega)) :
    let problem := Beli2019RepresentationProblem.ofData
      a c (Nat.le_refl (N + 4)) ambient hsource
    Beli2019RepresentationProblem.IndexPReduction problem := by
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  let source := a.castLength hambient
  let target := E.bong.castLength hlength
  let comparison := c.castLength hambient
  have hsourceOrders' : ∀ i : Fin 3,
      source.order (Fin.castAdd (N + 2) i) = ![R₁, R₂, R₁] i := by
    intro i
    rw [show source = a.castLength hambient by rfl, GoodBONG.order_castLength]
    exact hsourceOrders i
  have hsourceNorm :
      RepresentationConditions (source.castLength hlength) c le_rfl := by
    simpa only [source, castLength_castLength] using hsource
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  have hcomparisonZero : c.order (0 : Fin (N + 5)) = R₁ :=
    hfirst.symm.trans hR₁
  have hcomparisonOne : R₂ + 2 ≤ c.order (1 : Fin (N + 5)) := by
    simpa only [hR₂] using data.orderBounds.sourceSecondOrder
  have hsourceOrderCast :
      (source.castLength hlength).RepresentationOrderCondition
        (comparison.castLength hlength) le_rfl := by
    simpa only [source, comparison, castLength_castLength] using
      hsource.orderCondition
  have hcomparisonZeroCast :
      (comparison.castLength hlength).order (0 : Fin ((N + 2) + 3)) = R₁ := by
    simpa only [comparison, castLength_castLength] using hcomparisonZero
  have hcomparisonOneCast : R₂ + 2 ≤
      (comparison.castLength hlength).order (1 : Fin ((N + 2) + 3)) := by
    simpa only [comparison, castLength_castLength] using hcomparisonOne
  have horderTargetRaw := beli2019Lemma912_typeI_orderCondition
    source comparison D E hsourceOrders' hlength hcomparisonZeroCast
      hcomparisonOneCast hsourceOrderCast
  have horderTarget : target.RepresentationOrderCondition c le_rfl := by
    simpa only [target, comparison, castLength_castLength] using horderTargetRaw
  have hsourceTargetConditions :
      RepresentationConditions (source.castLength hlength) target le_rfl := by
    exact (source.castLength hlength).representationConditions_of_lattice_le_via_adapter
      target E.inclusion.lattice_le
  have hfirstNorm : (source.castLength hlength).order
        (⟨0, by omega⟩ : Fin ((N + 2) + 3)) =
      c.order (⟨0, by omega⟩ : Fin ((N + 2) + 3)) := by
    have hsourceBack : source.castLength hlength = a := by
      exact castLength_castLength a hambient hlength
    rw [hsourceBack]
    convert hfirst using 1 <;> congr 1
  have htarget : RepresentationConditions target c le_rfl :=
    (E.representationConditions_iff_typeIScalarConditions
      (sourceLaws := sourceLaws) (targetLaws := comparisonLaws)
      source c D hsourceOrders' hlength
        hsourceTargetConditions.defectCondition hsourceNorm hfirstNorm
        horderTarget (by omega)).mpr (by simpa only [source] using hscalar)
  let problem := Beli2019RepresentationProblem.ofData
    a c (Nat.le_refl (N + 4)) ambient hsource
  change Beli2019RepresentationProblem.IndexPReduction problem
  exact {
    index_eq := rfl
    lattice := E.lattice
    inclusion := E.inclusion
    targetBONG := target
    conditions := htarget }

end BONG.GoodBONG.Beli2019Lemma910Data

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type v} [AddCommGroup X] [Module K X]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {s : QuadraticSpace K X}
  {r : QuadraticSpace K W}
  {L : Lattice K V} {P : Lattice K X} {M : Lattice K W} {N : Nat}

set_option maxHeartbeats 8000000 in
-- The theorem elaborates four construction branches and their scalar proofs.
/-- The five parameter branches of Lemma 9.12 reduce to the paper's separate
type-III construction or to a literal index-uniformizer reduction.  In each
of the four type-I branches this theorem constructs the beta parameter, invokes
Lemmas 9.9 and 9.10, verifies the scalar representation conditions, and returns
the resulting sublattice for the original representation problem. -/
theorem beli2019Lemma912_typeIIIParameters_or_typeIReduction
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
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
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
    Beli2019Lemma912TypeIIIParameters a c ∨
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl (N + 4)) ambient hsource)) := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  letI : Beli2009AlphaParityLaws.{u, v} K := parityV
  letI : BONGStructuralLaws.{u, v} K := structuralV
  let hambient : N + 5 = 3 + (N + 2) := by omega
  let hlength : 3 + (N + 2) = (N + 2) + 3 := by omega
  have C := Beli2019Lemma99Conditions.ofReferenceInvariants.{u, v}
    reference R₁ R₂ A₁ hrefOrders hrefFirstAlpha
  have hR₁ : a.order (0 : Fin (N + 5)) = R₁ := by
    simpa using hsourceOrders (0 : Fin 3)
  have hR₂ : a.order (1 : Fin (N + 5)) = R₂ := by
    simpa using hsourceOrders (1 : Fin 3)
  have finish (β₁ : Int)
      (data : Beli2019Lemma912TypeIBetaData a c A₁ β₁)
      (shifted : Beli2019Lemma99Conditions reference R₁ (R₂ + 2) β₁)
      (scalar : ∀
        (D : Beli2019Lemma99Realization (q := s) R₁ (R₂ + 2) R₁ β₁)
        (E : Beli2019Lemma910Data (a.castLength hambient) D),
          E.TypeIScalarConditions (a.castLength hambient) c D hlength) :
      Nonempty (Beli2019RepresentationProblem.IndexPReduction
        (Beli2019RepresentationProblem.ofData
          a c (Nat.le_refl (N + 4)) ambient hsource)) := by
    rcases beli2019Lemma912_exists_lemma910Data_of_typeIBetaData.{u, v, w}
      (disc := disc) (constructionV := constructionV)
      (sectionTwoV := sectionTwoV) (structuralV := structuralV)
      (structuralModel := structuralModel) (alphaV := alphaV)
      (alphaModel := alphaModel) (classificationModel := classificationModel)
      reference a c data hrefOrders hrefFirstAlpha hsourceOrders hprefix
        shifted with ⟨D, ⟨E⟩⟩
    have hscalar := scalar D E
    exact ⟨E.indexPReduction_of_outerTypeIScalarConditions
      (sourceLaws := alphaV) (comparisonLaws := alphaW)
      (structural := structuralV) (representationLaws := representationLaws)
      a c data D hsourceOrders hfirst ambient hsource hscalar⟩
  rcases beli2019Lemma912_parameterBranches.{u, v, w}
      (K := K) a c profile with
    ⟨hfull, hfirstAlpha, hlarge⟩ |
    ⟨hfull, hfirstAlpha, hone⟩ |
    ⟨hstrict, hbelow⟩ |
    ⟨hstrict, hhalf, hisotropic⟩ |
    ⟨hstrict, hhalf, hanisotropic⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_equalSecondLarge
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hfirstAlpha hlarge with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hsourceFirstAlpha
    subst A
    letI : Beli2009AlphaParityLaws.{u, w} K := parityW
    have shifted := Beli2019Lemma99Conditions.ofEqualSecondLarge
      (alphaV := alphaV) (alphaW := alphaW) reference a c profile
      R₁ R₂ A₁ C hfirst hR₁ hR₂ hsourceFirstAlpha hfirstAlpha hlarge
    exact finish A₁ data shifted (by
      intro D E
      have hdefectTarget := E.representationDefectCondition_constructed a D
      exact E.typeIScalarConditions_of_equalSecondLarge
        (sourceLaws := alphaV) (targetLaws := alphaW)
        a c data D hsourceOrders hfull hfirstAlpha hdefectTarget)
  · left
    exact ⟨hfull, hfirstAlpha, hone⟩
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_belowHalfGap
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict hbelow with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hsourceFirstAlpha
    subst A
    have shifted := C.ofBelowHalfGap reference a c profile R₁ R₂ A₁
      hR₁ hR₂ hsourceFirstAlpha hbelow
    exact finish (A₁ + 2) data shifted (by
      intro D E
      have hdefectTarget := E.representationDefectCondition_constructed a D
      exact E.typeIScalarConditions_of_belowHalfGap
        (sourceLaws := alphaV) (sourceParity := parityV)
        (targetLaws := alphaW) (targetParity := parityW)
        a c profile data D hsourceOrders hfirst hstrict hbelow
          hdefectTarget hsource.defectCondition)
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapIsotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict hhalf with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hsourceFirstAlpha
    subst A
    have shifted := C.ofHalfGapIsotropic reference a c profile R₁ R₂ A₁
      hR₁ hR₂ hsourceFirstAlpha hhalf (hrefIsotropy.mpr hisotropic)
    exact finish (A₁ + 1) data shifted (by
      intro D E
      have horderTarget := E.representationOrderCondition_constructed
        a c data D hsourceOrders hfirst hsource
      exact E.typeIScalarConditions_of_halfGapIsotropic
        (sourceLaws := alphaV) (targetLaws := alphaW)
        (targetParity := parityW)
        a c profile data D hsourceOrders hstrict hhalf horderTarget)
  · right
    rcases exists_beli2019Lemma912TypeIBetaData_of_halfGapAnisotropic
      (alphaV := alphaV) (parityV := parityV) (alphaW := alphaW)
      a c profile hfirst hstrict with ⟨A, data⟩
    have hA : A = A₁ := by
      exact_mod_cast data.firstAlpha.symm.trans hsourceFirstAlpha
    subst A
    have hgapSharp :=
      a.beli2019Lemma912_firstGap_le_twoE_sub_four_of_strict_anisotropic
        (alphaV := alphaV) (parityV := parityV)
        (alphaW := alphaW) (parityW := parityW)
        c profile hstrict hhalf hanisotropic
    have hrefAnisotropic : reference.Lemma814FirstThreeAnisotropic := by
      apply (reference.not_firstThreeIsotropic_iff_anisotropic).mp
      intro hrefIsotropic
      exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic
        (hrefIsotropy.mp hrefIsotropic)
    have shifted := C.ofHalfGapAnisotropic reference a R₁ R₂ A₁
      hR₁ hR₂ hsourceFirstAlpha hhalf hgapSharp hrefAnisotropic
    exact finish A₁ data shifted (by
      intro D E
      have hdefectTarget := E.representationDefectCondition_constructed a D
      have horderTarget := E.representationOrderCondition_constructed
        a c data D hsourceOrders hfirst hsource
      exact E.typeIScalarConditions_of_halfGapAnisotropic
        (sourceLaws := alphaV) (comparisonLaws := alphaW)
        (sourceParity := parityV) (comparisonParity := parityW)
        (structural := structuralV)
        reference C a c profile data D hsourceOrders hfirst hstrict hhalf
          hrefIsotropy ambient hsource hdefectTarget horderTarget
            hanisotropic)

end BONG.GoodBONG

end Bong
