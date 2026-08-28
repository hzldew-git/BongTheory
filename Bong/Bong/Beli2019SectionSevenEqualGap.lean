/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ComplementaryHilbertChoice
import Bong.Bong.Beli2019Lemma714Stopping
import Bong.Bong.Beli2019Lemma716SpecialReduction
import Bong.Bong.Beli2019Lemma717Stopping
import Bong.Bong.Beli2019Lemma718Preparation
import Bong.Bong.Beli2019Lemma718Volume
import Bong.Bong.Beli2019Lemma720
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Section 7: the exceptional first-gap reduction

This file assembles the equal-first-gap branch of Section 7.  The stopping
index of Lemma 7.17 is chosen automatically.  The formally delicate boundary
case is type II with `s = 2`: the construction of Lemma 7.18 is then the
identity, so it is routed through the strict special lattice of Lemmas
7.14--7.16 instead.  Every other case gives the literal strict sublattice of
Lemmas 7.18--7.20.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

/-- At the initial endpoint, type II with stopping index two is exactly the
discriminant binary class used by Lemmas 7.14--7.16. -/
theorem lemma717_typeII_two_adjacentUnitSquareClass
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (R : Int)
    (hfirst : a.order (0 : Fin (n + 3)) = R)
    (hsecond : a.order (1 : Fin (n + 3)) =
      R - 2 * (ramificationIndex K : Int))
    (hII : Lemma717IsTypeII a R 2) :
    a.toBONG.adjacentUnitSquareClass (0 : Fin (n + 3)) (by simp) =
      unitSquareClass K (lemma712DiscriminantParameter (K := K)) := by
  have hgap : a.order (1 : Fin (n + 3)) -
      a.order (0 : Fin (n + 3)) =
        -(2 * (ramificationIndex K : Int)) := by
    rw [hfirst, hsecond]
    ring
  rcases a.toBONG.adjacentUnitSquareClass_endpoint_cases
      (0 : Fin (n + 3)) (by simp) hgap with hquarter | hdiscriminant
  · have hparameterSquare : IsSquare
        (-(a.toBONG.adjacentParameter (0 : Fin (n + 3)) (by simp))) :=
      isSquare_neg_of_unitSquareClass_eq_negativeQuarter hquarter
    have hproduct :
        -(a.toBONG.valueUnit (0 : Fin (n + 3)) *
            a.toBONG.valueUnit (1 : Fin (n + 3))) =
          (-(a.toBONG.adjacentParameter
              (0 : Fin (n + 3)) (by simp))) *
            a.toBONG.valueUnit (0 : Fin (n + 3)) ^ 2 := by
      unfold BONG.adjacentParameter
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero
        (a.toBONG.valueUnit (0 : Fin (n + 3)))]
      <;> simp
    have hpairSquare : IsSquare
        (-(a.toBONG.valueUnit (0 : Fin (n + 3)) *
          a.toBONG.valueUnit (1 : Fin (n + 3)))) := by
      rw [hproduct]
      exact hparameterSquare.mul
        ⟨a.toBONG.valueUnit (0 : Fin (n + 3)), by simp [pow_two]⟩
    have hsigned : IsSquare
        (a.toBONG.signedEvenPrefixProduct (2 / 2)) := by
      have hrec := a.toBONG.signedEvenPrefixProduct_succ 0 (by omega)
      norm_num at hrec ⊢
      rw [hrec]
      simpa [BONG.signedEvenPrefixProduct] using hpairSquare
    exact (lemma717_typeI_typeII_disjoint a R 2
      ⟨⟨hII.1, hsigned⟩, hII⟩).elim
  · simpa only [lemma712DiscriminantParameter] using hdiscriminant

/-- The two valuation units used in Lemmas 7.14--7.16 can be chosen from
the dyadic unit-defect spectrum, with the required negative Hilbert symbol. -/
theorem exists_lemma716SpecialUnits
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K] :
    ∃ ε η : Kˣ,
      IsValuationUnit K (ε : K) ∧
      IsValuationUnit K (η : K) ∧
      defectOrder (K := K) ε = (1 : WithTop ℚ) ∧
      defectOrder (K := K) η =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ∧
      hilbertSymbol K ε η = -1 := by
  have hoddOne : IsOddRationalInteger (1 : ℚ) := by
    refine ⟨1, odd_one, ?_⟩
    norm_num
  have hOneLt : (1 : ℚ) < 2 * (ramificationIndex K : ℚ) := by
    have he := ramificationIndex_pos (K := K)
    exact_mod_cast (show 1 < 2 * ramificationIndex K by omega)
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (K := K) 1 hoddOne (by norm_num) hOneLt with
    ⟨ε, hεUnit, hεDefect⟩
  rcases exists_complementaryDefect_hilbert_neg
      (K := K) ε 1 hεDefect (by norm_num) hOneLt with
    ⟨η, hηUnit, hηDefect, hhilbert⟩
  refine ⟨ε, η, hεUnit, hηUnit, hεDefect, ?_, ?_⟩
  · simpa using hηDefect
  · rw [hilbertSymbol_comm K ε η]
    exact hhilbert

section Laws

variable
    [defect : QuadraticDefectLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [unramified : DyadicUnramifiedNormLaws K]
    [residueDefect : DyadicResidueDefectProductLaws K]
    [hilbertChoice : DyadicHilbertDefectChoiceLaws K]
    [unitParity : UnitQuadraticDefectParityLaws K]
    [unitSpectrum : DyadicUnitDefectSpectrumLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [structuralModel : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaModel : Beli2006AlphaLaws.{u, u} K]
    [constructionModel : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoModel : Beli2006SectionTwoLaws.{u, u} K]
    [classificationModel : GoodBONGClassificationLaws.{u, u, u} K]
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [parityV : Beli2009AlphaParityLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [binaryLocal : BinaryNormGeneratorLocalLaws.{u, v} K]
    [lemma49 : BeliLemma49Laws.{u, v} K]
    [towerRepresentation :
      DyadicAlternatingEndpointTowerRepresentationLaws K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [lemma310 : Beli2019Lemma310RepresentationLaws.{u, v, v} K]

/-- The complete equal-first-gap branch of Section 7.  If the source norm is
strictly smaller, the four conditions can always be transferred to a literal
strict sublattice of the target.  The theorem includes the `s = 2` type-II
dispatch, so callers do not need to distinguish any of Lemmas 7.14--7.20. -/
theorem exists_sectionSevenEqualGapSublatticeReduction
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q N (n + 3))
    (hac : RepresentationConditions a b le_rfl)
    (hgap : a.order (1 : Fin (n + 3)) -
      a.order (0 : Fin (n + 3)) =
        -(2 * (ramificationIndex K : Int)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    Nonempty (Beli2019RepresentationProblem.SublatticeReduction
      (Beli2019RepresentationProblem.ofData a b le_rfl
        (QuadraticSpace.represents_refl q) hac)) := by
  let R := a.order (0 : Fin (n + 3))
  have hfirst : a.order (0 : Fin (n + 3)) = R := rfl
  have hsecond : a.order (1 : Fin (n + 3)) =
      R - 2 * (ramificationIndex K : Int) := by
    dsimp only [R]
    omega
  rcases a.exists_lemma717StoppingData R hsecond with ⟨s, stopping⟩
  rcases exists_lemma718NormalizedRealization
      (alphaV := alphaV) (alphaBase := alphaModel)
      (laws := laws) (unramified := unramified)
      (corollary44V := corollary44V) (binaryLocal := binaryLocal)
      (lemma49 := lemma49)
      (defect := defect) (hilbert := hilbert) (diagonal := diagonal)
      (perfect := perfect) (structural := structuralModel)
      (weight := weight) (unaryBinary := unaryBinary)
      (jordanOrder := jordanOrder)
      (constructionBase := constructionModel)
      (sectionTwoBase := sectionTwoModel)
      (classification := classificationModel)
      (sectionFourV := sectionFourV) (constructionV := constructionV)
      (sectionTwoV := sectionTwoV)
      a R s stopping hfirst with
    ⟨c, horder, realization⟩
  have hconditionsC : RepresentationConditions c b le_rfl :=
    (a.representationConditions_changeBONG_iff c b b le_rfl).mp hac
  rcases realization with ⟨realization⟩
  cases realization with
  | typeI D =>
      exact ⟨{
        index_eq := rfl
        lattice := D.target
        lattice_le := D.lattice_le
        volumeOrder_lt := D.volumeOrder_lt c R s
        targetBONG := D.bong
        conditions :=
          (Beli2019Lemma718NormalForm.typeI D.normalForm)
            |>.representationConditions c D.bong b R s hconditionsC hnorm }⟩
  | typeIII D =>
      exact ⟨{
        index_eq := rfl
        lattice := D.target
        lattice_le := D.lattice_le
        volumeOrder_lt := D.volumeOrder_lt c R s
        targetBONG := D.bong
        conditions :=
          (Beli2019Lemma718NormalForm.typeIII D.normalForm)
            |>.representationConditions c D.bong b R s hconditionsC hnorm }⟩
  | typeII D =>
      by_cases hs : 2 < s
      · exact ⟨{
          index_eq := rfl
          lattice := D.target
          lattice_le := D.lattice_le
          volumeOrder_lt := D.volumeOrder_lt c R s hs
          targetBONG := D.bong
          conditions :=
            (Beli2019Lemma718NormalForm.typeII D.normalForm)
              |>.representationConditions c D.bong b R s hconditionsC hnorm }⟩
      · have hsTwo : s = 2 := by
          have hsLower := D.normalForm.stopping.two_le
          omega
        subst s
        have hfirstC : c.order (0 : Fin (n + 3)) = R := by
          exact (horder 0).trans hfirst
        have hsecondC : c.order (1 : Fin (n + 3)) =
            R - 2 * (ramificationIndex K : Int) := by
          exact (horder 1).trans hsecond
        have hthirdC : R + 1 ≤ c.order (2 : Fin (n + 3)) := by
          rcases D.normalForm.typeII.1 with hend | ⟨hbound, habove⟩
          · omega
          · have hindex : (⟨2, hbound⟩ : Fin (n + 3)) =
                (2 : Fin (n + 3)) := by
              apply Fin.ext
              rfl
            have habove' : R < c.order (2 : Fin (n + 3)) := by
              rwa [hindex] at habove
            omega
        have hclass := lemma717_typeII_two_adjacentUnitSquareClass
          c R hfirstC hsecondC D.normalForm.typeII
        have horderSplit : c.order (1 : Fin (n + 3)) ≤
            c.order (2 : Fin (n + 3)) := by
          calc
            c.order (1 : Fin (n + 3)) =
                R - 2 * (ramificationIndex K : Int) := hsecondC
            _ ≤ R + 1 := by
              have he := ramificationIndex_pos (K := K)
              omega
            _ ≤ c.order (2 : Fin (n + 3)) := hthirdC
        rcases c.toBONG.beliCorollary44_i_unconditional c.good
            (1 : Fin (n + 3)) (by simp) horderSplit with ⟨split⟩
        rcases c.exists_lemma714StoppingData R with ⟨t, specialStopping⟩
        have htriggers := c.beli2019Lemma216
          (sourceLaws := alphaV) (targetLaws := alphaV) b le_rfl
          hconditionsC.orderCondition hconditionsC.defectCondition
        have hprime : RepresentationConditionsPrime c b le_rfl :=
          (representationConditions_iff_prime c b le_rfl htriggers).mp
            hconditionsC
        rcases exists_lemma716SpecialUnits (K := K) with
          ⟨ε, η, hεUnit, hηUnit, hεDefect, hηDefect, hhilbert⟩
        let C := c.beli2019Lemma716Special
          (modelAlpha := alphaModel)
          (modelLemma43 := constructionModel)
          (modelSectionTwo := sectionTwoModel)
          (classificationModel := classificationModel)
          (ambientLemma43 := constructionV)
          (ambientSectionTwo := sectionTwoV)
          b R t specialStopping
          hfirstC hsecondC hthirdC split hclass hnorm hprime
            ε η hεUnit hηUnit hεDefect hηDefect hhilbert
        rcases C.sublatticeReduction hconditionsC with ⟨E⟩
        exact ⟨{
          index_eq := E.index_eq
          lattice := E.lattice
          lattice_le := E.lattice_le
          volumeOrder_lt := E.volumeOrder_lt
          targetBONG := E.targetBONG
          conditions := E.conditions }⟩

end Laws

end BONG.GoodBONG

end Bong
