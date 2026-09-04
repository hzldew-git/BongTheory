/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicPublishedRepresentation
import Bong.Bong.He2022ClassicLemma58
import Bong.Bong.HeHu2022Theorem12

/-!
# He (2024), Section 7: the explicit classic testing family

This file fixes the exact bundled meaning of Theorem 1.3 and proves its
necessity half for the literal finite table `C_e^n`.  In particular, the
family contains actual classic integral lattices, rather than condition-only
surrogates, and deletion minimality is stated for literal table entries.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice.QuadraticLatticeModel

/-- Match the two-column He--Hu odd table with the parity/column layout of
the literal classic table. -/
def classicOddIndexOfHeHu {I : Type u} :
    HeHuPublishedOddTestingIndex I -> HeClassicPublishedOddTestingIndex I
  | .inl p => (p, false)
  | .inr p => (p, true)

/-- The exact good-BONG lattice and the canonical maximal lattice have
isometric ambient spaces whenever their displayed diagonal rows do. -/
theorem exactModel_isAmbientlyIsometric_omaximalModel
    {n : Nat} (source target : Fin n -> Kˣ)
    (hadj : BONG.CoefficientAdjacentAdmissible source)
    (hweak : BONG.CoefficientWeakTwoStep (K := K) source)
    (hrep : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients source)
      (BONG.GoodBONG.diagonalUnitCoefficients target)) :
    (heHuExactModel source hadj hweak).IsAmbientlyIsometric
      (heHuOMaximalModel target) := by
  change (BONG.coefficientDiagonalSpace source).IsIsometric
    (BONG.coefficientDiagonalSpace target)
  have hspace :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      source target).2 hrep
  rcases hspace with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEq (by simp)⟩

/-- Convert a representation of a displayed finite diagonal space into
diagonal coordinates on an arbitrary target space. -/
theorem diagonalRepresents_of_represents_coefficientDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (a : Fin n -> Kˣ)
    (h : q.Represents (BONG.coefficientDiagonalSpace a)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients a)
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits) := by
  have hdiag : q.diagonalModel.Represents
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients a)
        (fun i => Units.ne_zero (a i))) := by
    change q.diagonalModel.Represents (BONG.coefficientDiagonalSpace a)
    exact ⟨q.diagonalizationIsometry.toRepresentation.trans
      (Classical.choice h)⟩
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    a q.diagonalUnits).mp hdiag

/-- In equal dimension, one space cannot represent both members of a
nonisometric determinant-class pair. -/
theorem pair_not_both_represents_of_rank_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (first second : Fin n -> Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : Module.finrank K V = n)
    (hfirst : q.Represents (BONG.coefficientDiagonalSpace first))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  let e : Fin n ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  let target : Fin n -> Kˣ := fun i => q.diagonalUnits (e i)
  have hqToTarget : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits)
      (BONG.GoodBONG.diagonalUnitCoefficients target) := by
    have h := BONG.GoodBONG.DiagonalRepresents.reindexEquiv
      (BONG.GoodBONG.diagonalUnitCoefficients target) e.symm
    have hsource :
        (BONG.GoodBONG.diagonalUnitCoefficients target ∘ e.symm) =
          BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits := by
      funext i
      simp only [Function.comp_apply, target,
        BONG.GoodBONG.diagonalUnitCoefficients, Equiv.apply_symm_apply]
    rw [hsource] at h
    exact h
  have hf :=
    (diagonalRepresents_of_represents_coefficientDiagonal first hfirst).trans
      hqToTarget
  have hs :=
    (diagonalRepresents_of_represents_coefficientDiagonal second hsecond).trans
      hqToTarget
  exact pair.nonisometric (hs.trans hf.symm_of_sameRank)

/-- Lemma 3.13 supplies the same exclusion in codimension one. -/
theorem pair_not_both_represents_of_rank_eq_add_one
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {q : QuadraticSpace K V}
    {n : Nat} (first second : Fin n -> Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : Module.finrank K V = n + 1)
    (hfirst : q.Represents (BONG.coefficientDiagonalSpace first))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  let e : Fin (n + 1) ≃ Fin (Module.finrank K V) := finCongr hrank.symm
  let target : Fin (n + 1) -> Kˣ := fun i => q.diagonalUnits (e i)
  have hqToTarget : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits)
      (BONG.GoodBONG.diagonalUnitCoefficients target) := by
    have h := BONG.GoodBONG.DiagonalRepresents.reindexEquiv
      (BONG.GoodBONG.diagonalUnitCoefficients target) e.symm
    have hsource :
        (BONG.GoodBONG.diagonalUnitCoefficients target ∘ e.symm) =
          BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits := by
      funext i
      simp only [Function.comp_apply, target,
        BONG.GoodBONG.diagonalUnitCoefficients, Equiv.apply_symm_apply]
    rw [hsource] at h
    exact h
  have hf :=
    (diagonalRepresents_of_represents_coefficientDiagonal first hfirst).trans
      hqToTarget
  have hs :=
    (diagonalRepresents_of_represents_coefficientDiagonal second hsecond).trans
      hqToTarget
  rcases heHu2022Lemma313CodimensionOne first second pair target with
    hexact | hexact
  · exact hexact.2 hs
  · exact hexact.1 hf

/-- Every odd He--Hu row has the same ambient quadratic space as the
corresponding literal classic row.  This is the space-level bridge used in
Lemma 7.3; it does not identify their generally different lattices. -/
theorem classicOddModel_isAmbientlyIsometric_heHuModel
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (j : HeHuPublishedOddTestingIndex I) :
    IsAmbientlyIsometric
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs (classicOddIndexOfHeHu j))
      (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) j) := by
  have homega : omegaData.omega = heClassicOmega (K := K) := by
    apply Units.ext
    exact omegaData.omega_value.trans (heClassicOmega_value (K := K)).symm
  have homegaSharp : omegaData.omegaSharp =
      heClassicOmegaSharp (K := K) := by
    apply Units.ext
    exact omegaData.omegaSharp_value.trans
      (heClassicOmegaSharp_value (K := K)).symm
  rcases j with p | p
  · rcases p with ⟨i, parity⟩
    cases parity
    · have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs (U i)))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs (U i))) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_unit,
        heClassicOddC1Model] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K)
            (heClassicOddC1 (K := K) pairs (U i))
            (heHuOddFirst pairs (U i))
            (heClassicOddC1_adjacentAdmissible pairs (U i) (by
              exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
                (hU.isUnit i) ▸ le_rfl))
            (heClassicOddC1_weakTwoStep pairs (U i) (by
              exact (isValuationUnit_iff_ordUnit_eq_zero K _).1
                (hU.isUnit i) ▸ le_rfl)) hdiag)
    · let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : ordUnit K c = 1 := by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num
      have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs c))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs c)) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        heClassicOddC1Model, c] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K) (heClassicOddC1 (K := K) pairs c)
            (heHuOddFirst pairs c)
            (heClassicOddC1_adjacentAdmissible pairs c (by omega))
            (heClassicOddC1_weakTwoStep pairs c (by omega)) hdiag)
  · rcases p with ⟨i, parity⟩
    cases parity
    · have hnegative : hilbertSymbol K omegaData.omegaSharp
          omegaData.omega = -1 := by
        rw [homega, homegaSharp]
        exact BONG.GoodBONG.heClassicOmegaSharp_hilbert_neg (K := K)
      have hfirst : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC1 (K := K) pairs (U i)))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddFirst pairs (U i))) := by
        rw [heClassicOddC1_eq_heHuOddFirst]
        exact diagonalRepresents_refl _
      have hdiag := HeHuSpacePairProperties.second_represents_second
        (heClassicOddC_evenOrder_pairProperties (K := K) pairs (U i)
          omegaData.omega omegaData.omegaSharp hnegative)
        (heHu2022Definition34Proposition35Odd pairs (U i)) hfirst
      have hc : ordUnit K (U i) = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_unit,
        heClassicOddC2EvenModel] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K)
            (heClassicOddC2Even (K := K) pairs (U i)
              omegaData.omega omegaData.omegaSharp)
            (heHuOddSecond pairs (U i))
            (heClassicOddC2Even_adjacentAdmissible pairs (U i)
              omegaData.omega omegaData.omegaSharp hc
              omegaData.omega_order omegaData.omegaSharp_order)
            (heClassicOddC2Even_weakTwoStep pairs (U i)
              omegaData.omega omegaData.omegaSharp hc
              omegaData.omega_order omegaData.omegaSharp_order) hdiag)
    · let c := U i * uniformizerPowerUnit K (1 : Int)
      have hc : ordUnit K c = 1 := by
        rw [ordUnit_mul,
          (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
          ordUnit_uniformizerPowerUnit]
        norm_num
      have hodd : Odd (ordUnit K c) := by rw [hc]; exact odd_one
      have hdiag : DiagonalRepresents
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heClassicOddC2Odd (K := K) pairs c))
          (BONG.GoodBONG.diagonalUnitCoefficients
            (heHuOddSecond pairs c)) := by
        rw [heClassicOddC2Odd_eq_heHuOddSecond_of_odd pairs c hodd]
        exact diagonalRepresents_refl _
      simpa only [classicOddIndexOfHeHu,
        HeClassicPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.model,
        HeHuPublishedOddTestingIndex.toGeneral,
        HeHuOddTestingIndex.model, HeHuOddTestingIndex.coefficients,
        HeHuPublishedSquareClassIndex.parameter_uniformizer,
        heClassicOddC2OddModel, c] using
          (exactModel_isAmbientlyIsometric_omaximalModel
            (K := K) (heClassicOddC2Odd (K := K) pairs c)
            (heHuOddSecond pairs c)
            (heClassicOddC2Odd_adjacentAdmissible pairs c (by omega))
            (heClassicOddC2Odd_weakTwoStep pairs c (by omega)) hdiag)

/-- Classic `n`-universality of a bundled local quadratic lattice. -/
def IsClassicNUniversal (X : QuadraticLatticeModel (K := K))
    (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  exact Lattice.IsClassicNUniversal.{u, u, u} X.form X.lattice n

/-- Ambient rank-`n` universality of a bundled local quadratic lattice. -/
def IsAmbientlyNUniversal (X : QuadraticLatticeModel (K := K))
    (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.AmbientlyNUniversal.{u, u, u} X.form n

/-- A finite family tests classic rank-`n` universality.  The source is
required to be classic integral, exactly as in Theorem 1.3. -/
def IsClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  forall X : QuadraticLatticeModel (K := K),
    X.IsClassicIntegral -> (forall i, X.Represents (family i)) ->
      X.IsClassicNUniversal n

/-- Literal deletion minimality for a classic testing family.  Distinct
indices are retained because Theorem 1.3 counts and deletes the displayed
lattices themselves. -/
def IsLiteralMinimalClassicUniversalityTestingFamily {I : Type u}
    (family : I -> QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  IsClassicUniversalityTestingFamily family n ∧
    forall i, exists X : QuadraticLatticeModel (K := K),
      X.IsClassicIntegral ∧ ¬ X.Represents (family i) ∧
        forall j, j ≠ i -> X.Represents (family j)

/-- Necessity in Lemma 7.4 for every even entry of the printed table. -/
theorem classicUniversal_represents_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2))
    (i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K)) :
    X.Represents
      (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) := by
  let T := HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedEvenTestingIndex.model_rank U hU pairs i)
    (HeClassicPublishedEvenTestingIndex.model_isClassicIntegral U hU pairs i)

/-- Necessity in Lemma 7.4 for every odd entry of the printed table. -/
theorem classicUniversal_represents_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3))
    (i : HeClassicPublishedOddTestingIndex I) :
    X.Represents
      (HeClassicPublishedOddTestingIndex.model
        (K := K) U hU omegaData pairs i) := by
  let T := HeClassicPublishedOddTestingIndex.model
    (K := K) U hU omegaData pairs i
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  exact hX.2 T.form T.lattice
    (HeClassicPublishedOddTestingIndex.model_rank U hU omegaData pairs i)
    (HeClassicPublishedOddTestingIndex.model_isClassicIntegral
      U hU omegaData pairs i)

/-- The necessity direction of Lemma 7.4, even rank. -/
theorem classicUniversal_implies_all_publishedEven
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 2)) :
    forall i : HeClassicPublishedEvenTestingIndex (K := K) U
      (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model (K := K) U hU pairs i) :=
  fun i => classicUniversal_represents_publishedEven U hU pairs X hX i

/-- The necessity direction of Lemma 7.4, odd rank. -/
theorem classicUniversal_implies_all_publishedOdd
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K))
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hX : X.IsClassicNUniversal (2 * pairs + 3)) :
    forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i) :=
  fun i => classicUniversal_represents_publishedOdd
    U hU omegaData pairs X hX i

/-- Lemma 7.3, odd-rank branch.  The literal classic table exhausts all
ambient quadratic spaces because each row has the same space as its He--Hu
maximal representative and the latter family is already classified. -/
theorem all_publishedOdd_implies_ambientlyUniversal
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (omegaData : HeClassicOmegaData (K := K)) (pairs : Nat)
    (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedOddTestingIndex I,
      X.Represents
        (HeClassicPublishedOddTestingIndex.model
          (K := K) U hU omegaData pairs i)) :
    X.IsAmbientlyNUniversal (2 * pairs + 3) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  change Lattice.AmbientlyNUniversal.{u, u, u} X.form (2 * pairs + 3)
  intro W _instWGroup _instWModule r M hRank _hIntegral
  let Y := Lattice.quadraticLatticeModel r M
  have hYRank : Y.rank = 2 * pairs + 3 := by
    change Module.finrank K W = 2 * pairs + 3
    exact hRank
  obtain ⟨j, hYj⟩ :=
    exists_publishedOddIndex_for_model U hU pairs Y hYRank
  let i := classicOddIndexOfHeHu j
  let C := HeClassicPublishedOddTestingIndex.model
    (K := K) U hU omegaData pairs i
  let H := HeHuPublishedOddTestingIndex.model
    (K := K) (U := U) (pairs := pairs) j
  have hXC : X.Represents C := by
    simpa only [C, i] using hAll i
  have hCH : C.IsAmbientlyIsometric H := by
    simpa only [C, H, i] using
      classicOddModel_isAmbientlyIsometric_heHuModel
        U hU omegaData pairs j
  have hYH : Y.IsAmbientlyIsometric H := by
    simpa only [H] using hYj
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup H.Carrier := H.addCommGroup
  letI : Module K H.Carrier := H.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  rcases hCH with ⟨fCH⟩
  rcases hYH with ⟨fYH⟩
  exact hXC.ambient.trans
    ⟨fCH.symm.toRepresentation.trans fYH.toRepresentation⟩

/-- The two defect-one `C` rows already force an even-rank source to have
at least two extra variables.  Equal rank is excluded by nonisometry and
codimension one by He--Hu Lemma 3.13. -/
theorem all_publishedEven_implies_rank_add_two_le
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    2 * pairs + 4 <= X.rank := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  have homegaUnit : IsValuationUnit K ((heClassicOmega (K := K) : K)) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2
      (heClassicOmega_order (K := K))
  obtain ⟨i, s, _hsUnit, hfactor⟩ :=
    hU.complete (heClassicOmega (K := K)) homegaUnit
  have hdefect : BONG.GoodBONG.defectOrder (K := K) (U i) =
      (1 : WithTop ℚ) := by
    have h := heClassicOmega_defect (K := K)
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at h
    exact h
  let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hdefect⟩
  let iFirst : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
  let iSecond : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, true))
  let CFirst := HeClassicPublishedEvenTestingIndex.model
    (K := K) U hU pairs iFirst
  let CSecond := HeClassicPublishedEvenTestingIndex.model
    (K := K) U hU pairs iSecond
  have hXFirst : X.Represents CFirst := by
    simpa only [CFirst] using hAll iFirst
  have hXSecond : X.Represents CSecond := by
    simpa only [CSecond] using hAll iSecond
  dsimp [CFirst, iFirst, di,
    HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenC1Model, heHuExactModel] at hXFirst
  dsimp [CSecond, iSecond, di,
    HeClassicPublishedEvenTestingIndex.model,
    heClassicEvenC2Model, heHuExactModel] at hXSecond
  have hFirst : X.form.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs (U i))) := by
    exact hXFirst.ambient
  have hSecond : X.form.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC2 (K := K) pairs (U i)
          (heClassicDefectOneSharp (K := K) (U i) hdefect))) := by
    simpa only using hXSecond.ambient
  have hRankLower : 2 * pairs + 2 <= Module.finrank K X.Carrier := by
    rcases hFirst with ⟨f⟩
    have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
    simpa using hle
  by_contra hnot
  have hRankCases : Module.finrank K X.Carrier = 2 * pairs + 2 ∨
      Module.finrank K X.Carrier = 2 * pairs + 3 := by
    have hRankDef : X.rank = Module.finrank K X.Carrier := by rfl
    rw [hRankDef] at hnot
    omega
  have pair := BONG.GoodBONG.heClassicEvenC_pairProperties
    (K := K) pairs (U i) hdefect
  rcases hRankCases with hEq | hEq
  · exact pair_not_both_represents_of_rank_eq
      (heClassicEvenC1 (K := K) pairs (U i))
      (heClassicEvenC2 (K := K) pairs (U i)
        (heClassicDefectOneSharp (K := K) (U i) hdefect))
      pair hEq hFirst hSecond
  · exact pair_not_both_represents_of_rank_eq_add_one
      (heClassicEvenC1 (K := K) pairs (U i))
      (heClassicEvenC2 (K := K) pairs (U i)
        (heClassicDefectOneSharp (K := K) (U i) hdefect))
      pair hEq hFirst hSecond

end Lattice.QuadraticLatticeModel

end Bong
