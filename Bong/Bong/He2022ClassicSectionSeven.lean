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

/-- Integral isometry of bundled quadratic lattices. -/
def IsIntegrallyIsometric (X Y : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.IsIsometric X.form Y.form X.lattice Y.lattice

/-- The diagonal change of basis between square-equivalent even `C₁`
rows is trivial except at the final coefficient. -/
def heClassicEvenC1SquareScale (pairs : Nat) (s : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ := fun i =>
  if i.val = 2 * pairs + 1 then s else 1

theorem heClassicEvenC1_coefficients_mul_square
    (pairs : Nat) (c d s : Kˣ) (h : c = d * s ^ 2) (i : Fin (2 * pairs + 2)) :
    heClassicEvenC1 (K := K) pairs c i =
      heClassicEvenC1 (K := K) pairs d i *
        heClassicEvenC1SquareScale pairs s i ^ 2 := by
  by_cases hlast : i.val = 2 * pairs + 1
  · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 2) := by
      apply Fin.ext
      simpa using hlast
    rw [hi, heClassicEvenC1_tail, heClassicEvenC1_tail]
    simp [heClassicEvenC1SquareScale, h]
  · by_cases hhead : i.val < 2 * pairs
    · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
      have hi : i = Fin.castAdd 2 j := Fin.ext rfl
      rw [hi, heClassicEvenC1_head, heClassicEvenC1_head]
      have hjNotLast : j.val ≠ 2 * pairs + 1 := by omega
      simp [heClassicEvenC1SquareScale, hjNotLast]
    · have hmiddle : i.val = 2 * pairs := by omega
      have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 2) := by
        apply Fin.ext
        simpa using hmiddle
      rw [hi, heClassicEvenC1_tail, heClassicEvenC1_tail]
      simp [heClassicEvenC1SquareScale]

/-- Square-equivalent unit parameters give isometric literal `C₁` lattices,
not merely isometric ambient spaces. -/
theorem heClassicEvenC1Model_isIsometric_of_mul_square
    (pairs : Nat) (c d s : Kˣ)
    (hc : ordUnit K c = 0) (hd : ordUnit K d = 0)
    (hsUnit : IsValuationUnit K (s : K))
    (h : c = d * s ^ 2) :
    (heClassicEvenC1Model (K := K) pairs c (by omega)).IsIntegrallyIsometric
      (heClassicEvenC1Model (K := K) pairs d (by omega)) := by
  let source := heClassicEvenC1 (K := K) pairs c
  let target := heClassicEvenC1 (K := K) pairs d
  let scale := heClassicEvenC1SquareScale pairs s
  have hsourceMono : ∀ i j, i ≤ j →
      ordUnit K (source i) ≤ ordUnit K (source j) := by
    intro i j _hij
    rw [show ordUnit K (source i) = 0 by
      simp only [source, heClassicEvenC1_order, hc]
      split <;> rfl,
      show ordUnit K (source j) = 0 by
        simp only [source, heClassicEvenC1_order, hc]
        split <;> rfl]
  have htargetMono : ∀ i j, i ≤ j →
      ordUnit K (target i) ≤ ordUnit K (target j) := by
    intro i j _hij
    rw [show ordUnit K (target i) = 0 by
      simp only [target, heClassicEvenC1_order, hd]
      split <;> rfl,
      show ordUnit K (target j) = 0 by
        simp only [target, heClassicEvenC1_order, hd]
        split <;> rfl]
  have hscaleUnit : ∀ i, IsValuationUnit K (scale i : K) := by
    intro i
    unfold scale heClassicEvenC1SquareScale
    split
    · exact hsUnit
    · simp [IsValuationUnit]
  have hcoeff : ∀ i, source i = target i * scale i ^ 2 := by
    intro i
    exact heClassicEvenC1_coefficients_mul_square pairs c d s h i
  unfold IsIntegrallyIsometric
  change Lattice.IsIsometric
    (BONG.coefficientDiagonalSpace source)
    (BONG.coefficientDiagonalSpace target)
    (heHuExactRealization source
      (heClassicEvenC1_adjacentAdmissible pairs c (by omega))
      (heClassicEvenC1_weakTwoStep pairs c (by omega))).lattice
    (heHuExactRealization target
      (heClassicEvenC1_adjacentAdmissible pairs d (by omega))
      (heClassicEvenC1_weakTwoStep pairs d (by omega))).lattice
  exact heHuExactModel_isIsometric_of_pointwise_unit_square
    source target scale
    (heClassicEvenC1_adjacentAdmissible pairs c (by omega))
    (heClassicEvenC1_weakTwoStep pairs c (by omega))
    (heClassicEvenC1_adjacentAdmissible pairs d (by omega))
    (heClassicEvenC1_weakTwoStep pairs d (by omega))
    hsourceMono htargetMono hscaleUnit hcoeff

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

/-- Express an ambient representation in the orthogonal coordinates of a
chosen good BONG.  This keeps the determinant calculation in the same BONG
coordinates used by Lemma 4.4. -/
theorem diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {m n : Nat} (a : BONG.GoodBONG q L n) (source : Fin m -> Kˣ)
    (h : q.Represents (BONG.coefficientDiagonalSpace source)) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients source)
      (BONG.GoodBONG.diagonalUnitCoefficients a.valueUnit) := by
  rcases h with ⟨f⟩
  let g : (Fin m -> K) →ₗ[K] (Fin n -> K) :=
    a.toBONG.basis.equivFun.toLinearMap.comp f.toLinearMap
  refine ⟨g, a.toBONG.basis.equivFun.injective.comp f.injective, ?_⟩
  intro x
  change diagonalQuadratic (fun i => (a.valueUnit i : K)) (g x) =
    diagonalQuadratic (fun i => (source i : K)) x
  change diagonalQuadratic a.toBONG.value (g x) =
    diagonalQuadratic (fun i => (source i : K)) x
  rw [a.toBONG.diagonalQuadratic_value_eq]
  simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  simpa only [BONG.coefficientDiagonalSpace,
    QuadraticSpace.finiteDiagonal_quadratic_apply] using f.map_quadratic x

/-- For an odd-order determinant parameter, the literal discriminant-unit
second column is the other member of the common determinant square class. -/
theorem heClassicEvenC_oddOrder_literalPairProperties
    [HilbertSymbolLaws K] [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (c : Kˣ) (hodd : Odd (ordUnit K c)) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit) := by
  let delta :=
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
  have hnegative : hilbertSymbol K delta c = -1 := by
    simpa only [delta] using
      (hilbertSymbol_discriminant_eq_neg_one_of_odd_order c hodd)
  have hclassification :=
    heHuBinaryTwist_classification c delta hnegative
  have hbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinaryTwist c delta) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact hclassification.1
    · exact hclassification.2.1
  have hpair := hbinary.append
    (AlternatingEndpointTower.standardHyperbolicEndpointTower
      (K := K) pairs)
  simpa only [delta, heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinaryTwist] using hpair

/-- The determinant calculation at the heart of the even branch of Lemma
7.3.  If the signed determinant of a rank-`n+2` good BONG is square
equivalent to the parameter of a published `C₁/C₂` pair, that pair
cannot both be represented by the ambient source space. -/
theorem heClassicEvenPair_not_both_goodBONG_of_signedPrefix_factor
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (pairs : Nat) (a : BONG.GoodBONG q L (2 * pairs + 4))
    (c s : Kˣ) (second : Fin (2 * pairs + 2) -> Kˣ)
    (pair : HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c) second)
    (hcNonnegative : 0 <= ordUnit K c)
    (hfactor : ((-1 : Kˣ) ^ (pairs + 2)) *
      a.prefixProduct (2 * pairs + 4) = c * s ^ 2)
    (hfirst : q.Represents
      (BONG.coefficientDiagonalSpace
        (heClassicEvenC1 (K := K) pairs c)))
    (hsecond : q.Represents (BONG.coefficientDiagonalSpace second)) : False := by
  have hFirstDiagonal :=
    diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
      a (heClassicEvenC1 (K := K) pairs c) hfirst
  have hSecondDiagonal :=
    diagonalRepresents_goodBONG_of_represents_coefficientDiagonal
      a second hsecond
  let bFirst := heClassicEvenC1GoodBONG (K := K) pairs c hcNonnegative
  have hFirstDet :
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
        (-1 : Kˣ) ^ (pairs + 1) * c := by
    calc
      BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c) =
          BONG.GoodBONG.diagonalUnitDeterminant
            (bFirst.prefixValueUnits (2 * pairs + 2) le_rfl) := by
        rw [BONG.GoodBONG.heClassicEvenC1_fullPrefixValueUnits
          pairs c hcNonnegative]
      _ = bFirst.prefixProduct (2 * pairs + 2) :=
        bFirst.diagonalUnitDeterminant_prefixValueUnits
          (2 * pairs + 2) le_rfl
      _ = (-1 : Kˣ) ^ (pairs + 1) * c :=
        BONG.GoodBONG.heClassicEvenC1_prefixProduct_full
          (K := K) pairs c hcNonnegative
  have hTargetDet :
      BONG.GoodBONG.diagonalUnitDeterminant a.valueUnit =
        a.prefixProduct (2 * pairs + 4) := by
    have hvalues : a.prefixValueUnits (2 * pairs + 4) le_rfl =
        a.valueUnit := by
      funext i
      rfl
    rw [← hvalues]
    exact a.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 4) le_rfl
  have hSquare : IsSquare
      (((( (-1 : Kˣ) ^ (pairs + 2)) *
          a.prefixProduct (2 * pairs + 4)) * c)) := by
    refine ⟨c * s, ?_⟩
    rw [hfactor]
    simp only [pow_two]
    ac_rfl
  have hdet : IsSquare
      (-BONG.GoodBONG.diagonalUnitDeterminant a.valueUnit *
        BONG.GoodBONG.diagonalUnitDeterminant
          (heClassicEvenC1 (K := K) pairs c)) := by
    rw [hTargetDet, hFirstDet]
    have hsign :
        -a.prefixProduct (2 * pairs + 4) *
            ((-1 : Kˣ) ^ (pairs + 1) * c) =
          (((-1 : Kˣ) ^ (pairs + 2)) *
            a.prefixProduct (2 * pairs + 4)) * c := by
      have hneg : -a.prefixProduct (2 * pairs + 4) =
          (-1 : Kˣ) * a.prefixProduct (2 * pairs + 4) := by
        simp
      rw [hneg,
        show (-1 : Kˣ) ^ (pairs + 2) =
          (-1 : Kˣ) ^ (pairs + 1) * (-1 : Kˣ) by
            rw [show pairs + 2 = (pairs + 1) + 1 by omega, pow_succ]]
      ac_rfl
    rw [hsign]
    exact hSquare
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heClassicEvenC1 (K := K) pairs c) second pair a.valueUnit (by
      simpa only [show (2 * pairs + 2) + 2 = 2 * pairs + 4 by omega]
        using hdet)
  rcases hExactlyOne with hFirst | hSecond
  · exact hFirst.2 hSecondDiagonal
  · exact hSecond.1 hFirstDiagonal

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

/-- The finite even table contains the literal exceptional row
`H_e^(2p+2)(1)`. -/
theorem represents_literalEvenHOne_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    X.Represents
      (heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl)
        (by
          have h := ordUnit_mul K (1 : Kˣ) 1
          simp only [mul_one] at h
          omega)) := by
  let i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) :=
    .inl ⟨false, Or.inl rfl⟩
  simpa [i, HeClassicPublishedEvenTestingIndex.model,
    HeClassicExceptionalIndex.parameter] using hAll i

/-- When `e=1`, the finite even table also contains the literal
`H_1^(2p+2)(Delta)` row. -/
theorem represents_literalEvenHDelta_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (heOne : ramificationIndex K = 1)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    X.Represents
      (heClassicEvenHModel (K := K) pairs delta
        (Or.inr (show delta =
          (Dyadic.dyadicDiscriminantClassLawsProved
            (K := K)).discriminantUnit
          from rfl))
        deltaOrder) := by
  let delta :=
    (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
  let deltaOrder : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminant_isValuationUnit
  let i : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) :=
    .inl ⟨true, Or.inr heOne⟩
  simpa [i, delta, deltaOrder,
    HeClassicPublishedEvenTestingIndex.model,
    HeClassicExceptionalIndex.parameter] using hAll i

/-- Completeness of the unit square-class representatives and the integral
unit-square transport above recover the literal `C₁(omega)` row from the
finite even table. -/
theorem represents_literalEvenC1Omega_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    X.Represents
      (heClassicEvenC1Model (K := K) pairs
        (heClassicOmega (K := K)) (by
          rw [heClassicOmega_order (K := K)])) := by
  have homegaUnit : IsValuationUnit K ((heClassicOmega (K := K) : K)) :=
    (isValuationUnit_iff_ordUnit_eq_zero K _).2
      (heClassicOmega_order (K := K))
  obtain ⟨i, s, hsUnit, hfactor⟩ :=
    hU.complete (heClassicOmega (K := K)) homegaUnit
  have hdefect : BONG.GoodBONG.defectOrder (K := K) (U i) =
      (1 : WithTop ℚ) := by
    have h := heClassicOmega_defect (K := K)
    rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at h
    exact h
  let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hdefect⟩
  let idx : HeClassicPublishedEvenTestingIndex
      (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
  let C := heClassicEvenC1Model (K := K) pairs
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)])
  let D := heClassicEvenC1Model (K := K) pairs (U i) (by
    exact (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i) ▸ le_rfl)
  have hXD : X.Represents D := by
    simpa [D, idx, di, HeClassicPublishedEvenTestingIndex.model] using hAll idx
  have hCD : C.IsIntegrallyIsometric D := by
    simpa [C, D] using
      (heClassicEvenC1Model_isIsometric_of_mul_square
        (K := K) pairs (heClassicOmega (K := K)) (U i) s
        (heClassicOmega_order (K := K))
        ((isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i))
        hsUnit hfactor)
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup D.Carrier := D.addCommGroup
  letI : Module K D.Carrier := D.module
  change Lattice.Represents X.form C.form X.lattice C.lattice
  change Lattice.Represents X.form D.form X.lattice D.lattice at hXD
  change Lattice.IsIsometric C.form D.form C.lattice D.lattice at hCD
  rcases hXD with ⟨f⟩
  rcases hCD with ⟨g⟩
  exact ⟨f.trans g.toRepresentation⟩

/-- Actual representation of the finite even table supplies the two literal
condition-level tests used in Lemma 4.2. -/
theorem literalLemma42Tests_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice ((2 * pairs + 1) + 3))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
      letI : Module K X.Carrier := X.module (K := K)
      exact a.HeClassicLemma42PublishedTests pairs (by omega)) := by
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let omega := heClassicOmega (K := K)
  let omegaOrder : ordUnit K omega = 0 := heClassicOmega_order (K := K)
  let C := heClassicEvenC1Model (K := K) pairs omega (by omega)
  let H := heClassicEvenHModel (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hXC : X.Represents C := by
    simpa only [C, omega, omegaOrder] using
      represents_literalEvenC1Omega_of_all U hU pairs X hAll
  have hXH : X.Represents H := by
    simpa only [H, oneOrder] using
      represents_literalEvenHOne_of_all U hU pairs X hAll
  letI : AddCommGroup X.Carrier := X.addCommGroup (K := K)
  letI : Module K X.Carrier := X.module (K := K)
  letI : AddCommGroup C.Carrier := C.addCommGroup
  letI : Module K C.Carrier := C.module
  letI : AddCommGroup H.Carrier := H.addCommGroup
  letI : Module K H.Carrier := H.module
  let bC := heClassicEvenC1GoodBONG (K := K) pairs omega (by omega)
  let bH := heClassicEvenHGoodBONG (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hrepC : Lattice.Represents X.form C.form X.lattice C.lattice := by
    exact hXC
  have hrepH : Lattice.Represents X.form H.form X.lattice H.lattice := by
    exact hXH
  have hconditionsC := a.representationConditionsPrime_of_represents
    bC (by omega) hrepC
  have hconditionsH := a.representationConditionsPrime_of_represents
    bH (by omega) hrepH
  unfold BONG.GoodBONG.HeClassicLemma42PublishedTests
  dsimp only
  exact ⟨⟨hconditionsC.orderCondition, hconditionsC.defectCondition⟩,
    ⟨hconditionsH.orderCondition, hconditionsH.defectCondition⟩⟩

/-- In the only unstable rank, namely source rank `n+2`, the actual finite
table forces the signed full-prefix bound used by Lemma 4.4.  For `e>1`
this is `J₂'_E`; for `e=1` the proof uses exactly the two exceptional
`H(1)` and `H(Delta)` rows occurring in Lemma 4.3(i). -/
theorem fullRank_signedPrefix_upper_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (a : @BONG.GoodBONG K _ _ _ _ _ X.Carrier X.addCommGroup X.module
      X.form X.lattice ((2 * pairs + 1) + 3))
    (hXClassic : X.IsClassicIntegral)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact
        (((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
              (2 * pairs + 4) <= 1) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  have hClassic : Lattice.IsClassicIntegral X.form X.lattice := by
    exact hXClassic
  have hTests := literalLemma42Tests_of_all U hU pairs X a hAll
  have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests pairs
    (by omega) hClassic hTests
  by_cases heLarge : 1 < ramificationIndex K
  · have hJ2 := a.he2022ClassicLemma42_j2Prime_of_publishedTests pairs
      (by omega) hClassic hTests
    have hbound := hJ2 heLarge
    simpa only [show (2 * pairs + 2 + 2) / 2 = pairs + 2 by omega,
      show 2 * pairs + 2 + 1 = 2 * pairs + 3 by omega,
      show 2 * pairs + 2 + 2 = 2 * pairs + 4 by omega] using hbound
  · have hePositive : 0 < ramificationIndex K :=
      ramificationIndex_pos (K := K)
    have heOne : ramificationIndex K = 1 := by omega
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    let delta := (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    let HOne := heClassicEvenHModel (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let HDelta := heClassicEvenHModel (K := K) pairs delta
      (Or.inr (show delta =
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit from rfl)) deltaOrder
    have hXOne : X.Represents HOne := by
      simpa only [HOne, oneOrder] using
        represents_literalEvenHOne_of_all U hU pairs X hAll
    have hXDelta : X.Represents HDelta := by
      simpa only [HDelta, delta, deltaOrder] using
        represents_literalEvenHDelta_of_all U hU pairs X heOne hAll
    letI : AddCommGroup HOne.Carrier := HOne.addCommGroup
    letI : Module K HOne.Carrier := HOne.module
    letI : AddCommGroup HDelta.Carrier := HDelta.addCommGroup
    letI : Module K HDelta.Carrier := HDelta.module
    let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
      (Or.inr (show delta =
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminantUnit from rfl)) deltaOrder
    have hrepOne : Lattice.Represents X.form HOne.form
        X.lattice HOne.lattice := hXOne
    have hrepDelta : Lattice.Represents X.form HDelta.form
        X.lattice HDelta.lattice := hXDelta
    have hOneConditions := a.representationConditionsPrime_of_represents
      bOne (by omega) hrepOne
    have hDeltaConditions := a.representationConditionsPrime_of_represents
      bDelta (by omega) hrepDelta
    have hOneCentral := hOneConditions.centralRepresentations
    have hDeltaCentral := hDeltaConditions.centralRepresentations
    let D : WithTop ℚ :=
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)
    let R : Int := a.order ⟨2 * pairs + 3, by omega⟩
    let raw : WithTop ℚ := BONG.GoodBONG.defectOrder (K := K)
      (((-1 : Kˣ) ^ (pairs + 2)) * a.prefixProduct (2 * pairs + 4))
    let twoE : WithTop ℚ :=
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    have hSource : 2 * pairs + 4 <= (2 * pairs + 1) + 3 := by omega
    by_contra hupper
    have hsum : (1 : WithTop ℚ) <
        (((R : Int) : ℚ) : WithTop ℚ) + D := by
      exact lt_of_not_ge (by simpa only [R, D] using hupper)
    by_cases hRawLt : raw < twoE
    · have hfailure := a.he2022ClassicLemma43i pairs hSource
          hJ1 heOne (by simpa only [R, D] using hsum)
          (Or.inl (by simpa only [raw, twoE] using hRawLt))
      dsimp only at hfailure
      let i : CentralRepresentationIndex
          ((2 * pairs + 1) + 3) (2 * pairs + 2) :=
        BONG.GoodBONG.he2022ClassicLemma43Index pairs hSource
      rcases hfailure with hOneFails | hDeltaFails
      · exact hOneFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
            hOneCentral i)
      · exact hDeltaFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
            hDeltaCentral i)
    · have hRawGe : twoE <= raw := le_of_not_gt hRawLt
      by_cases hTwoELeD : twoE <= D
      · have hfailure := a.he2022ClassicLemma43i pairs hSource
            hJ1 heOne (by simpa only [R, D] using hsum)
            (Or.inr (by simpa only [D, twoE] using hTwoELeD))
        dsimp only at hfailure
        let i : CentralRepresentationIndex
            ((2 * pairs + 1) + 3) (2 * pairs + 2) :=
          BONG.GoodBONG.he2022ClassicLemma43Index pairs hSource
        rcases hfailure with hOneFails | hDeltaFails
        · exact hOneFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
              hOneCentral i)
        · exact hDeltaFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
              hDeltaCentral i)
      · have hDLtTwoE : D < twoE := lt_of_not_ge hTwoELeD
        have hDraw : D = raw := by
          dsimp only [D, raw]
          unfold BONG.GoodBONG.truncatedPrefixDefect
          have hlast : 2 * pairs + 4 = (2 * pairs + 1) + 3 := by omega
          have hcapLast : a.prefixAlphaCap (2 * pairs + 4) = ⊤ := by
            rw [hlast]
            exact a.prefixAlphaCap_last
          rw [a.prefixAlphaCap_zero, hcapLast]
          simp [BONG.GoodBONG.prefixProduct]
        rw [hDraw] at hDLtTwoE
        exact (not_lt_of_ge hRawGe) hDLtTwoE

/-- A signed determinant parameter with the two low-order and low-defect
possibilities singled out by Lemma 4.4 is square-equivalent to one of the
literal pairs in the finite even table, and both members of that pair are
represented by the source. -/
theorem exists_represented_publishedEven_pair_of_low_signed_parameter
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i))
    (c0 : Kˣ)
    (hOrder : ordUnit K c0 = 0 ∨ ordUnit K c0 = 1)
    (hDefect : BONG.GoodBONG.defectOrder (K := K) c0 = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c0 = 1) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact ∃ (c s : Kˣ) (second : Fin (2 * pairs + 2) -> Kˣ),
        HeHuSpacePairProperties
            (heClassicEvenC1 (K := K) pairs c) second ∧
          0 <= ordUnit K c ∧ c0 = c * s ^ 2 ∧
          X.form.Represents
            (BONG.coefficientDiagonalSpace
              (heClassicEvenC1 (K := K) pairs c)) ∧
          X.form.Represents (BONG.coefficientDiagonalSpace second)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  rcases hOrder with hOrderZero | hOrderOne
  · have hc0Unit : IsValuationUnit K (c0 : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K c0).2 hOrderZero
    have hc0Even : Even (ordUnit K c0) := by
      rw [hOrderZero]
      exact Even.zero
    have hDefectOne : BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
      rcases hDefect with hzero | hone
      · have hlower := BONG.GoodBONG.defectOrder_one_le_of_even
          c0 hc0Even
        rw [hzero] at hlower
        exact (not_le_of_gt (show (0 : WithTop ℚ) < 1 by norm_num)
          hlower).elim
      · exact hone
    obtain ⟨i, s, _hsUnit, hfactor⟩ := hU.complete c0 hc0Unit
    have hUiDefect : BONG.GoodBONG.defectOrder (K := K) (U i) = 1 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hDefectOne
      exact hDefectOne
    let di : HeClassicDefectOneIndex (K := K) U := ⟨i, hUiDefect⟩
    let iFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, false))
    let iSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inl (di, true))
    have hXFirst := hAll iFirst
    have hXSecond := hAll iSecond
    dsimp [iFirst, di,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC1Model, heHuExactModel] at hXFirst
    dsimp [iSecond, di,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC2Model, heHuExactModel] at hXSecond
    let cSharp := heClassicDefectOneSharp (K := K) (U i) hUiDefect
    refine ⟨U i, s,
      heClassicEvenC2 (K := K) pairs (U i) cSharp, ?_, ?_,
      hfactor, ?_, ?_⟩
    · simpa only [cSharp] using
        (BONG.GoodBONG.heClassicEvenC_pairProperties
          (K := K) pairs (U i) hUiDefect)
    · rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i)]
    · exact hXFirst.ambient
    · simpa only [cSharp] using hXSecond.ambient
  · have hc0Odd : Odd (ordUnit K c0) := by
      rw [hOrderOne]
      exact odd_one
    have hDefectZero : BONG.GoodBONG.defectOrder (K := K) c0 = 0 := by
      unfold BONG.GoodBONG.defectOrder
      rw [quadraticDefect_eq_zero_of_odd_ordUnit c0 hc0Odd]
      rfl
    let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
    let unitPart : Kˣ := c0 / pi
    have hUnitPartOrder : ordUnit K unitPart = 0 := by
      dsimp only [unitPart, pi]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_uniformizerPowerUnit, hOrderOne]
      norm_num
    have hUnitPart : IsValuationUnit K (unitPart : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K unitPart).2 hUnitPartOrder
    obtain ⟨i, s, _hsUnit, hunitFactor⟩ :=
      hU.complete unitPart hUnitPart
    let c : Kˣ := U i * pi
    have hcOrder : ordUnit K c = 1 := by
      dsimp only [c, pi]
      rw [ordUnit_mul,
        (isValuationUnit_iff_ordUnit_eq_zero K _).1 (hU.isUnit i),
        ordUnit_uniformizerPowerUnit]
      norm_num
    have hcOdd : Odd (ordUnit K c) := by
      rw [hcOrder]
      exact odd_one
    have hfactor : c0 = c * s ^ 2 := by
      calc
        c0 = unitPart * pi := by simp [unitPart]
        _ = (U i * s ^ 2) * pi := by rw [hunitFactor]
        _ = c * s ^ 2 := by
          dsimp only [c]
          ac_rfl
    have hcDefect : BONG.GoodBONG.defectOrder (K := K) c = 0 := by
      rw [hfactor, BONG.GoodBONG.defectOrder_mul_square] at hDefectZero
      exact hDefectZero
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let iFirst : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, false))
    let iSecond : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K) := .inr (.inr (i, true))
    have hXFirst := hAll iFirst
    have hXSecond := hAll iSecond
    dsimp [iFirst, c, pi,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC1Model, heHuExactModel] at hXFirst
    dsimp [iSecond, c, pi, delta,
      HeClassicPublishedEvenTestingIndex.model,
      heClassicEvenC2Model, heHuExactModel] at hXSecond
    refine ⟨c, s, heClassicEvenC2 (K := K) pairs c delta,
      ?_, by omega, hfactor, ?_, ?_⟩
    · simpa only [delta] using
        (heClassicEvenC_oddOrder_literalPairProperties
          (K := K) pairs c hcOdd)
    · simpa only [c, pi] using hXFirst.ambient
    · simpa only [c, pi, delta] using hXSecond.ambient

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

/-- Lemma 7.3, even-rank branch.  The only rank not covered directly by
high-rank isotropy is `n+2`.  Lemma 4.4 puts its signed determinant in one
of the two low-defect rows of the literal finite table, while Lemma 3.13
says that the corresponding two columns cannot both occur. -/
theorem all_publishedEven_implies_ambientlyUniversal
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {I : Type u} [Fintype I] (U : I -> Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hXClassic : X.IsClassicIntegral)
    (hAll : forall i : HeClassicPublishedEvenTestingIndex
        (K := K) U (ramificationIndex K),
      X.Represents
        (HeClassicPublishedEvenTestingIndex.model
          (K := K) U hU pairs i)) :
    (by
      letI : AddCommGroup X.Carrier := X.addCommGroup
      letI : Module K X.Carrier := X.module
      exact Lattice.AmbientlyNUniversal.{u, u, u}
        X.form (2 * pairs + 2)) := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  change Lattice.AmbientlyNUniversal.{u, u, u}
    X.form (2 * pairs + 2)
  by_cases hLarge : 2 * pairs + 5 <= Module.finrank K X.Carrier
  · exact Lattice.ambientlyNUniversal_of_rank_add_three_le.{u, u, u}
      (q := X.form) (2 * pairs + 2) (by simpa only [show
        2 * pairs + 2 + 3 = 2 * pairs + 5 by omega] using hLarge)
  · have hRankLower : 2 * pairs + 4 <= Module.finrank K X.Carrier := by
      have h := all_publishedEven_implies_rank_add_two_le
        (K := K) U hU pairs X hAll
      change 2 * pairs + 4 <= Module.finrank K X.Carrier at h
      exact h
    have hRankEq : Module.finrank K X.Carrier =
        2 * pairs + 4 := by omega
    obtain ⟨aRaw⟩ := exists_good_bong X.form X.lattice
    let a : BONG.GoodBONG X.form X.lattice (2 * pairs + 4) :=
      aRaw.castLength hRankEq
    have hClassic : Lattice.IsClassicIntegral X.form X.lattice :=
      hXClassic
    have hBound := fullRank_signedPrefix_upper_of_all
      U hU pairs X a hXClassic hAll
    have hTests := literalLemma42Tests_of_all U hU pairs X a hAll
    have hJ1 := a.he2022ClassicLemma42_j1Prime_of_publishedTests
      pairs (by omega) hClassic hTests
    have hPrevious : a.order ⟨2 * pairs + 1, by omega⟩ = 0 := by
      exact hJ1.1 ⟨2 * pairs + 1, by omega⟩
    have hCases := a.he2022ClassicLemma44 (j := 2 * pairs + 4)
      (by omega) (by omega) hPrevious (by
        simpa only [show (2 * pairs + 4) / 2 = pairs + 2 by omega,
          show 2 * pairs + 4 - 1 = 2 * pairs + 3 by omega]
          using hBound)
    let c0 : Kˣ := ((-1 : Kˣ) ^ (pairs + 2)) *
      a.prefixProduct (2 * pairs + 4)
    have hDefectEq :
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4) =
          BONG.GoodBONG.defectOrder (K := K) c0 := by
      dsimp only [c0]
      unfold BONG.GoodBONG.truncatedPrefixDefect
      rw [a.prefixAlphaCap_zero, a.prefixAlphaCap_last]
      simp [BONG.GoodBONG.prefixProduct]
    have hDefectCases :
        BONG.GoodBONG.defectOrder (K := K) c0 = 0 ∨
          BONG.GoodBONG.defectOrder (K := K) c0 = 1 := by
      simpa only [show (2 * pairs + 4) / 2 = pairs + 2 by omega,
        hDefectEq] using hCases.2
    have hPrefixZero :
        a.orderSequence.prefixSum (2 * pairs + 3) = 0 := by
      unfold BeliOrderSequence.prefixSum
      apply Finset.sum_eq_zero
      intro i hi
      rw [BeliOrderSequence.entryOrZero_of_lt _ (by
        have hi' := Finset.mem_range.mp hi
        omega)]
      exact hJ1.1 ⟨i, by
        have hi' := Finset.mem_range.mp hi
        omega⟩
    have hPrefixFull :
        a.orderSequence.prefixSum (2 * pairs + 4) =
          a.order ⟨2 * pairs + 3, by omega⟩ := by
      calc
        a.orderSequence.prefixSum (2 * pairs + 4) =
            a.orderSequence.prefixSum ((2 * pairs + 3) + 1) := by
              congr 1
        _ = a.orderSequence.prefixSum (2 * pairs + 3) +
            a.orderSequence.entryOrZero (2 * pairs + 3) :=
              a.orderSequence.prefixSum_succ (2 * pairs + 3)
        _ = a.order ⟨2 * pairs + 3, by omega⟩ := by
              rw [hPrefixZero,
                BeliOrderSequence.entryOrZero_of_lt _ (by omega)]
              simp
    have hOrdOne : ordUnit K (1 : Kˣ) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      simp
    have hOrderC0 : ordUnit K c0 =
        a.order ⟨2 * pairs + 3, by omega⟩ := by
      dsimp only [c0]
      rw [ordUnit_mul, ordUnit_pow, ordUnit_neg, hOrdOne,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * pairs + 4) (by omega),
        hPrefixFull]
      simp
    have hOrderCases : ordUnit K c0 = 0 ∨ ordUnit K c0 = 1 := by
      simpa only [show 2 * pairs + 4 - 1 = 2 * pairs + 3 by omega,
        hOrderC0] using hCases.1
    obtain ⟨c, s, second, hPair, hcNonnegative, hfactor,
        hFirst, hSecond⟩ :=
      exists_represented_publishedEven_pair_of_low_signed_parameter
        U hU pairs X hAll c0 hOrderCases hDefectCases
    exact (heClassicEvenPair_not_both_goodBONG_of_signedPrefix_factor
      (K := K) pairs a c s second hPair hcNonnegative
      (by simpa only [c0] using hfactor) hFirst hSecond).elim

end Lattice.QuadraticLatticeModel

end Bong
