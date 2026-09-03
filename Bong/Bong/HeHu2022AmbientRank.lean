/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022SectionFour
import Bong.Bong.HeHu2022Lemma313
import Bong.Bong.Beli2019SectionFiveRepresentationDual
import Bong.Bong.BeliUniversalCorollary45
import Bong.Lattice.OmearaUnimodularNormClassification
import Bong.QuadraticSpace.OrthogonalComplementRepresentation
import Bong.Lattice.RankFourDeterminantHyperbolic

/-!
# He--Hu 2022: ambient-space rank classification

This file formalizes the quadratic-space classification used in the proofs
of Corollary 4.6, Theorem 4.7, and Theorem 1.1.  For target rank at least two,
an ambient space represents every target space once its rank is at least
three larger.  The only lower-rank exception is binary targets represented
by the split quaternary space `H ⊥ H`.

The necessity proof uses the two nonisometric determinant-class
representatives of Definition 3.4 and the exact-one representation statement
of Lemma 3.13.  No classification axiom is added here.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u


variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- Convert the recursively adjoined standard hyperbolic planes to the
half-integral O'Meara-plane normalization used by the Witt-index theorem. -/
noncomputable def hyperbolicExtensionToHalfExtensionSpaceIsometry
    (r : QuadraticSpace K W) :
    (n : Nat) ->
      Isometry (Lattice.hyperbolicExtensionForm r n)
        (Lattice.halfHyperbolicExtensionForm r n)
  | 0 => Isometry.refl r
  | n + 1 => by
      let head := ((scaledHyperbolicChangeScaleSpaceIsometry
          (1 : Kˣ) (Lattice.dyadicHalfUnit (K := K))).trans
        ((Lattice.scaledZeroOmearaPlaneLatticeIsometry
          (Lattice.dyadicHalfUnit (K := K))).symm.toQuadraticSpaceIsometry))
      exact head.orthogonalSum
        (hyperbolicExtensionToHalfExtensionSpaceIsometry r n)

/-- Remove the terminal zero-dimensional coordinate from a tower of two
standard hyperbolic planes. -/
noncomputable def hyperbolicExtensionTwoToHyperbolicPairSpaceIsometry :
    Isometry
      (Lattice.hyperbolicExtensionForm
        (Lattice.zeroCoordinateQuadraticSpace (K := K)) 2)
      ((hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
        (hyperbolicPlane (K := K) (1 : Kˣ))) where
  toLinearEquiv :=
    { toFun := fun x => (x.1, x.2.1)
      invFun := fun y => (y.1, (y.2, 0))
      left_inv := by
        intro x
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · change (0 : Fin 0 → K) = x.2.2
            funext i
            exact Fin.elim0 i
      right_inv := by intro y; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  map_bilin := by
    intro x y
    change
      (hyperbolicPlane (K := K) (1 : Kˣ)).bilin x.1 y.1 +
          (hyperbolicPlane (K := K) (1 : Kˣ)).bilin x.2.1 y.2.1 =
        (hyperbolicPlane (K := K) (1 : Kˣ)).bilin x.1 y.1 +
          ((hyperbolicPlane (K := K) (1 : Kˣ)).bilin x.2.1 y.2.1 + 0)
    simp

end QuadraticSpace

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Ambient universality represents every nonsingular diagonal model of the
target rank; an integral rescaling supplies the lattice witness. -/
theorem AmbientlyNUniversal.representsFiniteDiagonal
    (h : AmbientlyNUniversal.{u, v, u} q n)
    (a : Fin n → Kˣ) :
    q.Represents
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients a)
        (fun i => Units.ne_zero (a i))) := by
  let r := QuadraticSpace.finiteDiagonal
    (BONG.GoodBONG.diagonalUnitCoefficients a)
    (fun i => Units.ne_zero (a i))
  let A : Lattice K (Fin n → K) := basisLattice (Pi.basisFun K (Fin n))
  obtain ⟨c, hc⟩ := exists_integral_rescale r A
  exact h r (rescale c A) (by simp) hc

/-- Diagonal-coordinate form of
`AmbientlyNUniversal.representsFiniteDiagonal`. -/
theorem AmbientlyNUniversal.diagonalRepresents
    [FiniteDimensional K V]
    (h : AmbientlyNUniversal.{u, v, u} q n)
    (a : Fin n → Kˣ) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients a)
      (BONG.GoodBONG.diagonalUnitCoefficients q.diagonalUnits) := by
  have hrep := h.representsFiniteDiagonal a
  have hdiag : q.diagonalModel.Represents
      (QuadraticSpace.finiteDiagonal
        (BONG.GoodBONG.diagonalUnitCoefficients a)
        (fun i => Units.ne_zero (a i))) :=
    ⟨q.diagonalizationIsometry.toRepresentation.trans
      (Classical.choice hrep)⟩
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    a q.diagonalUnits).mp hdiag

/-- Every dyadic quadratic space whose rank is at least three above the
target rank represents all target spaces. -/
theorem ambientlyNUniversal_of_rank_add_three_le
    [FiniteDimensional K V]
    (n : Nat) (hsourceRank : n + 3 ≤ finrank K V) :
    AmbientlyNUniversal.{u, v, w} q n := by
  intro W _ _ r M hrank hM
  letI : Module.Finite K W := M.moduleFinite
  let negativeR := r.rescaleUnit (-1 : Kˣ)
  let totalForm := q.orthogonalSum negativeR
  let diagonalForm := totalForm.diagonalModel
  let X : QuadraticLatticeModel (K := K) :=
    { Carrier := Fin (finrank K (V × W)) → K
      form := diagonalForm
      lattice := basisLattice (Pi.basisFun K (Fin (finrank K (V × W)))) }
  obtain ⟨d, hsource⟩ := Nat.exists_eq_add_of_le hsourceRank
  have hXrank : X.rank = 2 * n + (3 + d) := by
    change finrank K (Fin (finrank K (V × W)) → K) = _
    rw [Module.finrank_fin_fun, Module.finrank_prod, hrank, hsource]
    omega
  obtain ⟨S, hsplit⟩ :=
    QuadraticLatticeModel.hasWittIndexAtLeast_of_rank_eq_two_mul_add
      (3 + d) (by omega) n X hXrank
  letI : AddCommGroup S.Carrier := S.addCommGroup
  letI : Module K S.Carrier := S.module
  rcases hsplit with ⟨split⟩
  let totalSplit : QuadraticSpace.Isometry totalForm
      (halfHyperbolicExtensionForm S.form n) :=
    totalForm.diagonalizationIsometry.trans split
  let zeroForm := zeroCoordinateQuadraticSpace (K := K)
  let zeroLattice := zeroCoordinateLattice (K := K)
  let ordinaryToHalf :=
    QuadraticSpace.hyperbolicExtensionToHalfExtensionSpaceIsometry zeroForm n
  let appendHalf := (omearaPlaneExtensionAppendIsometry
    zeroLattice S.form S.lattice (dyadicHalfUnit (K := K)) n
      (fun _ => 0)).toQuadraticSpaceIsometry
  let halfTowerIntoHalfExtension : QuadraticSpace.Representation
      (hyperbolicExtensionForm zeroForm n)
      (halfHyperbolicExtensionForm S.form n) := by
    rw [halfHyperbolicExtensionForm_eq]
    exact appendHalf.toRepresentation.trans
      ((QuadraticSpace.Representation.orthogonalSumInl
        (halfHyperbolicExtensionForm zeroForm n) S.form).trans
          ordinaryToHalf.toRepresentation)
  let negativePairToOrdinary : QuadraticSpace.Isometry
      (negativeR.orthogonalSum r)
      (hyperbolicExtensionForm zeroForm n) := by
    rw [← hrank]
    exact negativeQuadraticHyperbolicIsometry r
  let negativePairIntoHalf : QuadraticSpace.Representation
      (negativeR.orthogonalSum r)
      (halfHyperbolicExtensionForm S.form n) :=
    halfTowerIntoHalfExtension.trans negativePairToOrdinary.toRepresentation
  let negativePairIntoTotal : QuadraticSpace.Representation
      (negativeR.orthogonalSum r) totalForm :=
    totalSplit.symm.toRepresentation.trans negativePairIntoHalf
  let negativePairIntoSwapped : QuadraticSpace.Representation
      (negativeR.orthogonalSum r) (negativeR.orthogonalSum q) :=
    (QuadraticSpace.orthogonalSumSwap q negativeR).toRepresentation.trans
      negativePairIntoTotal
  exact QuadraticSpace.orthogonalSumLeftCancelRepresents
    negativeR r q ⟨negativePairIntoSwapped⟩

/-- The split quaternary space represents every binary quadratic space. -/
theorem ambientlyTwoUniversal_hyperbolicPair :
    AmbientlyNUniversal.{u, u, w}
      ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))) 2 := by
  intro W _ _ r M hrank _hM
  letI : Module.Finite K W := M.moduleFinite
  let negativeR := r.rescaleUnit (-1 : Kˣ)
  let intoSwapped : QuadraticSpace.Representation r
      (negativeR.orthogonalSum r) :=
    (QuadraticSpace.orthogonalSumSwap r negativeR).toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl r negativeR)
  let intoTower : QuadraticSpace.Representation r
      (hyperbolicExtensionForm zeroCoordinateQuadraticSpace
        (finrank K W)) :=
    (negativeQuadraticHyperbolicIsometry r).toRepresentation.trans intoSwapped
  have intoTowerTwo : QuadraticSpace.Representation r
      (hyperbolicExtensionForm zeroCoordinateQuadraticSpace 2) := by
    rw [hrank] at intoTower
    exact intoTower
  exact ⟨QuadraticSpace.hyperbolicExtensionTwoToHyperbolicPairSpaceIsometry
    |>.toRepresentation.trans intoTowerTwo⟩

/-- Ambient rank-`n` universality forces the source rank to be at least
`n`. -/
theorem AmbientlyNUniversal.rank_le
    [FiniteDimensional K V]
    (h : AmbientlyNUniversal.{u, v, u} q n) :
    n ≤ finrank K V := by
  let a : Fin n → Kˣ := fun _ => 1
  rcases h.representsFiniteDiagonal a with ⟨f⟩
  have hle := f.toLinearMap.finrank_le_finrank_of_injective f.injective
  simpa using hle

/-- Two nonisometric models in one determinant class rule out ambient
universality in equal rank. -/
theorem not_ambientlyNUniversal_of_rank_eq
    [FiniteDimensional K V]
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : finrank K V = n) :
    ¬ AmbientlyNUniversal.{u, v, u} q n := by
  intro h
  let e : Fin n ≃ Fin (finrank K V) := finCongr hrank.symm
  let target : Fin n → Kˣ := fun i => q.diagonalUnits (e i)
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
  have hfirst := (h.diagonalRepresents first).trans
    hqToTarget
  have hsecond := (h.diagonalRepresents second).trans
    hqToTarget
  exact pair.nonisometric (hsecond.trans hfirst.symm_of_sameRank)

/-- Lemma 3.13 rules out ambient universality in codimension one. -/
theorem not_ambientlyNUniversal_of_rank_eq_add_one
    [FiniteDimensional K V]
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : finrank K V = n + 1) :
    ¬ AmbientlyNUniversal.{u, v, u} q n := by
  intro h
  let e : Fin (n + 1) ≃ Fin (finrank K V) := finCongr hrank.symm
  let target : Fin (n + 1) → Kˣ := fun i => q.diagonalUnits (e i)
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
  have hfirst := (h.diagonalRepresents first).trans
    hqToTarget
  have hsecond := (h.diagonalRepresents second).trans
    hqToTarget
  rcases heHu2022Lemma313CodimensionOne
      first second pair target with hexact | hexact
  · exact hexact.2 hsecond
  · exact hexact.1 hfirst

/-- Lemma 3.13 rules out ambient universality in codimension two whenever
the displayed determinant compatibility holds. -/
theorem not_ambientlyNUniversal_of_rank_eq_add_two
    [FiniteDimensional K V]
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hrank : finrank K V = n + 2)
    (hdet : IsSquare
      (-BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits *
        BONG.GoodBONG.diagonalUnitDeterminant first)) :
    ¬ AmbientlyNUniversal.{u, v, u} q n := by
  intro h
  let e : Fin (n + 2) ≃ Fin (finrank K V) := finCongr hrank.symm
  let target : Fin (n + 2) → Kˣ := fun i => q.diagonalUnits (e i)
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
  have hfirst := (h.diagonalRepresents first).trans
    hqToTarget
  have hsecond := (h.diagonalRepresents second).trans
    hqToTarget
  have htargetDet : IsSquare
      (-BONG.GoodBONG.diagonalUnitDeterminant target *
        BONG.GoodBONG.diagonalUnitDeterminant first) := by
    have htargetDetEq :
        BONG.GoodBONG.diagonalUnitDeterminant target =
          BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits := by
      unfold BONG.GoodBONG.diagonalUnitDeterminant target
      exact e.prod_comp q.diagonalUnits
    rw [htargetDetEq]
    exact hdet
  rcases heHu2022Lemma313CodimensionTwo
      first second pair target htargetDet with hexact | hexact
  · exact hexact.2 hsecond
  · exact hexact.1 hfirst

/-- Ambient classification for even target rank `2*pairs+2`, including the
unique split-quaternary exception. -/
theorem ambientlyEvenUniversal_rank_classification
    [FiniteDimensional K V]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) :
    AmbientlyNUniversal.{u, v, u} q (2 * pairs + 2) ↔
      2 * pairs + 5 ≤ finrank K V ∨
        (pairs = 0 ∧ finrank K V = 4 ∧
          q.IsIsometric
            ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
              (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)))) := by
  constructor
  · intro h
    by_cases hstable : 2 * pairs + 5 ≤ finrank K V
    · exact Or.inl hstable
    · right
      have hrankLe := h.rank_le
      have hrankCases :
          finrank K V = 2 * pairs + 2 ∨
          finrank K V = 2 * pairs + 3 ∨
          finrank K V = 2 * pairs + 4 := by omega
      rcases hrankCases with hrank | hrank | hrank
      · let delta :=
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        have hdelta : ¬ IsSquare delta :=
          AlternatingEndpointNormalization.discriminantUnit_not_isSquare
            (K := K)
        have hdefined : HeHuEvenSecondDefined pairs delta := Or.inr hdelta
        let pair := heHu2022Definition34Proposition35Even pairs delta hdefined
        exact (not_ambientlyNUniversal_of_rank_eq
          (heHuEvenFirst pairs delta)
          (heHuEvenSecond pairs delta hdefined) pair hrank h).elim
      · let delta :=
          (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        have hdelta : ¬ IsSquare delta :=
          AlternatingEndpointNormalization.discriminantUnit_not_isSquare
            (K := K)
        have hdefined : HeHuEvenSecondDefined pairs delta := Or.inr hdelta
        let pair := heHu2022Definition34Proposition35Even pairs delta hdefined
        exact (not_ambientlyNUniversal_of_rank_eq_add_one
          (heHuEvenFirst pairs delta)
          (heHuEvenSecond pairs delta hdefined) pair hrank h).elim
      · by_cases hpairs : pairs = 0
        · subst pairs
          let D := BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits
          by_cases hD : IsSquare D
          · refine ⟨rfl, by omega, ?_⟩
            have hHIntegral : Lattice.IsIntegral
                (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))
                (hyperbolicPlaneLattice (K := K)) := by
              rw [Lattice.isIntegral_iff_forall]
              intro x hx
              rw [QuadraticSpace.hyperbolicPlane_quadratic_apply]
              have hx' := (mem_hyperbolicPlaneLattice_iff x).mp hx
              have htwo : Dyadic.IsIntegral K (2 : K) :=
                (Dyadic.ord_two_pos K).le
              simpa using Dyadic.isIntegral_mul K htwo
                (Dyadic.isIntegral_mul K
                  ((Dyadic.mem_integerRing_iff K).mp hx'.1)
                  ((Dyadic.mem_integerRing_iff K).mp hx'.2))
            have hhyperbolic : q.Represents
                (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)) :=
              h (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))
                (hyperbolicPlaneLattice (K := K)) (by simp) hHIntegral
            exact QuadraticSpace.rankFour_isIsometric_hyperbolicPair_of_diagonalDeterminant_isSquare
              q (by omega) hD hhyperbolic
          · let c : Kˣ := D⁻¹
            have hc : ¬ IsSquare c := by
              intro hcSquare
              apply hD
              simpa [c, D] using hcSquare.inv
            have hdefined : HeHuEvenSecondDefined 0 c := Or.inr hc
            let pair := heHu2022Definition34Proposition35Even 0 c hdefined
            have hdet : IsSquare
                (-BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits *
                  BONG.GoodBONG.diagonalUnitDeterminant
                    (heHuEvenFirst 0 c)) := by
              rw [diagonalUnitDeterminant_heHuEvenFirst]
              refine ⟨1, ?_⟩
              simp [c, D]
            exact (not_ambientlyNUniversal_of_rank_eq_add_two
              (heHuEvenFirst 0 c) (heHuEvenSecond 0 c hdefined)
              pair hrank hdet h).elim
        · let D := BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits
          let c : Kˣ :=
            (-D * (-1 : Kˣ) ^ (pairs + 1))⁻¹
          have hdefined : HeHuEvenSecondDefined pairs c :=
            Or.inl (Nat.pos_of_ne_zero hpairs)
          let pair := heHu2022Definition34Proposition35Even pairs c hdefined
          have hdet : IsSquare
              (-BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits *
                BONG.GoodBONG.diagonalUnitDeterminant
                  (heHuEvenFirst pairs c)) := by
            rw [diagonalUnitDeterminant_heHuEvenFirst]
            refine ⟨1, ?_⟩
            simp [c, D, mul_comm]
          exact (not_ambientlyNUniversal_of_rank_eq_add_two
            (heHuEvenFirst pairs c) (heHuEvenSecond pairs c hdefined)
            pair hrank hdet h).elim
  · rintro (hstable | ⟨rfl, hrank, hsplit⟩)
    · exact ambientlyNUniversal_of_rank_add_three_le
        (2 * pairs + 2) (by omega)
    · intro W _ _ r M htargetRank hM
      rcases hsplit with ⟨split⟩
      have hqRepPair : q.Represents
          ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
            (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))) :=
        ⟨split.symm.toRepresentation⟩
      exact hqRepPair.trans
        (ambientlyTwoUniversal_hyperbolicPair r M htargetRank hM)

/-- Ambient classification for odd target rank `2*pairs+3`. -/
theorem ambientlyOddUniversal_rank_classification
    [FiniteDimensional K V]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) :
    AmbientlyNUniversal.{u, v, u} q (2 * pairs + 3) ↔
      2 * pairs + 6 ≤ finrank K V := by
  constructor
  · intro h
    by_contra hstable
    have hrankLe := h.rank_le
    have hrankCases :
        finrank K V = 2 * pairs + 3 ∨
        finrank K V = 2 * pairs + 4 ∨
        finrank K V = 2 * pairs + 5 := by omega
    rcases hrankCases with hrank | hrank | hrank
    · let pair := heHu2022Definition34Proposition35Odd pairs (1 : Kˣ)
      exact not_ambientlyNUniversal_of_rank_eq
        (heHuOddFirst pairs (1 : Kˣ))
        (heHuOddSecond pairs (1 : Kˣ)) pair hrank h
    · let pair := heHu2022Definition34Proposition35Odd pairs (1 : Kˣ)
      exact not_ambientlyNUniversal_of_rank_eq_add_one
        (heHuOddFirst pairs (1 : Kˣ))
        (heHuOddSecond pairs (1 : Kˣ)) pair hrank h
    · let D := BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits
      let c : Kˣ := (-D * (-1 : Kˣ) ^ (pairs + 1))⁻¹
      let pair := heHu2022Definition34Proposition35Odd pairs c
      have hdet : IsSquare
          (-BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits *
            BONG.GoodBONG.diagonalUnitDeterminant
              (heHuOddFirst pairs c)) := by
        rw [diagonalUnitDeterminant_heHuOddFirst]
        refine ⟨1, ?_⟩
        simp [c, D, mul_comm]
      exact not_ambientlyNUniversal_of_rank_eq_add_two
        (heHuOddFirst pairs c) (heHuOddSecond pairs c)
        pair hrank hdet h
  · intro hstable
    exact ambientlyNUniversal_of_rank_add_three_le
      (2 * pairs + 3) hstable

end Lattice

end Bong
