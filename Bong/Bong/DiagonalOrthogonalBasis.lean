/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Bong.Bong.BeliLemma43
import Bong.Bong.DiagonalLocalClassification
import Bong.Bong.DiagonalTernaryCore
import Mathlib.LinearAlgebra.StdBasis

/-!
# Orthogonal bases from diagonal representations

An equal-rank representation of a diagonal coefficient list by the values of
a BONG is an invertible coordinate change.  This file turns that coordinate
change into an actual orthogonal basis of the ambient quadratic space and
proves that its bundled values are the prescribed coefficients.
-/

namespace Bong

open Module
open Dyadic

universe u v

namespace DiagonalRepresents

variable {K : Type u} [Field K]

@[simp]
theorem diagonalQuadratic_basisFun {n : Nat} (c : Fin n → K) (i : Fin n) :
    diagonalQuadratic c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  simp [diagonalQuadratic, Pi.basisFun_apply, Pi.single_apply]

theorem diagonalQuadratic_basisFun_add {n : Nat}
    (c : Fin n → K) (i j : Fin n) (hij : i ≠ j) :
    diagonalQuadratic c
        (Pi.basisFun K (Fin n) i + Pi.basisFun K (Fin n) j) =
      c i + c j := by
  classical
  let ei := Pi.basisFun K (Fin n) i
  let ej := Pi.basisFun K (Fin n) j
  have hcross : ∑ k, c k * ei k * ej k = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k
      simp [ei, ej, Pi.basisFun_apply, hij]
    · simp [ei, Pi.basisFun_apply, hki]
  change diagonalQuadratic c (ei + ej) = c i + c j
  calc
    diagonalQuadratic c (ei + ej) =
        diagonalQuadratic c ei + diagonalQuadratic c ej +
          2 * ∑ k, c k * ei k * ej k := by
      unfold diagonalQuadratic
      simp_rw [Pi.add_apply]
      rw [show (∑ k, c k * (ei k + ej k) ^ 2) =
          (∑ k, c k * ei k ^ 2) + (∑ k, c k * ej k ^ 2) +
            2 * ∑ k, c k * ei k * ej k by
        simp_rw [add_sq, mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hmiddle : (∑ x, c x * (2 * ei x * ej x)) =
            2 * ∑ x, c x * ei x * ej x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hmiddle]
        ring]
    _ = c i + c j := by
      rw [hcross, mul_zero, add_zero]
      have hi : diagonalQuadratic c ei = c i := by
        simpa only [ei] using diagonalQuadratic_basisFun c i
      have hj : diagonalQuadratic c ej = c j := by
        simpa only [ej] using diagonalQuadratic_basisFun c j
      rw [hi, hj]

variable [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- An equal-rank diagonal representation supplies an ambient orthogonal
basis having exactly the prescribed nonzero values. -/
theorem exists_orthogonalBasisData
    (a : BONG.GoodBONG q L n) (c : Fin n → Kˣ)
    (h : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients c) a.toBONG.value) :
    ∃ X : BONG.OrthogonalBasisData q n, ∀ i, X.valueUnit i = c i := by
  classical
  rcases h with ⟨f, hf, hquadratic⟩
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofBijective f ⟨hf, LinearMap.surjective_of_injective hf⟩
  let coordinateToV : (Fin n → K) ≃ₗ[K] V :=
    e.trans a.toBONG.basis.equivFun.symm
  let newBasis : Basis (Fin n) K V :=
    (Pi.basisFun K (Fin n)).map coordinateToV
  have hpreserves (x : Fin n → K) :
      q.quadratic (coordinateToV x) =
        diagonalQuadratic (BONG.GoodBONG.diagonalUnitCoefficients c) x := by
    change q.quadratic (a.toBONG.basis.equivFun.symm (f x)) = _
    rw [← a.toBONG.diagonalQuadratic_value_eq]
    exact hquadratic x
  have horthogonal : q.bilin.iIsOrtho newBasis := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    let ei := Pi.basisFun K (Fin n) i
    let ej := Pi.basisFun K (Fin n) j
    have hi : q.quadratic (newBasis i) = (c i : K) := by
      rw [show newBasis i = coordinateToV ei by
        simp only [newBasis, Basis.map_apply, ei]]
      rw [hpreserves]
      unfold BONG.GoodBONG.diagonalUnitCoefficients
      exact diagonalQuadratic_basisFun (fun k ↦ (c k : K)) i
    have hj : q.quadratic (newBasis j) = (c j : K) := by
      rw [show newBasis j = coordinateToV ej by
        simp only [newBasis, Basis.map_apply, ej]]
      rw [hpreserves]
      unfold BONG.GoodBONG.diagonalUnitCoefficients
      exact diagonalQuadratic_basisFun (fun k ↦ (c k : K)) j
    have hijValue : q.quadratic (newBasis i + newBasis j) =
        (c i : K) + (c j : K) := by
      rw [show newBasis i + newBasis j = coordinateToV (ei + ej) by
        simp only [newBasis, Basis.map_apply, ei, ej, map_add]]
      rw [hpreserves]
      unfold BONG.GoodBONG.diagonalUnitCoefficients
      exact diagonalQuadratic_basisFun_add (fun k ↦ (c k : K)) i j hij
    have hadd := q.quadratic_add (newBasis i) (newBasis j)
    rw [hijValue, hi, hj] at hadd
    have hzero : 2 * q.bilin (newBasis i) (newBasis j) = 0 := by
      calc
        2 * q.bilin (newBasis i) (newBasis j) =
            ((c i : K) + (c j : K) +
              2 * q.bilin (newBasis i) (newBasis j)) -
                ((c i : K) + (c j : K)) := by ring
        _ = 0 := by rw [← hadd]; ring
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  let X : BONG.OrthogonalBasisData q n := ⟨newBasis, horthogonal⟩
  refine ⟨X, ?_⟩
  intro i
  apply Units.ext
  change q.quadratic (newBasis i) = (c i : K)
  rw [show newBasis i = coordinateToV (Pi.basisFun K (Fin n) i) by
    simp only [newBasis, Basis.map_apply]]
  rw [hpreserves]
  unfold BONG.GoodBONG.diagonalUnitCoefficients
  exact diagonalQuadratic_basisFun (fun k ↦ (c k : K)) i

end DiagonalRepresents

end Bong
