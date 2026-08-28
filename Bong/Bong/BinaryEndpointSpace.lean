/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointStandardModel
import Bong.QuadraticSpace.BinaryDiagonal
import Bong.QuadraticSpace.Isometry

/-!
# Ambient spaces of the standard binary endpoint models

The fixed model with parameter `-η/4` and shear `1/2` diagonalizes over the
field to `[u,-uη]`.  For `η = 1` this is a hyperbolic plane; for `η = Δ` it is
the residual plane displayed in Beli (2019), Lemma 7.5.
-/

namespace Bong

open Dyadic

universe u


variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The field change of coordinates
`(x₀,x₁) ↦ (x₀ + x₁/2, x₁/2)` which diagonalizes an endpoint model. -/
noncomputable def endpointDiagonalLinearEquiv :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x :=
    ![x 0 + standardEndpointShear (K := K) * x 1,
      standardEndpointShear (K := K) * x 1]
  invFun x := ![x 0 - x 1, 2 * x 1]
  left_inv x := by
    funext i
    fin_cases i
    · dsimp [standardEndpointShear]
      field_simp
      ring
    · dsimp [standardEndpointShear]
      field_simp
  right_inv x := by
    funext i
    fin_cases i
    · dsimp [standardEndpointShear]
      field_simp
      ring
    · dsimp [standardEndpointShear]
      field_simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem endpointDiagonalLinearEquiv_apply_zero (x : Fin 2 → K) :
    endpointDiagonalLinearEquiv (K := K) x 0 =
      x 0 + standardEndpointShear (K := K) * x 1 :=
  rfl

@[simp]
theorem endpointDiagonalLinearEquiv_apply_one (x : Fin 2 → K) :
    endpointDiagonalLinearEquiv (K := K) x 1 =
      standardEndpointShear (K := K) * x 1 :=
  rfl

/-- The endpoint model with parameter `-η/4` has underlying diagonal space
`[u,-uη]`. -/
theorem standardEndpointModelSpace_isIsometric_binaryDiagonal
    (u η : Kˣ) :
    QuadraticSpace.IsIsometric
      (QuadraticSpace.rescaleUnit u
        (QuadraticSpace.binaryModel
          (negativeQuarterUnit K * η)
          (standardEndpointShear (K := K))))
      (QuadraticSpace.binaryDiagonal u (-(u * η))) := by
  refine ⟨{
    toLinearEquiv := endpointDiagonalLinearEquiv (K := K)
    map_bilin := ?_
  }⟩
  intro x y
  rw [QuadraticSpace.binaryDiagonal_bilin_apply]
  simp only [endpointDiagonalLinearEquiv_apply_zero,
    endpointDiagonalLinearEquiv_apply_one,
    QuadraticSpace.rescaleUnit_bilin_apply]
  rw [QuadraticSpace.binaryModel, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two,
    QuadraticSpace.binaryModelMatrix_zero_zero,
    QuadraticSpace.binaryModelMatrix_zero_one,
    QuadraticSpace.binaryModelMatrix_one_zero,
    QuadraticSpace.binaryModelMatrix_one_one,
    Units.val_neg, Units.val_mul]
  dsimp [standardEndpointShear, negativeQuarterUnit]
  norm_num [show (4 : K) = 2 * 2 by norm_num]
  field_simp
  ring

end BONG

end Bong
