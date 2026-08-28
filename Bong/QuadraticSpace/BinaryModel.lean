/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.FinCases

/-!
# An explicit binary quadratic-space model

For `a ≠ 0` and `c ∈ K`, the symmetric Gram matrix

`[[1, c], [c, c² + a]]`

has determinant `a`.  This model is adapted to the first coordinate: its
orthogonal complement has quadratic value `a`.
-/

namespace Bong

open Module

universe u

variable {K : Type u} [Field K]

namespace QuadraticSpace

/-- The Gram matrix of the binary model with parameter `a` and shear `c`. -/
def binaryModelMatrix (a : Kˣ) (c : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, c; c, c ^ 2 + (a : K)]

@[simp]
theorem binaryModelMatrix_zero_zero (a : Kˣ) (c : K) :
    binaryModelMatrix a c 0 0 = 1 :=
  rfl

@[simp]
theorem binaryModelMatrix_zero_one (a : Kˣ) (c : K) :
    binaryModelMatrix a c 0 1 = c :=
  rfl

@[simp]
theorem binaryModelMatrix_one_zero (a : Kˣ) (c : K) :
    binaryModelMatrix a c 1 0 = c :=
  rfl

@[simp]
theorem binaryModelMatrix_one_one (a : Kˣ) (c : K) :
    binaryModelMatrix a c 1 1 = c ^ 2 + (a : K) :=
  rfl

theorem binaryModelMatrix_isSymm (a : Kˣ) (c : K) :
    (binaryModelMatrix a c).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem binaryModelMatrix_det (a : Kˣ) (c : K) :
    (binaryModelMatrix a c).det = (a : K) := by
  simp [binaryModelMatrix, Matrix.det_fin_two_of]
  ring

/-- The nondegenerate quadratic space attached to the binary model matrix. -/
noncomputable def binaryModel (a : Kˣ) (c : K) :
    QuadraticSpace K (Fin 2 → K) where
  bilin := Matrix.toBilin' (binaryModelMatrix a c)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (binaryModelMatrix_isSymm a c)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (binaryModelMatrix a c) (by simp)

/-- The first standard vector of the binary model. -/
def binaryModelFirst : Fin 2 → K :=
  Pi.single 0 1

/-- The second standard vector of the binary model. -/
def binaryModelSecond : Fin 2 → K :=
  Pi.single 1 1

@[simp]
theorem binaryModel_bilin_first_first (a : Kˣ) (c : K) :
    (binaryModel a c).bilin binaryModelFirst binaryModelFirst = 1 := by
  rw [binaryModel, binaryModelFirst, Matrix.toBilin'_single]
  rfl

@[simp]
theorem binaryModel_bilin_first_second (a : Kˣ) (c : K) :
    (binaryModel a c).bilin binaryModelFirst binaryModelSecond = c := by
  rw [binaryModel, binaryModelFirst, binaryModelSecond,
    Matrix.toBilin'_single]
  rfl

@[simp]
theorem binaryModel_bilin_second_second (a : Kˣ) (c : K) :
    (binaryModel a c).bilin binaryModelSecond binaryModelSecond =
      c ^ 2 + (a : K) := by
  rw [binaryModel, binaryModelSecond, Matrix.toBilin'_single]
  rfl

@[simp]
theorem binaryModel_quadratic_first (a : Kˣ) (c : K) :
    (binaryModel a c).quadratic binaryModelFirst = 1 :=
  binaryModel_bilin_first_first a c

@[simp]
theorem binaryModel_quadratic_second (a : Kˣ) (c : K) :
    (binaryModel a c).quadratic binaryModelSecond =
      c ^ 2 + (a : K) :=
  binaryModel_bilin_second_second a c

/-- Coordinate formula for the quadratic value in the binary model. -/
theorem binaryModel_quadratic_apply (a : Kˣ) (c : K)
    (x : Fin 2 → K) :
    (binaryModel a c).quadratic x =
      x 0 ^ 2 + (2 * c) * (x 0 * x 1) +
        (c ^ 2 + (a : K)) * x 1 ^ 2 := by
  rw [binaryModel, QuadraticSpace.quadratic,
    Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two, binaryModelMatrix_zero_zero,
    binaryModelMatrix_zero_one, binaryModelMatrix_one_zero,
    binaryModelMatrix_one_one]
  ring

/-- The vector `e₁ - c e₀` is orthogonal to the first standard vector. -/
theorem binaryModel_bilin_first_second_sub (a : Kˣ) (c : K) :
    (binaryModel a c).bilin binaryModelFirst
      (binaryModelSecond - c • binaryModelFirst) = 0 := by
  rw [LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_right]
  simp

/-- The orthogonalized second vector has quadratic value `a`. -/
theorem binaryModel_quadratic_second_sub (a : Kˣ) (c : K) :
    (binaryModel a c).quadratic
      (binaryModelSecond - c • binaryModelFirst) = (a : K) := by
  rw [binaryModel_quadratic_apply]
  simp [binaryModelFirst, binaryModelSecond]
  ring

end QuadraticSpace

end Bong
