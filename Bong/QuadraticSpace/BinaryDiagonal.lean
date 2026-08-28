/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.FinCases

/-! # Binary diagonal quadratic spaces -/

namespace Bong

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- The Gram matrix of the diagonal binary space `[a,b]`. -/
def binaryDiagonalMatrix (a b : Kˣ) : Matrix (Fin 2) (Fin 2) K :=
  !![(a : K), 0; 0, (b : K)]

theorem binaryDiagonalMatrix_isSymm (a b : Kˣ) :
    (binaryDiagonalMatrix a b).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem binaryDiagonalMatrix_det (a b : Kˣ) :
    (binaryDiagonalMatrix a b).det = (a : K) * (b : K) := by
  simp [binaryDiagonalMatrix, Matrix.det_fin_two_of]

/-- The nondegenerate diagonal binary quadratic space `[a,b]`. -/
noncomputable def binaryDiagonal (a b : Kˣ) :
    QuadraticSpace K (Fin 2 → K) where
  bilin := Matrix.toBilin' (binaryDiagonalMatrix a b)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (binaryDiagonalMatrix_isSymm a b)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (binaryDiagonalMatrix a b) (by simp)

@[simp]
theorem binaryDiagonal_bilin_apply (a b : Kˣ)
    (x y : Fin 2 → K) :
    (binaryDiagonal a b).bilin x y =
      (a : K) * x 0 * y 0 + (b : K) * x 1 * y 1 := by
  rw [binaryDiagonal, Matrix.toBilin'_apply]
  simp [binaryDiagonalMatrix]
  ring

@[simp]
theorem binaryDiagonal_quadratic_apply (a b : Kˣ)
    (x : Fin 2 → K) :
    (binaryDiagonal a b).quadratic x =
      (a : K) * x 0 ^ 2 + (b : K) * x 1 ^ 2 := by
  rw [quadratic, binaryDiagonal_bilin_apply]
  ring

end QuadraticSpace

end Bong
