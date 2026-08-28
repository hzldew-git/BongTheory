/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefect
import Bong.QuadraticSpace.WallForm

/-!
# The spinor norm from the Wall determinant

For a finite-dimensional nondegenerate quadratic space, the spinor norm of an
isometry is the square class of the determinant of its Wall form.  This
definition avoids choosing a reflection decomposition.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- The spinor norm of an isometry, defined by its Wall determinant. -/
noncomputable def spinorNorm [FiniteDimensional K V] (f : Isometry q q) :
    SquareClass K :=
  squareClass K (Units.mk0 (wallDeterminant f) (wallDeterminant_ne_zero f))

/-- The spinor norm is represented by the Wall determinant. -/
@[simp]
theorem spinorNorm_eq_wallDeterminant [FiniteDimensional K V]
    (f : Isometry q q) :
    spinorNorm f =
      squareClass K
        (Units.mk0 (wallDeterminant f) (wallDeterminant_ne_zero f)) :=
  rfl

/--
The square class of the Wall determinant can be computed in any basis with
the canonical finite index set.
-/
theorem spinorNorm_eq_basisDeterminant [FiniteDimensional K V]
    (f : Isometry q q)
    (b : Module.Basis (Fin (Module.finrank K (residualSpace f))) K
      (residualSpace f)) :
    spinorNorm f =
      squareClass K
        (Units.mk0
          (Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)))
          ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
            (wallForm_nondegenerate f))) := by
  let P := (wallBasis f).toMatrix b
  have hmatrix :
      P.transpose *
          LinearMap.BilinForm.toMatrix (wallBasis f) (wallForm f) * P =
        LinearMap.BilinForm.toMatrix b (wallForm f) := by
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (wallBasis f) b (wallForm f)
  have hdet :
      Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)) =
        wallDeterminant f * Matrix.det P ^ 2 := by
    rw [wallDeterminant, ← hmatrix]
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hP : Matrix.det P ≠ 0 := by
    intro hzero
    have hb := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
      (wallForm_nondegenerate f)
    apply hb
    rw [hdet, hzero]
    simp
  let p : Kˣ := Units.mk0 (Matrix.det P) hP
  have hu :
      Units.mk0
          (Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)))
          ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
            (wallForm_nondegenerate f)) =
        Units.mk0 (wallDeterminant f) (wallDeterminant_ne_zero f) * p ^ 2 := by
    apply Units.ext
    exact hdet
  rw [spinorNorm_eq_wallDeterminant, hu]
  exact (squareClass_mul_square K
    (Units.mk0 (wallDeterminant f) (wallDeterminant_ne_zero f)) p).symm

/-- A dimension equality allows an arbitrary finite index for computation. -/
theorem spinorNorm_eq_basisDeterminantOfFinrankEq [FiniteDimensional K V]
    (f : Isometry q q) {n : ℕ}
    (hfin : Module.finrank K (residualSpace f) = n)
    (b : Module.Basis (Fin n) K (residualSpace f)) :
    spinorNorm f =
      squareClass K
        (Units.mk0
          (Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)))
          ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
            (wallForm_nondegenerate f))) := by
  subst n
  exact spinorNorm_eq_basisDeterminant f b

omit [CharZero K] in
/-- The residual space of the identity is zero. -/
@[simp]
theorem residualSpace_refl : residualSpace (Isometry.refl q) = ⊥ := by
  rw [residualSpace, LinearMap.range_eq_bot]
  ext y
  simp [residualLinearMap, Isometry.refl]

omit [CharZero K] in
/-- The Wall determinant of the identity is one. -/
@[simp]
theorem wallDeterminant_refl [FiniteDimensional K V] :
    wallDeterminant (Isometry.refl q) = 1 := by
  have hfin : Module.finrank K (residualSpace (Isometry.refl q)) = 0 := by
    simp
  rw [wallDeterminant]
  apply Matrix.det_eq_one_of_card_eq_zero
  simp [hfin]

/-- The identity isometry has trivial spinor norm. -/
@[simp]
theorem spinorNorm_refl [FiniteDimensional K V] :
    spinorNorm (Isometry.refl q) = 1 := by
  rw [spinorNorm_eq_wallDeterminant]
  have hu :
      Units.mk0 (wallDeterminant (Isometry.refl q))
          (wallDeterminant_ne_zero (Isometry.refl q)) = (1 : Kˣ) := by
    apply Units.ext
    exact wallDeterminant_refl
  rw [hu]
  rfl

end QuadraticSpace

end Bong
