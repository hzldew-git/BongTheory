/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralPlane
import Bong.Bong.DiagonalHasseSymbol

/-!
# Diagonalizing O'Meara's general binary plane

For a nonzero first coefficient, the elementary orthogonalization

`e₁ ↦ e₁ - alpha⁻¹ e₀`

identifies `A(alpha,beta)` over the field with the diagonal form
`<alpha, beta - alpha⁻¹>`.  This file records the coordinate isometry and
packages the two nonzero diagonal coefficients as units.  It is the field
invariant layer used in the low-rank cases of O'Meara 93:18.
-/

namespace Bong

open Dyadic BONG.GoodBONG

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- The two diagonal coefficients obtained from `A(alpha,beta)` by
orthogonalizing the second standard vector against the first. -/
def omearaGeneralPlaneDiagonalCoefficients (alpha : Kˣ) (beta : K) :
    Fin 2 → K :=
  ![(alpha : K), beta - (alpha : K)⁻¹]

@[simp]
theorem omearaGeneralPlaneDiagonalCoefficients_zero
    (alpha : Kˣ) (beta : K) :
    omearaGeneralPlaneDiagonalCoefficients alpha beta 0 = (alpha : K) :=
  rfl

@[simp]
theorem omearaGeneralPlaneDiagonalCoefficients_one
    (alpha : Kˣ) (beta : K) :
    omearaGeneralPlaneDiagonalCoefficients alpha beta 1 =
      beta - (alpha : K)⁻¹ :=
  rfl

/-- Nondegeneracy of `A(alpha,beta)` is exactly nonvanishing of the second
coefficient after orthogonalization. -/
theorem omearaGeneralPlaneDiagonalTail_ne_zero
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    beta - (alpha : K)⁻¹ ≠ 0 := by
  intro hzero
  apply hnondegenerate
  have hbeta : beta = (alpha : K)⁻¹ := sub_eq_zero.mp hzero
  rw [hbeta]
  exact mul_inv_cancel₀ (Units.ne_zero alpha)

/-- Both diagonal coefficients of the orthogonalized plane are nonzero. -/
theorem omearaGeneralPlaneDiagonalCoefficients_ne_zero
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    ∀ i, omearaGeneralPlaneDiagonalCoefficients alpha beta i ≠ 0 := by
  intro i
  fin_cases i
  · exact Units.ne_zero alpha
  · exact omearaGeneralPlaneDiagonalTail_ne_zero alpha beta hnondegenerate

/-- Coordinate map from the standard basis of `A(alpha,beta)` to its
orthogonalized coordinates. -/
noncomputable def omearaGeneralPlaneOrthogonalizingLinearEquiv
    (alpha : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun := fun x ↦ ![x 0 + (alpha : K)⁻¹ * x 1, x 1]
  invFun := fun x ↦ ![x 0 - (alpha : K)⁻¹ * x 1, x 1]
  left_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem omearaGeneralPlaneOrthogonalizingLinearEquiv_zero
    (alpha : Kˣ) (x : Fin 2 → K) :
    omearaGeneralPlaneOrthogonalizingLinearEquiv alpha x 0 =
      x 0 + (alpha : K)⁻¹ * x 1 :=
  rfl

@[simp]
theorem omearaGeneralPlaneOrthogonalizingLinearEquiv_one
    (alpha : Kˣ) (x : Fin 2 → K) :
    omearaGeneralPlaneOrthogonalizingLinearEquiv alpha x 1 = x 1 :=
  rfl

/-- Field diagonalization of O'Meara's general plane. -/
noncomputable def omearaGeneralPlaneToFiniteDiagonalIsometry
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    Isometry
      (omearaGeneralPlane (alpha : K) beta hnondegenerate)
      (finiteDiagonal
        (omearaGeneralPlaneDiagonalCoefficients alpha beta)
        (omearaGeneralPlaneDiagonalCoefficients_ne_zero
          alpha beta hnondegenerate)) where
  toLinearEquiv := omearaGeneralPlaneOrthogonalizingLinearEquiv alpha
  map_bilin := by
    intro x y
    rw [finiteDiagonal_bilin_apply,
      omearaGeneralPlane_bilin_apply]
    simp only [Fin.sum_univ_two,
      omearaGeneralPlaneDiagonalCoefficients_zero,
      omearaGeneralPlaneDiagonalCoefficients_one,
      omearaGeneralPlaneOrthogonalizingLinearEquiv_zero,
      omearaGeneralPlaneOrthogonalizingLinearEquiv_one]
    field_simp [Units.ne_zero alpha]
    ring

/-- Unit-valued form of the two diagonalized coefficients. -/
noncomputable def omearaGeneralPlaneDiagonalUnits
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) : Fin 2 → Kˣ :=
  ![alpha, Units.mk0 (beta - (alpha : K)⁻¹)
    (omearaGeneralPlaneDiagonalTail_ne_zero alpha beta hnondegenerate)]

@[simp]
theorem omearaGeneralPlaneDiagonalUnits_zero
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    omearaGeneralPlaneDiagonalUnits alpha beta hnondegenerate 0 = alpha :=
  rfl

@[simp]
theorem omearaGeneralPlaneDiagonalUnits_one
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    (omearaGeneralPlaneDiagonalUnits alpha beta hnondegenerate 1 : K) =
      beta - (alpha : K)⁻¹ :=
  rfl

/-- The raw coefficient vector agrees with the coercions of the packaged
unit coefficients. -/
theorem omearaGeneralPlaneDiagonalCoefficients_eq_unitCoefficients
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    omearaGeneralPlaneDiagonalCoefficients alpha beta =
      diagonalUnitCoefficients
        (omearaGeneralPlaneDiagonalUnits alpha beta hnondegenerate) := by
  funext i
  fin_cases i <;> rfl

/-- Diagonalization with the target written in the project's standard
unit-coefficient notation. -/
noncomputable def omearaGeneralPlaneDiagonalUnitIsometry
    (alpha : Kˣ) (beta : K)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    Isometry
      (omearaGeneralPlane (alpha : K) beta hnondegenerate)
      (finiteDiagonal
        (diagonalUnitCoefficients
          (omearaGeneralPlaneDiagonalUnits alpha beta hnondegenerate))
        (fun i ↦ Units.ne_zero
          (omearaGeneralPlaneDiagonalUnits alpha beta hnondegenerate i))) := by
  simpa only [← omearaGeneralPlaneDiagonalCoefficients_eq_unitCoefficients]
    using omearaGeneralPlaneToFiniteDiagonalIsometry
      alpha beta hnondegenerate

end QuadraticSpace

end Bong
