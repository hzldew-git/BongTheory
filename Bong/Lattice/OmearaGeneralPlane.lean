/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaChangeOfComplement

/-!
# O'Meara's general binary plane `A(alpha,beta)`

The earlier cancellation development only needed `A(alpha,0)`.  Proposition
93:19 and the proof of Theorem 93:28 use both diagonal coefficients.  This
file supplies that exact coordinate model together with the elementary swap
and diagonal changes of basis.  The hypothesis `alpha * beta != 1` is exactly
nondegeneracy of the Gram matrix.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K]

/-- The Gram matrix of O'Meara's binary lattice `A(alpha,beta)`. -/
def omearaGeneralPlaneMatrix (alpha beta : K) : Matrix (Fin 2) (Fin 2) K :=
  !![alpha, 1; 1, beta]

@[simp]
theorem omearaGeneralPlaneMatrix_zero_zero (alpha beta : K) :
    omearaGeneralPlaneMatrix alpha beta 0 0 = alpha :=
  rfl

@[simp]
theorem omearaGeneralPlaneMatrix_zero_one (alpha beta : K) :
    omearaGeneralPlaneMatrix alpha beta 0 1 = 1 :=
  rfl

@[simp]
theorem omearaGeneralPlaneMatrix_one_zero (alpha beta : K) :
    omearaGeneralPlaneMatrix alpha beta 1 0 = 1 :=
  rfl

@[simp]
theorem omearaGeneralPlaneMatrix_one_one (alpha beta : K) :
    omearaGeneralPlaneMatrix alpha beta 1 1 = beta :=
  rfl

theorem omearaGeneralPlaneMatrix_isSymm (alpha beta : K) :
    (omearaGeneralPlaneMatrix alpha beta).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem omearaGeneralPlaneMatrix_det (alpha beta : K) :
    (omearaGeneralPlaneMatrix alpha beta).det = alpha * beta - 1 := by
  simp [omearaGeneralPlaneMatrix, Matrix.det_fin_two_of]

/-- The nondegenerate binary quadratic space with Gram matrix
`[[alpha,1],[1,beta]]`. -/
noncomputable def omearaGeneralPlane (alpha beta : K)
    (hnondegenerate : alpha * beta ≠ 1) :
    QuadraticSpace K (Fin 2 → K) where
  bilin := Matrix.toBilin' (omearaGeneralPlaneMatrix alpha beta)
  isSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2
    (omearaGeneralPlaneMatrix_isSymm alpha beta)
  nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (omearaGeneralPlaneMatrix alpha beta) (by
        rw [omearaGeneralPlaneMatrix_det]
        exact sub_ne_zero.mpr hnondegenerate)

/-- Coordinate formula for `A(alpha,beta)`. -/
theorem omearaGeneralPlane_bilin_apply
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (x y : Fin 2 → K) :
    (omearaGeneralPlane alpha beta hnondegenerate).bilin x y =
      alpha * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 +
        beta * x 1 * y 1 := by
  rw [omearaGeneralPlane, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two, omearaGeneralPlaneMatrix_zero_zero,
    omearaGeneralPlaneMatrix_zero_one,
    omearaGeneralPlaneMatrix_one_zero,
    omearaGeneralPlaneMatrix_one_one]
  ring

/-- `A(alpha,0)` in the general notation is the earlier one-parameter
O'Meara plane. -/
noncomputable def omearaGeneralPlaneZeroRightIsometry (alpha : K) :
    Isometry (omearaGeneralPlane alpha 0 (by simp)) (omearaPlane alpha) where
  toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
  map_bilin x y := by
    rw [omearaGeneralPlane_bilin_apply, omearaPlane_bilin_apply]
    simp

/-- Exchange the two displayed basis vectors of a general O'Meara plane. -/
noncomputable def omearaGeneralPlaneSwapIsometry
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1) :
    Isometry
      (omearaGeneralPlane alpha beta hnondegenerate)
      (omearaGeneralPlane beta alpha (by
        rwa [mul_comm])) where
  toLinearEquiv :=
    { toFun := fun x ↦ ![x 1, x 0]
      invFun := fun x ↦ ![x 1, x 0]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }
  map_bilin x y := by
    rw [omearaGeneralPlane_bilin_apply,
      omearaGeneralPlane_bilin_apply]
    simp
    ring

/-- Diagonal change of basis `(x,y) |-> (u*x,u^-1*y)` in a general
O'Meara plane. -/
noncomputable def omearaGeneralPlaneDiagonalIsometry
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1) (u : Kˣ) :
    Isometry
      (omearaGeneralPlane alpha beta hnondegenerate)
      (omearaGeneralPlane
        ((u : K) ^ 2 * alpha) (((u : K)⁻¹) ^ 2 * beta) (by
          intro h
          apply hnondegenerate
          have hu : (u : K) ≠ 0 := Units.ne_zero u
          calc
            alpha * beta =
                (((u : K) ^ 2 * alpha) * (((u : K)⁻¹) ^ 2 * beta)) := by
              field_simp
            _ = 1 := h)) where
  toLinearEquiv :=
    { toFun := fun x ↦ ![(u : K)⁻¹ * x 0, (u : K) * x 1]
      invFun := fun x ↦ ![(u : K) * x 0, (u : K)⁻¹ * x 1]
      left_inv := by
        intro x
        funext i
        fin_cases i <;> simp [Units.ne_zero u]
      right_inv := by
        intro x
        funext i
        fin_cases i <;> simp [Units.ne_zero u]
      map_add' := by intro x y; funext i; fin_cases i <;> simp [mul_add]
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc] }
  map_bilin x y := by
    rw [omearaGeneralPlane_bilin_apply,
      omearaGeneralPlane_bilin_apply]
    simp
    field_simp [Units.ne_zero u]

end QuadraticSpace

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The basis swap is integral on the standard binary lattice. -/
noncomputable def omearaGeneralPlaneSwapLatticeIsometry
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate)
      (QuadraticSpace.omearaGeneralPlane beta alpha (by rwa [mul_comm]))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv :=
    (QuadraticSpace.omearaGeneralPlaneSwapIsometry
      alpha beta hnondegenerate).toLinearEquiv
  map_bilin :=
    (QuadraticSpace.omearaGeneralPlaneSwapIsometry
      alpha beta hnondegenerate).map_bilin
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    exact and_comm

/-- A valuation-unit diagonal change of basis is integral on the standard
binary lattice. -/
noncomputable def omearaGeneralPlaneDiagonalLatticeIsometry
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate)
      (QuadraticSpace.omearaGeneralPlane
        ((u : K) ^ 2 * alpha) (((u : K)⁻¹) ^ 2 * beta) (by
          intro h
          apply hnondegenerate
          have hune : (u : K) ≠ 0 := Units.ne_zero u
          calc
            alpha * beta =
                (((u : K) ^ 2 * alpha) * (((u : K)⁻¹) ^ 2 * beta)) := by
              field_simp
            _ = 1 := h))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv :=
    (QuadraticSpace.omearaGeneralPlaneDiagonalIsometry
      alpha beta hnondegenerate u).toLinearEquiv
  map_bilin :=
    (QuadraticSpace.omearaGeneralPlaneDiagonalIsometry
      alpha beta hnondegenerate u).map_bilin
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hx0, hx1⟩
      have huInv : IsValuationUnit K ((u : K)⁻¹) := by
        simpa [IsValuationUnit, AddValuation.map_inv, hu]
      have huInvMem : (u : K)⁻¹ ∈ IntegerRing K :=
        (mem_integerRing_iff K).2 huInv.ge
      have huMem : (u : K) ∈ IntegerRing K :=
        (mem_integerRing_iff K).2 hu.ge
      exact ⟨(IntegerRing K).toSubring.mul_mem
          huInvMem hx0,
        (IntegerRing K).toSubring.mul_mem huMem hx1⟩
    · rintro ⟨hx0, hx1⟩
      have huInv : IsValuationUnit K ((u : K)⁻¹) := by
        simpa [IsValuationUnit, AddValuation.map_inv, hu]
      have huInvMem : (u : K)⁻¹ ∈ IntegerRing K :=
        (mem_integerRing_iff K).2 huInv.ge
      have huMem : (u : K) ∈ IntegerRing K :=
        (mem_integerRing_iff K).2 hu.ge
      have hfirst : x 0 = (u : K) * ((u : K)⁻¹ * x 0) := by
        field_simp [Units.ne_zero u]
      have hsecond : x 1 = (u : K)⁻¹ * ((u : K) * x 1) := by
        field_simp [Units.ne_zero u]
      rw [hfirst, hsecond]
      exact ⟨(IntegerRing K).toSubring.mul_mem huMem hx0,
        (IntegerRing K).toSubring.mul_mem huInvMem hx1⟩

end Lattice

end Bong
