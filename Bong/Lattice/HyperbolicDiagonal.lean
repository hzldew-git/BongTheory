/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaChangeOfComplement
import Mathlib.LinearAlgebra.Determinant

/-!
# Integral diagonal automorphisms of a scaled hyperbolic plane

The map `(x,y) ↦ (t x,t⁻¹ y)` preserves every scalar multiple of the
standard hyperbolic form.  If `t` is a valuation unit, it also preserves the
standard rank-two lattice.  Its determinant is one.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The hyperbolic diagonal map `(x,y) ↦ (tx,t⁻¹y)`. -/
noncomputable def hyperbolicDiagonalLinearEquiv (t : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![(t : K) * x 0, ((t⁻¹ : Kˣ) : K) * x 1]
  invFun x := ![((t⁻¹ : Kˣ) : K) * x 0, (t : K) * x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  right_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem hyperbolicDiagonalLinearEquiv_zero (t : Kˣ) (x : Fin 2 → K) :
    hyperbolicDiagonalLinearEquiv t x 0 = (t : K) * x 0 :=
  rfl

@[simp]
theorem hyperbolicDiagonalLinearEquiv_one (t : Kˣ) (x : Fin 2 → K) :
    hyperbolicDiagonalLinearEquiv t x 1 = ((t⁻¹ : Kˣ) : K) * x 1 :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- A hyperbolic diagonal map has determinant one. -/
theorem det_hyperbolicDiagonalLinearEquiv (t : Kˣ) :
    LinearEquiv.det (hyperbolicDiagonalLinearEquiv t) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  let A := LinearMap.toMatrix' (hyperbolicDiagonalLinearEquiv t).toLinearMap
  have hA : A = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, hyperbolicDiagonalLinearEquiv]
  change A.det = 1
  rw [hA]
  simp [Matrix.det_fin_two_of, Units.ne_zero]

/-- Hyperbolic diagonal scaling preserves every scaled hyperbolic form. -/
noncomputable def hyperbolicDiagonalIsometry (s t : Kˣ) :
    QuadraticSpace.Isometry
      (QuadraticSpace.hyperbolicPlane s)
      (QuadraticSpace.hyperbolicPlane s) where
  toLinearEquiv := hyperbolicDiagonalLinearEquiv t
  map_bilin x y := by
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    change (s : K) *
        (((t : K) * x 0) * (((t⁻¹ : Kˣ) : K) * y 1) +
          (((t⁻¹ : Kˣ) : K) * x 1) * ((t : K) * y 0)) = _
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero t]

/-- If the diagonal multiplier is a valuation unit, the preceding isometry
also preserves the standard lattice. -/
noncomputable def scaledHyperbolicDiagonalLatticeIsometry
    (s t : Kˣ) (ht : IsValuationUnit K (t : K)) :
    Isometry
      (QuadraticSpace.hyperbolicPlane s)
      (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := hyperbolicDiagonalLinearEquiv t
  map_bilin := (hyperbolicDiagonalIsometry s t).map_bilin
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff,
      mem_omearaPlaneLattice_iff]
    have htMem : (t : K) ∈ IntegerRing K :=
      (mem_integerRing_iff K).2 ht.ge
    have htInv : IsValuationUnit K ((t⁻¹ : Kˣ) : K) := by
      simpa [IsValuationUnit, AddValuation.map_inv, ht]
    have htInvMem : ((t⁻¹ : Kˣ) : K) ∈ IntegerRing K :=
      (mem_integerRing_iff K).2 htInv.ge
    constructor
    · rintro ⟨hzero, hone⟩
      exact ⟨(IntegerRing K).mul_mem _ _ htMem hzero,
        (IntegerRing K).mul_mem _ _ htInvMem hone⟩
    · rintro ⟨hzero, hone⟩
      constructor
      · have h := (IntegerRing K).mul_mem _ _ htInvMem hzero
        change ((t⁻¹ : Kˣ) : K) * ((t : K) * x 0) ∈ IntegerRing K at h
        simpa [Units.ne_zero] using h
      · have h := (IntegerRing K).mul_mem _ _ htMem hone
        change (t : K) * (((t⁻¹ : Kˣ) : K) * x 1) ∈ IntegerRing K at h
        simpa [Units.ne_zero] using h

end Lattice

end Bong
