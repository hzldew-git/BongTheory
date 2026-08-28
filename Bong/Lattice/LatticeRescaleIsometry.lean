/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.Lattice.Modular

/-!
# Scalar multiplication and lattice rescaling

Scalar multiplication by `a` identifies a lattice with its rescaling by
`a`; on the source quadratic space the form is multiplied by `a²`.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Multiplication by a nonzero field scalar as a linear automorphism. -/
noncomputable def scalarMultiplicationLinearEquiv (a : Kˣ) : V ≃ₗ[K] V where
  toFun x := (a : K) • x
  invFun x := ((a⁻¹ : Kˣ) : K) • x
  left_inv x := by
    simp only [smul_smul, Units.val_inv_eq_inv_val]
    rw [inv_mul_cancel₀ (Units.ne_zero a), one_smul]
  right_inv x := by
    simp only [smul_smul, Units.val_inv_eq_inv_val]
    rw [mul_inv_cancel₀ (Units.ne_zero a), one_smul]
  map_add' x y := smul_add (a : K) x y
  map_smul' c x := by
    simp [smul_smul, mul_comm]

@[simp]
theorem scalarMultiplicationLinearEquiv_apply (a : Kˣ) (x : V) :
    scalarMultiplicationLinearEquiv (V := V) a x = (a : K) • x :=
  rfl

/-- Rescaling a lattice by `a` is integrally isometric to retaining the
lattice and multiplying the quadratic form by `a²`. -/
noncomputable def scalarMultiplicationRescaleLatticeIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) :
    Isometry (q.rescaleUnit (a ^ 2)) q L (rescale a L) where
  toLinearEquiv := scalarMultiplicationLinearEquiv a
  map_bilin := by
    intro x y
    simp only [scalarMultiplicationLinearEquiv_apply,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      QuadraticSpace.rescaleUnit_bilin_apply, Units.val_mul, pow_two]
    ring
  map_mem := by
    intro x
    rw [mem_rescale_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      change (a : K) • y = (a : K) • x at hxy
      have h := congrArg
        (fun z : V => ((a⁻¹ : Kˣ) : K) • z) hxy
      have hyx : y = x := by
        simpa only [smul_smul, Units.val_inv_eq_inv_val,
          inv_mul_cancel₀ (Units.ne_zero a), one_smul] using h
      rwa [hyx] at hy

end Lattice

end Bong
