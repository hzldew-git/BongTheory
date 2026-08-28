/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Reflection
import Bong.QuadraticSpace.SpinorNorm

/-!
# Spinor norm of a reflection

This file computes the residual space and Wall form of a reflection and proves
the normalization `theta(tau_x) = [Q(x)]`.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {x : V}

/-- The residual endomorphism of a reflection has image on its defining line. -/
theorem residualLinearMap_reflection_apply (anisotropic : q.IsAnisotropic x)
    (y : V) :
    residualLinearMap (q.reflectionIsometry x anisotropic) y =
      (2 * q.bilin x y / q.quadratic x) • x := by
  rw [residualLinearMap_apply, reflectionIsometry,
    reflectionLinearEquiv_apply]
  abel

/-- The residual space of reflection in `x` is exactly `K x`. -/
theorem residualSpace_reflection_eq_span (anisotropic : q.IsAnisotropic x) :
    residualSpace (q.reflectionIsometry x anisotropic) = K ∙ x := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    rw [residualLinearMap_reflection_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · apply Submodule.span_le.2
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have htwoX : (2 : K) • x ∈
        residualSpace (q.reflectionIsometry x anisotropic) := by
      refine ⟨x, ?_⟩
      rw [residualLinearMap_reflection_apply]
      change (2 * q.quadratic x / q.quadratic x) • x = (2 : K) • x
      rw [mul_div_cancel_right₀ _ anisotropic]
    have hinv := (residualSpace
      (q.reflectionIsometry x anisotropic)).smul_mem (2 : K)⁻¹ htwoX
    convert hinv using 1
    rw [← mul_smul]
    simp

/-- The residual space of a reflection has dimension one. -/
theorem finrank_residualSpace_reflection [FiniteDimensional K V]
    (anisotropic : q.IsAnisotropic x) :
    Module.finrank K
      (residualSpace (q.reflectionIsometry x anisotropic)) = 1 := by
  rw [residualSpace_reflection_eq_span anisotropic]
  exact finrank_span_singleton anisotropic.ne_zero

/-- The canonical residual vector `(1 - tau_x)x`. -/
noncomputable def reflectionResidualVector (anisotropic : q.IsAnisotropic x) :
    residualSpace (q.reflectionIsometry x anisotropic) :=
  residualMap (q.reflectionIsometry x anisotropic) x

@[simp]
theorem coe_reflectionResidualVector (anisotropic : q.IsAnisotropic x) :
    (reflectionResidualVector anisotropic : V) = (2 : K) • x := by
  rw [reflectionResidualVector, residualMap_coe, reflectionIsometry,
    reflectionLinearEquiv_apply_self]
  simp [two_smul]

/-- The canonical residual vector of a reflection is nonzero. -/
theorem reflectionResidualVector_ne_zero (anisotropic : q.IsAnisotropic x) :
    reflectionResidualVector anisotropic ≠ 0 := by
  intro hzero
  have hcoe := congrArg
    (fun y : residualSpace (q.reflectionIsometry x anisotropic) => (y : V))
    hzero
  rw [coe_reflectionResidualVector] at hcoe
  simp only [Submodule.coe_zero] at hcoe
  have htwo : (2 : K) ≠ 0 := by norm_num
  exact anisotropic.ne_zero ((smul_eq_zero.mp hcoe).resolve_left htwo)

/-- The Wall value on `(1 - tau_x)x` is `4 Q(x)`. -/
theorem wallForm_reflectionResidualVector_self
    (anisotropic : q.IsAnisotropic x) :
    wallForm (q.reflectionIsometry x anisotropic)
        (reflectionResidualVector anisotropic)
        (reflectionResidualVector anisotropic) =
      4 * q.quadratic x := by
  change wallForm (q.reflectionIsometry x anisotropic)
      (residualMap (q.reflectionIsometry x anisotropic) x)
      (reflectionResidualVector anisotropic) = 4 * q.quadratic x
  rw [wallForm_residualMap_left, coe_reflectionResidualVector]
  simp only [LinearMap.BilinForm.smul_right]
  change 2 * (2 * q.quadratic x) = 4 * q.quadratic x
  ring

/-- The Wall spinor norm has the standard reflection normalization. -/
theorem spinorNorm_reflection [FiniteDimensional K V]
    (anisotropic : q.IsAnisotropic x) :
    spinorNorm (q.reflectionIsometry x anisotropic) =
      squareClass K (Units.mk0 (q.quadratic x) anisotropic) := by
  let f := q.reflectionIsometry x anisotropic
  let R := residualSpace f
  have hfin : Module.finrank K R = 1 :=
    finrank_residualSpace_reflection anisotropic
  letI : Unique (Fin (Module.finrank K R)) := by
    rw [hfin]
    infer_instance
  let v : R := reflectionResidualVector anisotropic
  have hv : v ≠ 0 := reflectionResidualVector_ne_zero anisotropic
  let b : Module.Basis (Fin (Module.finrank K R)) K R :=
    FiniteDimensional.basisSingleton
      (Fin (Module.finrank K R)) hfin v hv
  have hdet :
      Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)) =
        4 * q.quadratic x := by
    rw [Matrix.det_unique]
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show b default = v from FiniteDimensional.basisSingleton_apply
      (Fin (Module.finrank K R)) hfin v hv default]
    exact wallForm_reflectionResidualVector_self anisotropic
  let a : Kˣ := Units.mk0 (q.quadratic x) anisotropic
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have hu :
      Units.mk0
          (Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)))
          ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1
            (wallForm_nondegenerate f)) =
        a * two ^ 2 := by
    apply Units.ext
    change Matrix.det (LinearMap.BilinForm.toMatrix b (wallForm f)) =
      q.quadratic x * 2 ^ 2
    exact hdet.trans (by ring)
  rw [spinorNorm_eq_basisDeterminant f b, hu]
  exact squareClass_mul_square K a two

end QuadraticSpace

end Bong
