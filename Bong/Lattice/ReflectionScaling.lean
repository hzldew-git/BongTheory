/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.PrimitiveVector
import Bong.Lattice.Reflection

/-!
# Scaling reflection vectors

A nonzero scalar multiple defines the same reflection hyperplane.  Its
quadratic value changes by a square, so its reflection spinor class is also
unchanged.  These facts allow every integral reflection to be represented by
a primitive lattice vector before applying coordinate criteria.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {x : V}

/-- A nonzero scalar multiple of an anisotropic vector is anisotropic. -/
theorem IsAnisotropic.unit_smul (hx : q.IsAnisotropic x) (a : Kˣ) :
    q.IsAnisotropic ((a : K) • x) := by
  rw [IsAnisotropic, q.quadratic_smul]
  exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero a)) hx

/-- Rescaling the defining vector does not change its reflection. -/
theorem reflectionLinearEquiv_unit_smul
    (a : Kˣ) (hx : q.IsAnisotropic x) (y : V) :
    q.reflectionLinearEquiv ((a : K) • x) (hx.unit_smul a) y =
      q.reflectionLinearEquiv x hx y := by
  rw [reflectionLinearEquiv_apply, reflectionLinearEquiv_apply,
    LinearMap.BilinForm.smul_left, q.quadratic_smul, smul_smul]
  congr 1
  field_simp [Units.ne_zero a, hx]

end QuadraticSpace

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

/-- Integrality of a reflection depends only on its anisotropic line. -/
theorem isIntegralReflection_unit_smul_iff
    (a : Kˣ) (hx : q.IsAnisotropic x) :
    IsIntegralReflection (L := L) (hx.unit_smul a) ↔
      IsIntegralReflection (L := L) hx := by
  constructor <;> intro h y hy
  · rw [← QuadraticSpace.reflectionLinearEquiv_unit_smul a hx y]
    exact h y hy
  · rw [QuadraticSpace.reflectionLinearEquiv_unit_smul a hx y]
    exact h y hy

/-- Rescaling a reflection vector does not change its spinor square class. -/
theorem reflectionSpinorClass_unit_smul
    (a : Kˣ) (hx : q.IsAnisotropic x) :
    reflectionSpinorClass (q := q) (hx.unit_smul a) =
      reflectionSpinorClass (q := q) hx := by
  unfold reflectionSpinorClass
  have hunit :
      Units.mk0 (q.quadratic ((a : K) • x)) (hx.unit_smul a) =
        Units.mk0 (q.quadratic x) hx * a ^ 2 := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul,
      Units.val_pow_eq_pow_val, q.quadratic_smul]
    ring
  rw [hunit, squareClass_mul_square]

end Lattice

end Bong
