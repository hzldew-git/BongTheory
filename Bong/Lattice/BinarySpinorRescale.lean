/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BinaryRotationReflection
import Bong.Lattice.FormRescale

/-!
# Binary spinor norms and rescaling the form

Multiplying a binary quadratic form by a nonzero scalar does not change its
proper integral spinor-norm image.  The proof uses the two-reflection
description: each reflection class acquires the same scalar, and the two
factors cancel modulo squares.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- Rescaling does not change the reflection map. -/
theorem reflectionLinearEquiv_rescaleUnit
    (a : Kˣ) {x : V} (hx : q.IsAnisotropic x) (y : V) :
    (q.rescaleUnit a).reflectionLinearEquiv x (hx.rescaleUnit a) y =
      q.reflectionLinearEquiv x hx y := by
  rw [reflectionLinearEquiv_apply, reflectionLinearEquiv_apply]
  simp only [rescaleUnit_bilin_apply, rescaleUnit_quadratic]
  congr 1
  field_simp [Units.ne_zero a, hx]

end QuadraticSpace

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A reflection is integral before rescaling exactly when it is integral
after rescaling. -/
theorem isIntegralReflection_rescaleUnit_iff
    (a : Kˣ) {x : V} (hx : q.IsAnisotropic x) :
    IsIntegralReflection (q := q.rescaleUnit a) (L := L)
        (hx.rescaleUnit a) ↔
      IsIntegralReflection (q := q) (L := L) hx := by
  constructor <;> intro h y hy
  · rw [← QuadraticSpace.reflectionLinearEquiv_rescaleUnit
      (q := q) a hx y]
    exact h y hy
  · rw [QuadraticSpace.reflectionLinearEquiv_rescaleUnit
      (q := q) a hx y]
    exact h y hy

/-- A reflection class acquires the square class of the rescaling factor. -/
theorem reflectionSpinorClass_rescaleUnit
    (a : Kˣ) {x : V} (hx : q.IsAnisotropic x) :
    reflectionSpinorClass (q := q.rescaleUnit a) (hx.rescaleUnit a) =
      squareClass K a * reflectionSpinorClass (q := q) hx := by
  unfold reflectionSpinorClass
  change squareClass K
      (Units.mk0 ((a : K) * q.quadratic x)
        (mul_ne_zero (Units.ne_zero a) hx)) =
    squareClass K a * squareClass K (Units.mk0 (q.quadratic x) hx)
  have hunit :
      Units.mk0 ((a : K) * q.quadratic x)
          (mul_ne_zero (Units.ne_zero a) hx) =
        a * Units.mk0 (q.quadratic x) hx := by
    apply Units.ext
    rfl
  rw [hunit]
  rfl

private theorem squareClass_mul_self (a : Kˣ) :
    squareClass K a * squareClass K a = 1 := by
  change squareClass K (a * a) = 1
  rw [show a * a = (1 : Kˣ) * a ^ 2 by simp [pow_two],
    squareClass_mul_square]
  rfl

/-- Binary proper spinor norms are invariant under a common rescaling of
the quadratic form. -/
theorem spinorNormImage_rescaleUnit_of_finrank_eq_two
    [FiniteDimensional K V] (a : Kˣ)
    (hfin : Module.finrank K V = 2) {x : V}
    (hx : q.IsAnisotropic x) (hxIntegral : IsIntegralReflection (L := L) hx) :
    spinorNormImage (q := q.rescaleUnit a) (L := L) =
      spinorNormImage (q := q) (L := L) := by
  let hxScaled := hx.rescaleUnit a
  have hxIntegralScaled :
      IsIntegralReflection (q := q.rescaleUnit a) (L := L) hxScaled :=
    (isIntegralReflection_rescaleUnit_iff a hx).2 hxIntegral
  rw [spinorNormImage_eq_fixed_mul_integralReflectionClasses
      (q := q.rescaleUnit a) hfin hxScaled hxIntegralScaled,
    spinorNormImage_eq_fixed_mul_integralReflectionClasses
      (q := q) hfin hx hxIntegral]
  ext c
  constructor
  · rintro ⟨y, hyScaled, hyIntegralScaled, hclass⟩
    have hy : q.IsAnisotropic y := by
      intro hyZero
      exact hyScaled (by
        rw [QuadraticSpace.rescaleUnit_quadratic, hyZero, mul_zero])
    have hyScaledEq : hy.rescaleUnit a = hyScaled := Subsingleton.elim _ _
    have hyIntegral : IsIntegralReflection (q := q) (L := L) hy := by
      apply (isIntegralReflection_rescaleUnit_iff a hy).1
      simpa only [hyScaledEq] using hyIntegralScaled
    refine ⟨y, hy, hyIntegral, ?_⟩
    have hxScaledEq : hxScaled = hx.rescaleUnit a := Subsingleton.elim _ _
    have hyScaledEq' : hyScaled = hy.rescaleUnit a := Subsingleton.elim _ _
    have hxClass :
        reflectionSpinorClass (q := q.rescaleUnit a) hxScaled =
          squareClass K a * reflectionSpinorClass (q := q) hx := by
      simpa only [hxScaledEq] using
        (reflectionSpinorClass_rescaleUnit (q := q) (x := x) a hx)
    have hyClass :
        reflectionSpinorClass (q := q.rescaleUnit a) hyScaled =
          squareClass K a * reflectionSpinorClass (q := q) hy := by
      simpa only [hyScaledEq'] using
        (reflectionSpinorClass_rescaleUnit (q := q) (x := y) a hy)
    have haa := squareClass_mul_self (K := K) a
    have hproduct :
        reflectionSpinorClass (q := q.rescaleUnit a) hxScaled *
            reflectionSpinorClass (q := q.rescaleUnit a) hyScaled =
          reflectionSpinorClass (q := q) hx *
            reflectionSpinorClass (q := q) hy := by
      rw [hxClass, hyClass]
      calc
      (squareClass K a * reflectionSpinorClass hx) *
          (squareClass K a * reflectionSpinorClass hy) =
          (squareClass K a * squareClass K a) *
            (reflectionSpinorClass hx * reflectionSpinorClass hy) := by
          ac_rfl
        _ = reflectionSpinorClass hx * reflectionSpinorClass hy := by
          rw [haa, one_mul]
    exact hproduct.symm.trans hclass
  · rintro ⟨y, hy, hyIntegral, hclass⟩
    let hyScaled := hy.rescaleUnit a
    have hyIntegralScaled :
        IsIntegralReflection (q := q.rescaleUnit a) (L := L) hyScaled :=
      (isIntegralReflection_rescaleUnit_iff a hy).2 hyIntegral
    refine ⟨y, hyScaled, hyIntegralScaled, ?_⟩
    have hxScaledEq : hxScaled = hx.rescaleUnit a := Subsingleton.elim _ _
    have hyScaledEq : hyScaled = hy.rescaleUnit a := Subsingleton.elim _ _
    have hxClass :
        reflectionSpinorClass (q := q.rescaleUnit a) hxScaled =
          squareClass K a * reflectionSpinorClass (q := q) hx := by
      simpa only [hxScaledEq] using
        (reflectionSpinorClass_rescaleUnit (q := q) (x := x) a hx)
    have hyClass :
        reflectionSpinorClass (q := q.rescaleUnit a) hyScaled =
          squareClass K a * reflectionSpinorClass (q := q) hy := by
      simpa only [hyScaledEq] using
        (reflectionSpinorClass_rescaleUnit (q := q) (x := y) a hy)
    have haa := squareClass_mul_self (K := K) a
    have hproduct :
        reflectionSpinorClass (q := q.rescaleUnit a) hxScaled *
            reflectionSpinorClass (q := q.rescaleUnit a) hyScaled =
          reflectionSpinorClass (q := q) hx *
            reflectionSpinorClass (q := q) hy := by
      rw [hxClass, hyClass]
      calc
      (squareClass K a * reflectionSpinorClass hx) *
          (squareClass K a * reflectionSpinorClass hy) =
          (squareClass K a * squareClass K a) *
            (reflectionSpinorClass hx * reflectionSpinorClass hy) := by
          ac_rfl
        _ = reflectionSpinorClass hx * reflectionSpinorClass hy := by
          rw [haa, one_mul]
    exact hproduct.trans hclass

end Lattice

end Bong
