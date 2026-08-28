/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Automorphism
import Bong.QuadraticSpace.Reflection

/-!
# Integral reflections of quadratic lattices

This file characterizes the basic integrality condition for a reflection and
packages an integral reflection as an element of the integral orthogonal
group.  These are the generators used in Beli's spinor-norm calculations.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

/-- A reflection is integral when it preserves the lattice. -/
def IsIntegralReflection (anisotropic : q.IsAnisotropic x) : Prop :=
  ∀ y : V, y ∈ L → q.reflectionLinearEquiv x anisotropic y ∈ L

/--
The usual coefficient test: if `x ∈ L` and every reflection coefficient is
integral, then reflection in `x` preserves `L`.
-/
theorem isIntegralReflection_of_coefficient_mem_integerRing
    (anisotropic : q.IsAnisotropic x) (hxL : x ∈ L)
    (hcoefficient : ∀ y : V, y ∈ L →
      2 * q.bilin x y / q.quadratic x ∈ IntegerRing K) :
    IsIntegralReflection (L := L) anisotropic := by
  intro y hy
  rw [q.reflectionLinearEquiv_apply]
  let c : IntegerRing K :=
    ⟨2 * q.bilin x y / q.quadratic x, hcoefficient y hy⟩
  have hcx := L.smul_mem c hxL
  change (2 * q.bilin x y / q.quadratic x) • x ∈ L at hcx
  exact L.sub_mem hy hcx

/-- Reflection in an anisotropic norm generator preserves the lattice.  This
is the integral-reflection observation used in Beli (2003), paragraph 3.12. -/
theorem IsNormGenerator.isIntegralReflection
    (generator : IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x) :
    IsIntegralReflection (L := L) anisotropic := by
  apply isIntegralReflection_of_coefficient_mem_integerRing
    anisotropic generator.mem
  intro y hy
  have hbilin := bilin_mem_scaleIdeal_of_mem q L generator.mem hy
  have htwo := two_smul_mem_normIdeal q L hbilin
  rw [generator.normIdeal_eq, principalIdeal,
    Submodule.mem_span_singleton] at htwo
  rcases htwo with ⟨c, hc⟩
  have hcoefficient :
      2 * q.bilin x y / q.quadratic x =
        algebraMap (IntegerRing K) K c := by
    rw [div_eq_iff anisotropic]
    simpa only [Algebra.smul_def, map_ofNat] using hc.symm
  rw [hcoefficient]
  convert c.property using 1
  exact ValuationSubring.algebraMap_apply (IntegerRing K) c

/-- An integral reflection as an element of the integral orthogonal group. -/
noncomputable def integralReflection (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (L := L) anisotropic) :
    IntegralOrthogonalGroup q L where
  toLinearEquiv := q.reflectionLinearEquiv x anisotropic
  map_bilin := (q.reflectionIsometry x anisotropic).map_bilin
  map_mem y := by
    constructor
    · exact integral y
    · intro hy
      have htwice := integral (q.reflectionLinearEquiv x anisotropic y) hy
      have hinvolutive := q.reflectionLinearEquiv_involutive x anisotropic y
      rw [hinvolutive] at htwice
      exact htwice

@[simp]
theorem integralReflection_apply (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (L := L) anisotropic) (y : V) :
    (integralReflection anisotropic integral).toLinearEquiv y =
      y - (2 * q.bilin x y / q.quadratic x) • x :=
  q.reflectionLinearEquiv_apply x anisotropic y

/-- Every integral reflection is an involution in the orthogonal group. -/
theorem integralReflection_mul_self (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (L := L) anisotropic) :
    integralReflection anisotropic integral *
      integralReflection anisotropic integral = 1 := by
  apply Isometry.ext
  intro y
  exact q.reflectionLinearEquiv_involutive x anisotropic y

/-- The determinant of an integral reflection is `-1`. -/
theorem det_integralReflection (anisotropic : q.IsAnisotropic x)
    (integral : IsIntegralReflection (L := L) anisotropic) :
    LinearEquiv.det (integralReflection anisotropic integral).toLinearEquiv =
      (-1 : Kˣ) := by
  letI : Module.Finite K V := L.moduleFinite
  exact q.det_reflectionLinearEquiv anisotropic

/-- The product of two integral reflections is an integral rotation. -/
noncomputable def integralReflectionProduct {y : V}
    (anisotropicX : q.IsAnisotropic x)
    (integralX : IsIntegralReflection (L := L) anisotropicX)
    (anisotropicY : q.IsAnisotropic y)
    (integralY : IsIntegralReflection (L := L) anisotropicY) :
    IntegralRotation q L where
  toIntegralOrthogonalGroup :=
    integralReflection anisotropicX integralX *
      integralReflection anisotropicY integralY
  det_eq_one := by
    letI : Module.Finite K V := L.moduleFinite
    change LinearEquiv.det
        ((integralReflection anisotropicY integralY).toLinearEquiv.trans
          (integralReflection anisotropicX integralX).toLinearEquiv) = 1
    rw [LinearEquiv.det_trans,
      det_integralReflection anisotropicX integralX,
      det_integralReflection anisotropicY integralY]
    norm_num

/-- The square class assigned to reflection in `x` by the spinor norm. -/
noncomputable def reflectionSpinorClass (anisotropic : q.IsAnisotropic x) :
    SquareClass K :=
  squareClass K (Units.mk0 (q.quadratic x) anisotropic)

/--
An integral reflection of the projected lattice remains integral after
extension to the original lattice.
-/
theorem isIntegralReflection_of_projectedLattice
    {z : q.vectorOrthogonal x} (generator : IsNormGenerator q L x)
    (anisotropicX : q.IsAnisotropic x)
    (anisotropicZ : (q.orthogonalSpace x anisotropicX).IsAnisotropic z)
    (integralZ : IsIntegralReflection
      (q := q.orthogonalSpace x anisotropicX)
      (L := projectedLattice q L x anisotropicX) anisotropicZ) :
    IsIntegralReflection (q := q) (L := L) (x := (z : V)) anisotropicZ := by
  let tailReflection : IntegralOrthogonalGroup
      (q.orthogonalSpace x anisotropicX)
      (projectedLattice q L x anisotropicX) :=
    integralReflection anisotropicZ integralZ
  let extended := tailReflection.extendProjectedAutomorphism generator
  intro y hy
  have hyExtended : extended.toLinearEquiv y ∈ L :=
    (extended.map_mem y).1 hy
  have heq := congrArg
    (fun f : QuadraticSpace.Isometry q q => f.toLinearEquiv y)
    (q.orthogonalExtensionIsometry_reflection
      x anisotropicX z anisotropicZ)
  change extended.toLinearEquiv y =
    q.reflectionLinearEquiv (z : V) anisotropicZ y at heq
  rw [← heq]
  exact hyExtended

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- A tail reflection and its ambient extension have the same spinor class. -/
lemma reflectionSpinorClass_projectedLattice
    (anisotropicX : q.IsAnisotropic x) (z : q.vectorOrthogonal x)
    (anisotropicZ : (q.orthogonalSpace x anisotropicX).IsAnisotropic z) :
    reflectionSpinorClass
        (q := q.orthogonalSpace x anisotropicX) anisotropicZ =
      reflectionSpinorClass (q := q) (x := (z : V)) anisotropicZ :=
  rfl

end Lattice

end Bong
