/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.SpinorNormMultiplicative
import Bong.QuadraticSpace.BinaryImproperIsometry

/-!
# Binary integral rotations as products of two reflections

After fixing one integral reflection in a binary lattice, every proper
integral rotation is its product with a second integral reflection.  This
turns the binary spinor-norm calculation into a classification of integral
reflection vectors.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- With one integral reflection fixed, every binary integral rotation is a
product of that reflection and another integral reflection. -/
theorem IntegralRotation.exists_integralReflectionProduct_of_finrank_eq_two
    [FiniteDimensional K V] (f : IntegralRotation q L)
    (hfin : Module.finrank K V = 2) {x : V}
    (hx : q.IsAnisotropic x) (hxIntegral : IsIntegralReflection (L := L) hx) :
    ∃ (y : V) (hy : q.IsAnisotropic y)
      (hyIntegral : IsIntegralReflection (L := L) hy),
      f.toIntegralOrthogonalGroup =
        integralReflection hx hxIntegral *
          integralReflection hy hyIntegral := by
  let sx : IntegralOrthogonalGroup q L :=
    integralReflection hx hxIntegral
  let g : IntegralOrthogonalGroup q L :=
    sx * f.toIntegralOrthogonalGroup
  have hdetG : LinearEquiv.det g.toLinearEquiv = (-1 : Kˣ) := by
    change LinearEquiv.det
      (f.toIntegralOrthogonalGroup.toLinearEquiv.trans sx.toLinearEquiv) =
        (-1 : Kˣ)
    rw [LinearEquiv.det_trans, f.det_eq_one]
    change LinearEquiv.det sx.toLinearEquiv * 1 = (-1 : Kˣ)
    rw [show LinearEquiv.det sx.toLinearEquiv = (-1 : Kˣ) by
      exact det_integralReflection hx hxIntegral]
    simp
  obtain ⟨y, hy, hgy⟩ :=
    g.toQuadraticSpaceIsometry
      |>.exists_eq_reflection_of_det_neg_one_of_finrank_eq_two hfin hdetG
  have hyIntegral : IsIntegralReflection (L := L) hy := by
    intro z hz
    have hmap : g.toLinearEquiv z ∈ L := (g.map_mem z).1 hz
    have happ := congrArg
      (fun e : QuadraticSpace.Isometry q q => e.toLinearEquiv z) hgy
    change g.toLinearEquiv z = q.reflectionLinearEquiv y hy z at happ
    rw [← happ]
    exact hmap
  have hgyIntegral : g = integralReflection hy hyIntegral := by
    apply Isometry.ext
    intro z
    have happ := congrArg
      (fun e : QuadraticSpace.Isometry q q => e.toLinearEquiv z) hgy
    exact happ
  refine ⟨y, hy, hyIntegral, ?_⟩
  calc
    f.toIntegralOrthogonalGroup = 1 * f.toIntegralOrthogonalGroup := by simp
    _ = (sx * sx) * f.toIntegralOrthogonalGroup := by
      rw [integralReflection_mul_self hx hxIntegral]
    _ = sx * (sx * f.toIntegralOrthogonalGroup) := by
      rw [mul_assoc]
    _ = sx * g := rfl
    _ = integralReflection hx hxIntegral *
        integralReflection hy hyIntegral := by
      rw [hgyIntegral]

/-- Spinor norm of the preceding two-reflection factorization. -/
theorem IntegralRotation.exists_spinorNorm_eq_reflectionClasses_of_finrank_eq_two
    [FiniteDimensional K V] (f : IntegralRotation q L)
    (hfin : Module.finrank K V = 2) {x : V}
    (hx : q.IsAnisotropic x) (hxIntegral : IsIntegralReflection (L := L) hx) :
    ∃ (y : V) (hy : q.IsAnisotropic y)
      (hyIntegral : IsIntegralReflection (L := L) hy),
      f.spinorNorm =
        reflectionSpinorClass hx * reflectionSpinorClass hy := by
  obtain ⟨y, hy, hyIntegral, hfactor⟩ :=
    f.exists_integralReflectionProduct_of_finrank_eq_two
      hfin hx hxIntegral
  refine ⟨y, hy, hyIntegral, ?_⟩
  change integralSpinorNorm f.toIntegralOrthogonalGroup = _
  rw [hfactor, integralSpinorNorm_mul,
    integralSpinorNorm_integralReflection,
    integralSpinorNorm_integralReflection]

/-- The binary spinor image is exactly the fixed reflection class times the
classes of all integral reflections. -/
theorem spinorNormImage_eq_fixed_mul_integralReflectionClasses
    [FiniteDimensional K V] (hfin : Module.finrank K V = 2)
    {x : V} (hx : q.IsAnisotropic x)
    (hxIntegral : IsIntegralReflection (L := L) hx) :
    spinorNormImage (q := q) (L := L) =
      {a | ∃ (y : V) (hy : q.IsAnisotropic y)
        (hyIntegral : IsIntegralReflection (L := L) hy),
        reflectionSpinorClass hx * reflectionSpinorClass hy = a} := by
  ext a
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨y, hy, hyIntegral, hspinor⟩ :=
      f.exists_spinorNorm_eq_reflectionClasses_of_finrank_eq_two
        hfin hx hxIntegral
    exact ⟨y, hy, hyIntegral, hspinor.symm⟩
  · rintro ⟨y, hy, hyIntegral, rfl⟩
    let f := integralReflectionProduct hx hxIntegral hy hyIntegral
    refine ⟨f, ?_⟩
    change integralSpinorNorm
      (integralReflection hx hxIntegral *
        integralReflection hy hyIntegral) = _
    rw [integralSpinorNorm_mul,
      integralSpinorNorm_integralReflection,
      integralSpinorNorm_integralReflection]

end Lattice

end Bong
