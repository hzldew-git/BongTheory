/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Transporter
import Mathlib.LinearAlgebra.Determinant

/-!
# Integral orthogonal groups and projected embeddings

This file packages integral lattice automorphisms as a group and proves the
group embedding in Beli (2003), Section 2.5.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The integral orthogonal group of a quadratic lattice. -/
abbrev IntegralOrthogonalGroup (q : QuadraticSpace K V) (L : Lattice K V) :=
  Isometry q q L L

namespace IntegralOrthogonalGroup

variable {q : QuadraticSpace K V} {L : Lattice K V}

instance : Group (IntegralOrthogonalGroup q L) where
  one := Isometry.refl q L
  mul f g := g.trans f
  inv := Isometry.symm
  mul_assoc f g h := by
    apply Isometry.ext
    intro x
    rfl
  one_mul f := by
    apply Isometry.ext
    intro x
    rfl
  mul_one f := by
    apply Isometry.ext
    intro x
    rfl
  inv_mul_cancel f := by
    apply Isometry.ext
    intro x
    exact f.toLinearEquiv.symm_apply_apply x

@[simp]
theorem one_toLinearEquiv_apply (x : V) :
    (1 : IntegralOrthogonalGroup q L).toLinearEquiv x = x :=
  rfl

@[simp]
theorem mul_toLinearEquiv_apply
    (f g : IntegralOrthogonalGroup q L) (x : V) :
    (f * g).toLinearEquiv x = f.toLinearEquiv (g.toLinearEquiv x) :=
  rfl

@[simp]
theorem inv_toLinearEquiv_apply (f : IntegralOrthogonalGroup q L) (x : V) :
    f⁻¹.toLinearEquiv x = f.toLinearEquiv.symm x :=
  rfl

end IntegralOrthogonalGroup

/-- The integral proper orthogonal group `O⁺(L)`: integral orthogonal
transformations with determinant one.  Beli's integral spinor-norm group is
the image of this group, not of the full orthogonal group. -/
structure IntegralRotation (q : QuadraticSpace K V) (L : Lattice K V) where
  /-- The underlying integral orthogonal transformation. -/
  toIntegralOrthogonalGroup : IntegralOrthogonalGroup q L
  /-- Properness. -/
  det_eq_one :
    LinearEquiv.det toIntegralOrthogonalGroup.toLinearEquiv = 1

namespace IntegralRotation

variable {q : QuadraticSpace K V} {L : Lattice K V}

@[ext]
theorem ext (f g : IntegralRotation q L)
    (h : f.toIntegralOrthogonalGroup = g.toIntegralOrthogonalGroup) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Group (IntegralRotation q L) where
  one := ⟨1, by exact LinearEquiv.det_refl⟩
  mul f g := ⟨f.toIntegralOrthogonalGroup * g.toIntegralOrthogonalGroup, by
    change LinearEquiv.det
        (g.toIntegralOrthogonalGroup.toLinearEquiv.trans
          f.toIntegralOrthogonalGroup.toLinearEquiv) = 1
    rw [LinearEquiv.det_trans, f.det_eq_one, g.det_eq_one, one_mul]⟩
  inv f := ⟨f.toIntegralOrthogonalGroup⁻¹, by
    change LinearEquiv.det
        (f.toIntegralOrthogonalGroup.toLinearEquiv⁻¹) = 1
    rw [map_inv, f.det_eq_one, inv_one]⟩
  mul_assoc f g h := by
    apply ext
    exact mul_assoc _ _ _
  one_mul f := by
    apply ext
    exact one_mul _
  mul_one f := by
    apply ext
    exact mul_one _
  inv_mul_cancel f := by
    apply ext
    exact inv_mul_cancel f.toIntegralOrthogonalGroup

@[simp]
theorem one_toIntegralOrthogonalGroup :
    (1 : IntegralRotation q L).toIntegralOrthogonalGroup = 1 :=
  rfl

@[simp]
theorem mul_toIntegralOrthogonalGroup (f g : IntegralRotation q L) :
    (f * g).toIntegralOrthogonalGroup =
      f.toIntegralOrthogonalGroup * g.toIntegralOrthogonalGroup :=
  rfl

@[simp]
theorem inv_toIntegralOrthogonalGroup (f : IntegralRotation q L) :
    f⁻¹.toIntegralOrthogonalGroup = f.toIntegralOrthogonalGroup⁻¹ :=
  rfl

/-- Application of an integral rotation to an ambient vector. -/
def apply (f : IntegralRotation q L) (x : V) : V :=
  f.toIntegralOrthogonalGroup.toLinearEquiv x

/-- An integral rotation preserves the quadratic form. -/
theorem quadratic_apply (f : IntegralRotation q L) (x : V) :
    q.quadratic (f.apply x) = q.quadratic x :=
  f.toIntegralOrthogonalGroup.map_quadratic x

/-- An integral rotation preserves the lattice. -/
theorem apply_mem (f : IntegralRotation q L) {x : V} (hx : x ∈ L) :
    f.apply x ∈ L :=
  (f.toIntegralOrthogonalGroup.map_mem x).1 hx

end IntegralRotation

variable {q : QuadraticSpace K V} {L : Lattice K V} {x : V}
  {anisotropic : q.IsAnisotropic x}

/-- Extension of projected automorphisms respects the identity. -/
theorem extendProjectedAutomorphism_one
    (generator : IsNormGenerator q L x) :
    Isometry.extendProjectedAutomorphism generator
        (1 : IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
          (projectedLattice q L x anisotropic)) =
      (1 : IntegralOrthogonalGroup q L) := by
  apply Isometry.ext
  intro y
  change QuadraticSpace.orthogonalExtensionLinearEquiv
      (QuadraticSpace.Isometry.refl (q.orthogonalSpace x anisotropic)) y = y
  rw [QuadraticSpace.orthogonalExtensionLinearEquiv_apply,
    QuadraticSpace.orthogonalExtensionLinearMap_apply]
  simp only [QuadraticSpace.Isometry.refl, LinearEquiv.refl_apply]
  simpa only [QuadraticSpace.lineProjection_apply,
    QuadraticSpace.projectionToOrthogonal_coe] using
      q.lineProjection_add_orthogonalProjection x y

/-- Extension of projected automorphisms respects composition. -/
theorem extendProjectedAutomorphism_mul
    (generator : IsNormGenerator q L x)
    (f g : IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    Isometry.extendProjectedAutomorphism generator (f * g) =
      Isometry.extendProjectedAutomorphism generator f *
        Isometry.extendProjectedAutomorphism generator g := by
  apply Isometry.ext
  intro y
  change QuadraticSpace.orthogonalExtensionLinearEquiv
      (g.toQuadraticSpaceIsometry.trans f.toQuadraticSpaceIsometry) y =
    QuadraticSpace.orthogonalExtensionLinearEquiv f.toQuadraticSpaceIsometry
      (QuadraticSpace.orthogonalExtensionLinearEquiv
        g.toQuadraticSpaceIsometry y)
  rw [QuadraticSpace.orthogonalExtensionLinearEquiv_apply,
    QuadraticSpace.orthogonalExtensionLinearMap_apply]
  rw [QuadraticSpace.orthogonalExtensionLinearEquiv_apply,
    QuadraticSpace.orthogonalExtensionLinearMap_apply]
  have hbilin := QuadraticSpace.bilin_orthogonalExtensionLinearMap
    g.toQuadraticSpaceIsometry y
  change q.bilin x
      (QuadraticSpace.orthogonalExtensionLinearEquiv
        g.toQuadraticSpaceIsometry y) = q.bilin x y at hbilin
  rw [hbilin]
  have hprojection :=
    QuadraticSpace.projectionToOrthogonal_orthogonalExtensionLinearEquiv
      g.toQuadraticSpaceIsometry y
  rw [hprojection]
  rfl

/-- The group homomorphism `O(pr_(x^⊥) L) → O(L)` from Beli's Section 2.5. -/
noncomputable def projectedAutomorphismHom
    (generator : IsNormGenerator q L x) :
    IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
        (projectedLattice q L x anisotropic) →*
      IntegralOrthogonalGroup q L where
  toFun f := f.extendProjectedAutomorphism generator
  map_one' := extendProjectedAutomorphism_one generator
  map_mul' := extendProjectedAutomorphism_mul generator

@[simp]
theorem projectedAutomorphismHom_apply
    (generator : IsNormGenerator q L x)
    (f : IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    projectedAutomorphismHom generator f =
      f.extendProjectedAutomorphism generator :=
  rfl

/-- The projected-automorphism homomorphism is injective. -/
theorem projectedAutomorphismHom_injective
    (generator : IsNormGenerator q L x) :
    Function.Injective
      (projectedAutomorphismHom (anisotropic := anisotropic) generator) := by
  intro f g hfg
  apply Isometry.ext f g
  intro y
  apply Subtype.ext
  have happ := congrArg
    (fun h : IntegralOrthogonalGroup q L =>
      q.projectionToOrthogonal x anisotropic (h.toLinearEquiv (y : V))) hfg
  rw [projectedAutomorphismHom_apply,
    projectedAutomorphismHom_apply] at happ
  rw [f.projection_extendProjectedAutomorphism generator,
    g.projection_extendProjectedAutomorphism generator] at happ
  have hy : q.projectionToOrthogonal x anisotropic (y : V) = y := by
    apply Subtype.ext
    exact q.orthogonalProjection_eq_self y.property
  simpa only [hy] using congrArg Subtype.val happ

namespace IntegralRotation

/-- Extending a rotation of the projected lattice by the identity on the
norm-generator line gives an integral rotation of the original lattice. -/
noncomputable def extendProjectedAutomorphism
    (generator : IsNormGenerator q L x)
    (f : IntegralRotation (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    IntegralRotation q L where
  toIntegralOrthogonalGroup :=
    f.toIntegralOrthogonalGroup.extendProjectedAutomorphism generator
  det_eq_one := by
    letI : Module.Finite K V := L.moduleFinite
    change LinearEquiv.det
        (QuadraticSpace.orthogonalExtensionLinearEquiv
          f.toIntegralOrthogonalGroup.toQuadraticSpaceIsometry) = 1
    rw [QuadraticSpace.det_orthogonalExtensionLinearEquiv]
    exact f.det_eq_one

@[simp]
theorem extendProjectedAutomorphism_toIntegralOrthogonalGroup
    (generator : IsNormGenerator q L x)
    (f : IntegralRotation (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic)) :
    (f.extendProjectedAutomorphism generator).toIntegralOrthogonalGroup =
      f.toIntegralOrthogonalGroup.extendProjectedAutomorphism generator :=
  rfl

end IntegralRotation

end Lattice

end Bong
