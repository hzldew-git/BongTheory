/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Automorphism

/-!
# Negation isometries and integral automorphisms
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The negative identity as a quadratic-space isometry. -/
def negOneIsometry (q : QuadraticSpace K V) : Isometry q q where
  toLinearEquiv := LinearEquiv.neg K
  map_bilin x y := by
    simp only [LinearEquiv.neg_apply, LinearMap.BilinForm.neg_left,
      LinearMap.BilinForm.neg_right, neg_neg]

@[simp]
theorem negOneIsometry_apply (q : QuadraticSpace K V) (x : V) :
    (negOneIsometry q).toLinearEquiv x = -x :=
  rfl

end QuadraticSpace

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The negative identity preserves every lattice. -/
def negOneAutomorphism (q : QuadraticSpace K V) (L : Lattice K V) :
    IntegralOrthogonalGroup q L where
  toLinearEquiv := LinearEquiv.neg K
  map_bilin x y := by
    simp only [LinearEquiv.neg_apply, LinearMap.BilinForm.neg_left,
      LinearMap.BilinForm.neg_right, neg_neg]
  map_mem y := by
    change y ∈ L.toSubmodule ↔ -y ∈ L.toSubmodule
    exact L.toSubmodule.neg_mem_iff.symm

@[simp]
theorem negOneAutomorphism_apply (q : QuadraticSpace K V)
    (L : Lattice K V) (x : V) :
    (negOneAutomorphism q L).toLinearEquiv x = -x :=
  LinearEquiv.neg_apply x

@[simp]
theorem negOneAutomorphism_toQuadraticSpaceIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) :
    (negOneAutomorphism q L).toQuadraticSpaceIsometry =
      QuadraticSpace.negOneIsometry q := by
  apply QuadraticSpace.Isometry.ext
  intro x
  change (LinearEquiv.neg K : V ≃ₗ[K] V) x =
    (LinearEquiv.neg K : V ≃ₗ[K] V) x
  rfl

/-- In dimension two, integral negation is a proper rotation. -/
theorem det_negOneAutomorphism_eq_one_of_finrank_two
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfin : Module.finrank K V = 2) :
    LinearEquiv.det (negOneAutomorphism q L).toLinearEquiv = 1 := by
  letI : Module.Finite K V := L.moduleFinite
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hmap :
      (negOneAutomorphism q L).toLinearEquiv.toLinearMap =
        (-1 : K) • (LinearMap.id : V →ₗ[K] V) := by
    ext y
    simp
  rw [hmap, LinearMap.det_smul, LinearMap.det_id, hfin]
  norm_num

end Lattice

end Bong
