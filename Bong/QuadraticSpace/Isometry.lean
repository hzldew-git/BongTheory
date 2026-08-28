/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Basic

/-!
# Isometries of quadratic spaces

This file provides the reusable isometry layer for Beli's transporter,
classification, and representation arguments.
-/

namespace Bong

namespace QuadraticSpace

universe u v w z

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- An isometry of nondegenerate symmetric quadratic spaces. -/
structure Isometry (q : QuadraticSpace K V) (r : QuadraticSpace K W) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : V ≃ₗ[K] W
  /-- The bilinear form is preserved. -/
  map_bilin (x y : V) :
    r.bilin (toLinearEquiv x) (toLinearEquiv y) = q.bilin x y

/-- Quadratic-space isometries are equal when their underlying maps are equal. -/
@[ext]
theorem Isometry.ext {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (f g : Isometry q r) (h : ∀ x, f.toLinearEquiv x = g.toLinearEquiv x) :
    f = g := by
  cases f with
  | mk fe fbilin =>
    cases g with
    | mk ge gbilin =>
      have he : fe = ge := LinearEquiv.ext h
      subst ge
      rfl

/-- Two quadratic spaces are isometric. -/
def IsIsometric (q : QuadraticSpace K V) (r : QuadraticSpace K W) : Prop :=
  Nonempty (Isometry q r)

/-- The identity isometry. -/
def Isometry.refl (q : QuadraticSpace K V) : Isometry q q where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin _ _ := rfl

/-- The inverse of a quadratic-space isometry. -/
def Isometry.symm {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (f : Isometry q r) : Isometry r q where
  toLinearEquiv := f.toLinearEquiv.symm
  map_bilin x y := by
    simpa using (f.map_bilin (f.toLinearEquiv.symm x) (f.toLinearEquiv.symm y)).symm

/-- Composition of quadratic-space isometries. -/
def Isometry.trans {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {s : QuadraticSpace K Z} (f : Isometry q r) (g : Isometry r s) :
    Isometry q s where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  map_bilin x y := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, g.map_bilin, f.map_bilin]

@[simp]
theorem Isometry.trans_refl {q : QuadraticSpace K V} (f : Isometry q q) :
    f.trans (Isometry.refl q) = f := by
  apply Isometry.ext
  intro x
  rfl

@[simp]
theorem Isometry.refl_trans {q : QuadraticSpace K V} (f : Isometry q q) :
    (Isometry.refl q).trans f = f := by
  apply Isometry.ext
  intro x
  rfl

theorem Isometry.trans_assoc {q : QuadraticSpace K V}
    (f g h : Isometry q q) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  apply Isometry.ext
  intro x
  rfl

/-- A quadratic-space isometry preserves quadratic values. -/
@[simp]
theorem Isometry.map_quadratic {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} (f : Isometry q r) (x : V) :
    r.quadratic (f.toLinearEquiv x) = q.quadratic x :=
  f.map_bilin x x

theorem isIsometric_refl (q : QuadraticSpace K V) : q.IsIsometric q :=
  ⟨Isometry.refl q⟩

end QuadraticSpace

end Bong
