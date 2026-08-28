/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals
import Bong.QuadraticSpace.Isometry
import Bong.QuadraticSpace.Rescale

/-!
# Images and isometries of quadratic lattices

Full lattices are stable under linear equivalences.  We also bundle ambient
quadratic isometries which carry one lattice exactly onto another.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- The image of a full lattice under a field-linear equivalence. -/
noncomputable def map (e : V ≃ₗ[K] W) (L : Lattice K V) : Lattice K W where
  toSubmodule := L.toSubmodule.map
    (e.toLinearMap.restrictScalars (IntegerRing K))
  fg := L.fg.map (e.toLinearMap.restrictScalars (IntegerRing K))
  span_eq_top := by
    apply top_unique
    intro y _
    let x := e.symm y
    have hx : x ∈ Submodule.span K (L.toSubmodule : Set V) := by
      rw [L.span_eq_top]
      exact Submodule.mem_top
    have he : e x = y := e.apply_symm_apply y
    have hmap : e x ∈ Submodule.span K (e '' (L.toSubmodule : Set V)) :=
      Submodule.apply_mem_span_image_of_mem_span e.toLinearMap hx
    rw [he] at hmap
    apply (Submodule.span_mono ?_) hmap
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.mem_map_of_mem hz

@[simp]
theorem map_toSubmodule (e : V ≃ₗ[K] W) (L : Lattice K V) :
    (map e L).toSubmodule = L.toSubmodule.map
      (e.toLinearMap.restrictScalars (IntegerRing K)) :=
  rfl

/-- Membership in an image lattice, expressed in the source. -/
@[simp]
theorem mem_map_iff (e : V ≃ₗ[K] W) (L : Lattice K V) (y : W) :
    y ∈ map e L ↔ e.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    simpa [← hxy] using hx
  · intro hy
    refine ⟨e.symm y, hy, ?_⟩
    exact e.apply_symm_apply y

@[simp]
theorem map_mem_map_iff (e : V ≃ₗ[K] W) (L : Lattice K V) (x : V) :
    e x ∈ map e L ↔ x ∈ L := by
  rw [mem_map_iff]
  simp

/-- Mapping by the identity equivalence leaves a lattice unchanged. -/
@[simp]
theorem map_refl (L : Lattice K V) : map (LinearEquiv.refl K V) L = L := by
  apply Lattice.ext
  ext x
  simp

/-- An ambient quadratic isometry carrying one lattice exactly onto another. -/
structure Isometry (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) where
  /-- The underlying linear equivalence. -/
  toLinearEquiv : V ≃ₗ[K] W
  /-- The bilinear form is preserved. -/
  map_bilin (x y : V) :
    r.bilin (toLinearEquiv x) (toLinearEquiv y) = q.bilin x y
  /-- The equivalence carries the source lattice exactly onto the target. -/
  map_mem (x : V) : x ∈ L ↔ toLinearEquiv x ∈ M

/-- Lattice isometries are equal when their underlying maps are equal. -/
@[ext]
theorem Isometry.ext {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} (f g : Isometry q r L M)
    (h : ∀ x, f.toLinearEquiv x = g.toLinearEquiv x) : f = g := by
  cases f with
  | mk fe fbilin fmem =>
    cases g with
    | mk ge gbilin gmem =>
      have he : fe = ge := LinearEquiv.ext h
      subst ge
      rfl

/-- Two quadratic lattices are isometric. -/
def IsIsometric (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) : Prop :=
  Nonempty (Isometry q r L M)

/-- Forgetting the integral condition gives an ambient-space isometry. -/
def Isometry.toQuadraticSpaceIsometry {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) : QuadraticSpace.Isometry q r where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin

/-- A lattice isometry preserves quadratic values. -/
@[simp]
theorem Isometry.map_quadratic {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) (x : V) :
    r.quadratic (f.toLinearEquiv x) = q.quadratic x :=
  f.map_bilin x x

/-- The identity lattice isometry. -/
def Isometry.refl (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry q q L L where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin _ _ := rfl
  map_mem _ := Iff.rfl

/-- The inverse of a lattice isometry. -/
def Isometry.symm {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} (f : Isometry q r L M) :
    Isometry r q M L where
  toLinearEquiv := f.toLinearEquiv.symm
  map_bilin x y := by
    simpa using (f.map_bilin (f.toLinearEquiv.symm x) (f.toLinearEquiv.symm y)).symm
  map_mem x := by
    simpa using (f.map_mem (f.toLinearEquiv.symm x)).symm

/-- Composition of lattice isometries. -/
def Isometry.trans {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {s : QuadraticSpace K Z} {L : Lattice K V} {M : Lattice K W}
    {N : Lattice K Z} (f : Isometry q r L M) (g : Isometry r s M N) :
    Isometry q s L N where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  map_bilin x y := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, g.map_bilin, f.map_bilin]
  map_mem x := (f.map_mem x).trans (g.map_mem (f.toLinearEquiv x))

/-- Rescaling both ambient quadratic spaces by the same nonzero scalar does
not change an integral isometry. -/
def Isometry.rescaleUnitBoth {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) (s : Kˣ) :
    Isometry (q.rescaleUnit s) (r.rescaleUnit s) L M where
  toLinearEquiv := f.toLinearEquiv
  map_bilin x y := by
    simp only [QuadraticSpace.rescaleUnit_bilin_apply]
    rw [f.map_bilin]
  map_mem := f.map_mem

/-- Rescaling a quadratic form by the scalar unit `1` gives the same
quadratic lattice. -/
def Isometry.rescaleUnitOne (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry (q.rescaleUnit (1 : Kˣ)) q L L where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin x y := by
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      Units.val_one, one_mul, LinearEquiv.refl_apply]
  map_mem _ := Iff.rfl

/-- The image lattice attached to a lattice isometry is its target. -/
theorem Isometry.map_eq {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} (f : Isometry q r L M) :
    map f.toLinearEquiv L = M := by
  apply Lattice.ext
  ext y
  change y ∈ map f.toLinearEquiv L ↔ y ∈ M
  rw [mem_map_iff]
  simpa using f.map_mem (f.toLinearEquiv.symm y)

theorem isIsometric_refl (q : QuadraticSpace K V) (L : Lattice K V) :
    IsIsometric q q L L :=
  ⟨Isometry.refl q L⟩

/-- A quadratic isometry preserves the norm ideal of an image lattice. -/
theorem normIdeal_map_isometry {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} (f : QuadraticSpace.Isometry q r)
    (L : Lattice K V) :
    normIdeal r (map f.toLinearEquiv L) = normIdeal q L := by
  apply le_antisymm
  · rw [normIdeal, Submodule.span_le]
    rintro a ⟨y, rfl⟩
    change r.quadratic (y : W) ∈ normIdeal q L
    have hy : f.toLinearEquiv.symm (y : W) ∈ L := by
      rw [← mem_map_iff f.toLinearEquiv L]
      exact y.property
    have hq := f.map_quadratic (f.toLinearEquiv.symm (y : W))
    rw [f.toLinearEquiv.apply_symm_apply] at hq
    rw [hq]
    exact quadratic_mem_normIdeal_of_mem q L hy
  · rw [normIdeal, Submodule.span_le]
    rintro a ⟨x, rfl⟩
    change q.quadratic (x : V) ∈ normIdeal r (map f.toLinearEquiv L)
    rw [← f.map_quadratic]
    exact quadratic_mem_normIdeal_of_mem r (map f.toLinearEquiv L)
      ((map_mem_map_iff f.toLinearEquiv L x).2 x.property)

/-- A quadratic isometry preserves the scale ideal of an image lattice. -/
theorem scaleIdeal_map_isometry {q : QuadraticSpace K V}
    {r : QuadraticSpace K W} (f : QuadraticSpace.Isometry q r)
    (L : Lattice K V) :
    scaleIdeal r (map f.toLinearEquiv L) = scaleIdeal q L := by
  apply le_antisymm
  · rw [scaleIdeal, Submodule.span_le]
    rintro a ⟨p, rfl⟩
    change r.bilin (p.1 : W) (p.2 : W) ∈ scaleIdeal q L
    have hx : f.toLinearEquiv.symm (p.1 : W) ∈ L := by
      rw [← mem_map_iff f.toLinearEquiv L]
      exact p.1.property
    have hy : f.toLinearEquiv.symm (p.2 : W) ∈ L := by
      rw [← mem_map_iff f.toLinearEquiv L]
      exact p.2.property
    have hpair := f.map_bilin
      (f.toLinearEquiv.symm (p.1 : W))
      (f.toLinearEquiv.symm (p.2 : W))
    rw [f.toLinearEquiv.apply_symm_apply,
      f.toLinearEquiv.apply_symm_apply] at hpair
    rw [hpair]
    exact bilin_mem_scaleIdeal_of_mem q L hx hy
  · rw [scaleIdeal, Submodule.span_le]
    rintro a ⟨p, rfl⟩
    change q.bilin (p.1 : V) (p.2 : V) ∈
      scaleIdeal r (map f.toLinearEquiv L)
    rw [← f.map_bilin]
    exact bilin_mem_scaleIdeal_of_mem r (map f.toLinearEquiv L)
      ((map_mem_map_iff f.toLinearEquiv L p.1).2 p.1.property)
      ((map_mem_map_iff f.toLinearEquiv L p.2).2 p.2.property)

end Lattice

end Bong
