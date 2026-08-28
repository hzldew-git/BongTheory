/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Dual
import Mathlib.Tactic.Group

/-!
# Rescaling and modular quadratic lattices

Multiplication by a nonzero field element preserves full integral lattices.  We
use this action to express modularity in the basis-free form

`L♯ = a⁻¹ L`.

Here `a : Kˣ` is a chosen generator of the scale.  This convention makes
unimodularity the special case `a = 1` and interacts transparently with
integral duality.
-/

namespace Bong

open Dyadic
open scoped Pointwise

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- Rescale a lattice by a nonzero field element. -/
noncomputable def rescale (a : Kˣ) (L : Lattice K V) : Lattice K V where
  toSubmodule := a • L.toSubmodule
  fg := Submodule.IsLattice.fg (A := K)
  span_eq_top := Submodule.IsLattice.span_eq_top (A := K)

@[simp]
theorem toSubmodule_rescale (a : Kˣ) (L : Lattice K V) :
    (rescale a L).toSubmodule = a • L.toSubmodule :=
  rfl

theorem mem_rescale_iff (a : Kˣ) (L : Lattice K V) (x : V) :
    x ∈ rescale a L ↔ ∃ y : V, y ∈ L ∧ (a : K) • y = x := by
  exact Submodule.mem_smul_pointwise_iff_exists x a L.toSubmodule

theorem smul_mem_rescale (a : Kˣ) (L : Lattice K V) {x : V}
    (hx : x ∈ L) : (a : K) • x ∈ rescale a L :=
  Submodule.smul_mem_pointwise_smul x a L.toSubmodule hx

/-- Rescaling by a nonzero integral scalar produces a sublattice. -/
theorem rescale_le_self_of_mem_integerRing (a : Kˣ) (L : Lattice K V)
    (ha : (a : K) ∈ IntegerRing K) : rescale a L ≤ L := by
  intro x hx
  change x ∈ rescale a L at hx
  rw [mem_rescale_iff] at hx
  rcases hx with ⟨y, hy, rfl⟩
  let aO : IntegerRing K := ⟨(a : K), ha⟩
  exact L.smul_mem aO hy

@[simp]
theorem rescale_one (L : Lattice K V) : rescale 1 L = L := by
  apply ext
  simp [rescale]

theorem rescale_mul (a b : Kˣ) (L : Lattice K V) :
    rescale (a * b) L = rescale a (rescale b L) := by
  apply ext
  simp [rescale, mul_smul]

@[simp]
theorem rescale_inv_rescale (a : Kˣ) (L : Lattice K V) :
    rescale a⁻¹ (rescale a L) = L := by
  rw [← rescale_mul]
  convert rescale_one L using 1
  group

@[simp]
theorem rescale_rescale_inv (a : Kˣ) (L : Lattice K V) :
    rescale a (rescale a⁻¹ L) = L := by
  rw [← rescale_mul]
  convert rescale_one L using 1
  group

/-- Duality reverses a lattice rescaling. -/
theorem dualSubmodule_rescale (q : QuadraticSpace K V) (a : Kˣ)
    (L : Lattice K V) :
    dualSubmodule q (rescale a L).toSubmodule =
      (rescale a⁻¹ (dualLattice q L)).toSubmodule := by
  ext x
  constructor
  · intro hx
    change x ∈ rescale a⁻¹ (dualLattice q L)
    have hz : (a : K) • x ∈ dualLattice q L := by
      rw [mem_dualLattice_iff]
      intro y hy
      have hay : (a : K) • y ∈ rescale a L := smul_mem_rescale a L hy
      simpa only [LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right] using hx ((a : K) • y) hay
    have hz' := smul_mem_rescale a⁻¹ (dualLattice q L) hz
    simpa [smul_smul] using hz'
  · intro hx
    change x ∈ rescale a⁻¹ (dualLattice q L) at hx
    rw [mem_rescale_iff] at hx
    rcases hx with ⟨z, hz, rfl⟩
    intro y hy
    change y ∈ rescale a L at hy
    rw [mem_rescale_iff] at hy
    rcases hy with ⟨w, hw, rfl⟩
    simpa [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right] using hz w hw

/-- Bundled form of the rescaling rule `(aL)♯ = a⁻¹L♯`. -/
theorem dualLattice_rescale (q : QuadraticSpace K V) (a : Kˣ)
    (L : Lattice K V) :
    dualLattice q (rescale a L) = rescale a⁻¹ (dualLattice q L) := by
  apply ext
  exact dualSubmodule_rescale q a L

/-- A lattice is `a`-modular when its dual is `a⁻¹` times the lattice. -/
def IsModular (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) : Prop :=
  dualLattice q L = rescale a⁻¹ L

/-- A unimodular lattice is equal to its integral dual. -/
def IsUnimodular (q : QuadraticSpace K V) (L : Lattice K V) : Prop :=
  IsModular q L 1

theorem isUnimodular_iff_dualLattice_eq (q : QuadraticSpace K V)
    (L : Lattice K V) :
    IsUnimodular q L ↔ dualLattice q L = L := by
  simp [IsUnimodular, IsModular]

/-- The dual of an `a`-modular lattice is `a⁻¹`-modular. -/
theorem IsModular.dual {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}
    (hL : IsModular q L a) : IsModular q (dualLattice q L) a⁻¹ := by
  rw [IsModular, dualLattice_dualLattice, inv_inv, hL]
  exact (rescale_rescale_inv a L).symm

/-- Rescaling an `a`-modular lattice by `c` changes the parameter to `a c²`. -/
theorem IsModular.rescale {q : QuadraticSpace K V} {L : Lattice K V}
    {a : Kˣ} (hL : IsModular q L a) (c : Kˣ) :
    IsModular q (rescale c L) (a * c ^ 2) := by
  rw [IsModular, dualLattice_rescale, hL]
  rw [← rescale_mul, ← rescale_mul]
  congr 1
  simp only [mul_inv_rev, pow_two]
  calc
    c⁻¹ * a⁻¹ = (c⁻¹ * c) * (c⁻¹ * a⁻¹) := by simp
    _ = c⁻¹ * c⁻¹ * a⁻¹ * c := by ac_rfl

end Lattice

end Bong
