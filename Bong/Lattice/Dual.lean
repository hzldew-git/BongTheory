/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Integral duals of quadratic lattices

For an `𝓞`-submodule `M` of a quadratic space, its integral dual is

`M♯ = {x | B(x, M) ⊆ 𝓞}`.

This file constructs the dual as an `𝓞`-submodule and proves its elementary
order-theoretic properties.  The normalized valuation ring is a PID, so an
integral basis and mathlib's dual-basis theorem then upgrade the module to a
full lattice and prove integral biduality.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The integral dual of an `𝓞`-submodule with respect to a quadratic space. -/
noncomputable def dualSubmodule (q : QuadraticSpace K V)
    (M : Submodule (IntegerRing K) V) : Submodule (IntegerRing K) V where
  carrier := {x | ∀ y : V, y ∈ M → q.bilin x y ∈ IntegerRing K}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy z hz
    rw [LinearMap.BilinForm.add_left]
    exact (IntegerRing K).add_mem _ _ (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx y hy
    change q.bilin ((a : K) • x) y ∈ IntegerRing K
    rw [LinearMap.BilinForm.smul_left]
    exact (IntegerRing K).mul_mem _ _ a.property (hx y hy)

@[simp]
theorem mem_dualSubmodule_iff (q : QuadraticSpace K V)
    (M : Submodule (IntegerRing K) V) (x : V) :
    x ∈ dualSubmodule q M ↔ ∀ y : V, y ∈ M → q.bilin x y ∈ IntegerRing K :=
  Iff.rfl

/-- Compatibility with mathlib's bilinear-form dual-submodule construction. -/
theorem dualSubmodule_eq_bilinDualSubmodule (q : QuadraticSpace K V)
    (M : Submodule (IntegerRing K) V) :
    dualSubmodule q M = q.bilin.dualSubmodule M := by
  ext x
  rw [mem_dualSubmodule_iff, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hx y hy
    exact Submodule.mem_one.mpr ⟨⟨q.bilin x y, hx y hy⟩, rfl⟩
  · intro hx y hy
    rcases Submodule.mem_one.mp (hx y hy) with ⟨a, ha⟩
    have ha' : (a : K) = q.bilin x y := by simpa using ha
    rw [← ha']
    exact a.property

/-- Integral duality reverses inclusions. -/
theorem dualSubmodule_antitone (q : QuadraticSpace K V)
    {M N : Submodule (IntegerRing K) V} (hMN : M ≤ N) :
    dualSubmodule q N ≤ dualSubmodule q M := by
  intro x hx y hy
  exact hx y (hMN hy)

/-- Every submodule is contained in its integral bidual. -/
theorem le_dualSubmodule_dualSubmodule (q : QuadraticSpace K V)
    (M : Submodule (IntegerRing K) V) :
    M ≤ dualSubmodule q (dualSubmodule q M) := by
  intro x hx y hy
  rw [q.isSymm.eq]
  exact hy x hx

/-- Biduality is an equality for the integral span of a field basis. -/
theorem dualSubmodule_dualSubmodule_of_basis {i : Type*} [Finite i]
    (q : QuadraticSpace K V) (b : Basis i K V) :
    dualSubmodule q
        (dualSubmodule q (Submodule.span (IntegerRing K) (Set.range b))) =
      Submodule.span (IntegerRing K) (Set.range b) := by
  rw [dualSubmodule_eq_bilinDualSubmodule,
    dualSubmodule_eq_bilinDualSubmodule]
  exact q.bilin.dualSubmodule_dualSubmodule_of_basis
    q.nondegenerate q.isSymm b

/-- The dual module of a lattice is the integral span of the dual ambient basis. -/
theorem dualSubmodule_eq_span_dualBasis (q : QuadraticSpace K V)
    (L : Lattice K V) :
    dualSubmodule q L.toSubmodule =
      Submodule.span (IntegerRing K)
        (Set.range (q.bilin.dualBasis q.nondegenerate L.ambientBasis)) := by
  rw [dualSubmodule_eq_bilinDualSubmodule]
  calc
    q.bilin.dualSubmodule L.toSubmodule =
        q.bilin.dualSubmodule
          (Submodule.span (IntegerRing K) (Set.range L.ambientBasis)) :=
      congrArg q.bilin.dualSubmodule L.toSubmodule_eq_span_ambientBasis
    _ = Submodule.span (IntegerRing K)
        (Set.range (q.bilin.dualBasis q.nondegenerate L.ambientBasis)) := by
      exact q.bilin.dualSubmodule_span_of_basis
        q.nondegenerate L.ambientBasis

/-- Integral biduality for an arbitrary full lattice. -/
theorem dualSubmodule_dualSubmodule_eq_lattice (q : QuadraticSpace K V)
    (L : Lattice K V) :
    dualSubmodule q (dualSubmodule q L.toSubmodule) = L.toSubmodule := by
  rw [L.toSubmodule_eq_span_ambientBasis]
  exact dualSubmodule_dualSubmodule_of_basis q L.ambientBasis

/-- The integral dual, bundled as a full lattice. -/
noncomputable def dualLattice (q : QuadraticSpace K V) (L : Lattice K V) :
    Lattice K V := by
  classical
  let db := q.bilin.dualBasis q.nondegenerate L.ambientBasis
  have hdual : dualSubmodule q L.toSubmodule =
      Submodule.span (IntegerRing K) (Set.range db) := by
    simpa [db] using dualSubmodule_eq_span_dualBasis q L
  exact
    { toSubmodule := dualSubmodule q L.toSubmodule
      fg := by
        rw [hdual]
        exact Submodule.fg_span (Set.toFinite (Set.range db))
      span_eq_top := by
        rw [hdual, Submodule.span_span_of_tower, db.span_eq] }

@[simp]
theorem toSubmodule_dualLattice (q : QuadraticSpace K V) (L : Lattice K V) :
    (dualLattice q L).toSubmodule = dualSubmodule q L.toSubmodule :=
  rfl

@[simp]
theorem mem_dualLattice_iff (q : QuadraticSpace K V) (L : Lattice K V)
    (x : V) :
    x ∈ dualLattice q L ↔
      ∀ y : V, y ∈ L → q.bilin x y ∈ IntegerRing K :=
  Iff.rfl

/-- Bundled lattice duality reverses inclusions. -/
theorem dualLattice_antitone (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) : dualLattice q M ≤ dualLattice q L :=
  dualSubmodule_antitone q hLM

/-- Taking the bundled integral dual twice returns the original lattice. -/
@[simp]
theorem dualLattice_dualLattice (q : QuadraticSpace K V) (L : Lattice K V) :
    dualLattice q (dualLattice q L) = L := by
  apply ext
  exact dualSubmodule_dualSubmodule_eq_lattice q L

/-- The dual of a basis lattice is generated by the bilinear dual basis. -/
theorem dualLattice_basisLattice {ι : Type*} [Finite ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) :
    dualLattice q (basisLattice b) =
      basisLattice (q.bilin.dualBasis q.nondegenerate b) := by
  classical
  apply Lattice.ext
  change dualSubmodule q
      (Submodule.span (IntegerRing K) (Set.range b)) =
    Submodule.span (IntegerRing K)
      (Set.range (q.bilin.dualBasis q.nondegenerate b))
  rw [dualSubmodule_eq_bilinDualSubmodule]
  exact q.bilin.dualSubmodule_span_of_basis q.nondegenerate b

/-- The integral dual module of a lattice. -/
noncomputable def dualModule (q : QuadraticSpace K V) (L : Lattice K V) :
    Submodule (IntegerRing K) V :=
  dualSubmodule q L.toSubmodule

@[simp]
theorem mem_dualModule_iff (q : QuadraticSpace K V) (L : Lattice K V) (x : V) :
    x ∈ dualModule q L ↔ ∀ y : V, y ∈ L → q.bilin x y ∈ IntegerRing K :=
  Iff.rfl

/-- Lattice dual modules reverse lattice inclusions. -/
theorem dualModule_antitone (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) : dualModule q M ≤ dualModule q L :=
  dualSubmodule_antitone q hLM

/-- A lattice lies in its dual exactly when its scale ideal is integral. -/
theorem le_dualModule_iff_isScaleIntegral (q : QuadraticSpace K V) (L : Lattice K V) :
    L.toSubmodule ≤ dualModule q L ↔ IsScaleIntegral q L := by
  constructor
  · intro hL
    rw [IsScaleIntegral, scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply mem_unitIdeal_iff.mpr
    exact hL p.1.property p.2 p.2.property
  · intro hL x hx y hy
    apply mem_unitIdeal_iff.mp
    exact hL (bilin_mem_scaleIdeal_of_mem q L hx hy)

/-- Bundled version of the scale-integrality criterion `L ⊆ L♯`. -/
theorem le_dualLattice_iff_isScaleIntegral (q : QuadraticSpace K V)
    (L : Lattice K V) :
    L ≤ dualLattice q L ↔ IsScaleIntegral q L :=
  le_dualModule_iff_isScaleIntegral q L

end Lattice

end Bong
