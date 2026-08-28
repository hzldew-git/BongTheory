/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Dual
import Bong.Lattice.Isometry

/-!
# Functoriality of integral dual lattices under isometries

An ambient quadratic isometry carrying one full lattice onto another carries
their integral dual lattices onto one another by the same linear map.  This
is the reusable lattice-theoretic transport needed by reverse-dual arguments.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Regard an equality of lattices in one quadratic space as the identity
lattice isometry. -/
def Isometry.ofLatticeEq
    (q : QuadraticSpace K V) {L N : Lattice K V} (h : L = N) :
    Isometry q q L N := by
  subst N
  exact Isometry.refl q L

@[simp]
theorem Isometry.ofLatticeEq_apply
    (q : QuadraticSpace K V) {L N : Lattice K V} (h : L = N) (x : V) :
    (Isometry.ofLatticeEq q h).toLinearEquiv x = x := by
  subst N
  rfl

@[simp]
theorem Isometry.ofLatticeEq_symm_apply
    (q : QuadraticSpace K V) {L N : Lattice K V} (h : L = N) (x : V) :
    (Isometry.ofLatticeEq q h).toLinearEquiv.symm x = x := by
  subst N
  rfl

/-- A lattice isometry induces a lattice isometry between the integral
duals, with the same underlying linear equivalence. -/
noncomputable def Isometry.dual (f : Isometry q r L M) :
    Isometry q r (dualLattice q L) (dualLattice r M) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := by
    rw [mem_dualLattice_iff, mem_dualLattice_iff]
    constructor
    · intro hx y hy
      let z : V := f.toLinearEquiv.symm y
      have hz : z ∈ L := by
        apply (f.map_mem z).mpr
        simpa [z] using hy
      have hxy := hx z hz
      have hbilin := f.map_bilin x z
      rw [show f.toLinearEquiv z = y by simp [z]] at hbilin
      rwa [hbilin]
    · intro hx y hy
      have hfy : f.toLinearEquiv y ∈ M :=
        (f.map_mem y).mp hy
      have hxy := hx (f.toLinearEquiv y) hfy
      rwa [f.map_bilin] at hxy

@[simp]
theorem Isometry.dual_toLinearEquiv (f : Isometry q r L M) :
    f.dual.toLinearEquiv = f.toLinearEquiv :=
  rfl

/-- Equality of integral dual lattices reflects equality of the original
lattices.  This is the involutive step used when a lattice identity is first
proved after reverse duality. -/
theorem eq_of_dualLattice_eq {N : Lattice K V}
    (h : dualLattice q L = dualLattice q N) : L = N := by
  calc
    L = dualLattice q (dualLattice q L) :=
      (dualLattice_dualLattice q L).symm
    _ = dualLattice q (dualLattice q N) := congrArg (dualLattice q) h
    _ = N := dualLattice_dualLattice q N

end Lattice

end Bong
