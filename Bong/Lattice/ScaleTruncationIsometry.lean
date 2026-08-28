/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ScaleTruncation
import Bong.Lattice.ModularIsometry

/-!
# O'Meara scale truncations under isometry

O'Meara's intrinsic auxiliary lattice `L^s = L ∩ π^s L♯` commutes with
quadratic-space isometries.  This is a basic input for proving that the
fundamental invariants used in Theorem 93:28 are genuine lattice invariants.
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

/-- Mapping by a linear equivalence commutes with the intersection of full
lattices. -/
theorem map_inf (e : V ≃ₗ[K] W) (L N : Lattice K V) :
    map e (inf L N) = inf (map e L) (map e N) := by
  apply Lattice.ext
  apply Submodule.ext
  intro y
  change y ∈ map e (inf L N) ↔ y ∈ inf (map e L) (map e N)
  simp only [mem_map_iff, mem_inf_iff]

/-- O'Meara's intrinsic lattice `L^s = L ∩ π^s L♯` is functorial under
quadratic-space isometries. -/
theorem scaleTruncation_map_isometry
    (f : QuadraticSpace.Isometry q r) (L : Lattice K V) (s : Int) :
    scaleTruncation r (map f.toLinearEquiv L) s =
      map f.toLinearEquiv (scaleTruncation q L s) := by
  rw [scaleTruncation, scaleTruncation,
    dualLattice_map_isometry f L, ← map_rescale, ← map_inf]

/-- Restricting an integral lattice isometry to O'Meara's intrinsic
auxiliary lattices gives another integral lattice isometry. -/
noncomputable def Isometry.scaleTruncation
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) (s : Int) :
    Isometry q r (Lattice.scaleTruncation q L s)
      (Lattice.scaleTruncation r M s) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := by
    have htarget : Lattice.scaleTruncation r M s =
        map f.toLinearEquiv (Lattice.scaleTruncation q L s) := by
      calc
        Lattice.scaleTruncation r M s =
            Lattice.scaleTruncation r (map f.toLinearEquiv L) s := by
              rw [f.map_eq]
        _ = map f.toLinearEquiv (Lattice.scaleTruncation q L s) :=
          scaleTruncation_map_isometry f.toQuadraticSpaceIsometry L s
    rw [htarget, map_mem_map_iff]

end Lattice

end Bong
