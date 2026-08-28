/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.Lattice.Modular

/-!
# Modularity under lattice isometries

Linear equivalences commute with lattice rescaling, and quadratic isometries
commute with integral duality.  Consequently modularity is invariant under
integral quadratic isometry.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- Mapping a rescaled lattice is the rescaling of the mapped lattice. -/
theorem map_rescale (e : V ≃ₗ[K] W) (a : Kˣ) (L : Lattice K V) :
    map e (rescale a L) = rescale a (map e L) := by
  apply Lattice.ext
  apply Submodule.ext
  intro y
  change y ∈ map e (rescale a L) ↔ y ∈ rescale a (map e L)
  rw [mem_map_iff, mem_rescale_iff, mem_rescale_iff]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨e x, (map_mem_map_iff e L x).2 hx, ?_⟩
    rw [← e.map_smul, hxy, e.apply_symm_apply]
  · rintro ⟨z, hz, hzy⟩
    have hz' : e.symm z ∈ L := by
      simpa using (mem_map_iff e L z).1 hz
    refine ⟨e.symm z, hz', ?_⟩
    calc
      (a : K) • e.symm z = e.symm ((a : K) • z) := by
        exact (e.symm.map_smul (a : K) z).symm
      _ = e.symm y := congrArg e.symm hzy

/-- Integral duality commutes with mapping by a quadratic isometry. -/
theorem dualLattice_map_isometry
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (f : QuadraticSpace.Isometry q r) (L : Lattice K V) :
    dualLattice r (map f.toLinearEquiv L) =
      map f.toLinearEquiv (dualLattice q L) := by
  apply Lattice.ext
  apply Submodule.ext
  intro y
  change y ∈ dualLattice r (map f.toLinearEquiv L) ↔
    y ∈ map f.toLinearEquiv (dualLattice q L)
  rw [mem_dualLattice_iff, mem_map_iff, mem_dualLattice_iff]
  constructor
  · intro hy x hx
    have hfx : f.toLinearEquiv x ∈ map f.toLinearEquiv L :=
      (map_mem_map_iff f.toLinearEquiv L x).2 hx
    have h := hy (f.toLinearEquiv x) hfx
    rw [← f.map_bilin (f.toLinearEquiv.symm y) x]
    simpa using h
  · intro hy z hz
    have hz' : f.toLinearEquiv.symm z ∈ L :=
      (mem_map_iff f.toLinearEquiv L z).1 hz
    have h := hy (f.toLinearEquiv.symm z) hz'
    rw [← f.map_bilin (f.toLinearEquiv.symm y)
      (f.toLinearEquiv.symm z)] at h
    simpa using h

/-- A lattice isometry transports modularity with the same scale parameter. -/
theorem IsModular.mapLatticeIsometry
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {a : Kˣ}
    (hmodular : IsModular q L a) (f : Isometry q r L M) :
    IsModular r M a := by
  rw [IsModular]
  calc
    dualLattice r M = dualLattice r (map f.toLinearEquiv L) := by
      rw [f.map_eq]
    _ = map f.toLinearEquiv (dualLattice q L) :=
      dualLattice_map_isometry f.toQuadraticSpaceIsometry L
    _ = map f.toLinearEquiv (Lattice.rescale a⁻¹ L) := by rw [hmodular]
    _ = Lattice.rescale a⁻¹ (map f.toLinearEquiv L) := map_rescale _ _ _
    _ = Lattice.rescale a⁻¹ M := by rw [f.map_eq]

end Lattice

end Bong
