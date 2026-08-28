/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Representation
import Bong.Lattice.Dual

/-!
# Integral representations and lattice duality

An integral representation between quadratic spaces of equal dimension is an
ambient isometry onto its image.  Integral duality reverses the lattice
inclusion, so the inverse ambient isometry represents the dual of the target
lattice by the dual of the source lattice.  This is the representation-level
duality used in Beli (2019), Lemma 9.7.
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

namespace Representation

/-- Duality reverses an integral representation between equal-dimensional
quadratic spaces.  The inverse of the induced ambient isometry sends
`M♯` into `L♯`. -/
noncomputable def dualOfFinrankEq
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : Representation q r L M)
    (hfinrank : Module.finrank K V = Module.finrank K W) :
    Representation r q (dualLattice r M) (dualLattice q L) := by
  let g := f.toQuadraticSpaceIsometryOfFinrankEq hfinrank
  refine
    { toLinearMap := g.toLinearEquiv.symm
      injective := g.toLinearEquiv.symm.injective
      map_bilin := g.symm.map_bilin
      map_mem := ?_ }
  intro x hx
  rw [mem_dualLattice_iff] at hx ⊢
  intro y hy
  have hgy : g.toLinearEquiv y ∈ M := f.map_mem hy
  have hxy := hx (g.toLinearEquiv y) hgy
  have hbilin := g.map_bilin (g.toLinearEquiv.symm x) y
  simp only [LinearEquiv.apply_symm_apply] at hbilin
  change q.bilin (g.toLinearEquiv.symm x) y ∈ IntegerRing K
  rw [← hbilin]
  exact hxy

end Representation

/-- If `M` represents `L` and their ambient dimensions agree, then `L♯`
represents `M♯`. -/
theorem Represents.dual_of_finrank_eq
    [FiniteDimensional K V] [FiniteDimensional K W]
    (h : Represents r q M L)
    (hfinrank : Module.finrank K V = Module.finrank K W) :
    Represents q r (dualLattice q L) (dualLattice r M) := by
  rcases h with ⟨f⟩
  exact ⟨f.dualOfFinrankEq hfinrank⟩

end Lattice

end Bong
