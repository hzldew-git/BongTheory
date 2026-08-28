/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.QuadraticSpace.OrthogonalMap

/-!
# Projected lattices under ambient isometries
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
  {L : Lattice K V}

/-- Projection of an isometric image is the image of the projection. -/
theorem projectedLattice_map_isometry (f : QuadraticSpace.Isometry q r)
    (x : V) (hx : q.IsAnisotropic x) :
    projectedLattice r (map f.toLinearEquiv L) (f.toLinearEquiv x)
        (f.map_isAnisotropic hx) =
      map (f.orthogonalLinearEquiv x) (projectedLattice q L x hx) := by
  apply Lattice.ext
  ext y
  change y ∈ projectedLattice r (map f.toLinearEquiv L)
      (f.toLinearEquiv x) (f.map_isAnisotropic hx) ↔
    y ∈ map (f.orthogonalLinearEquiv x) (projectedLattice q L x hx)
  rw [mem_projectedLattice_iff, mem_map_iff]
  constructor
  · rintro ⟨z, hz, hprojection⟩
    have hw : f.toLinearEquiv.symm z ∈ L := by
      simpa only [mem_map_iff] using hz
    let w := f.toLinearEquiv.symm z
    have hzw : f.toLinearEquiv w = z :=
      f.toLinearEquiv.apply_symm_apply z
    have htail : q.projectionToOrthogonal x hx w =
        (f.orthogonalLinearEquiv x).symm y := by
      apply (f.orthogonalLinearEquiv x).injective
      rw [(f.orthogonalLinearEquiv x).apply_symm_apply]
      rw [f.map_projectionToOrthogonal, hzw, hprojection]
    rw [← htail]
    exact projection_mem_projectedLattice q L x hx hw
  · intro hy
    rcases (mem_projectedLattice_iff q L x hx
      ((f.orthogonalLinearEquiv x).symm y)).1 hy with
      ⟨z, hz, hprojection⟩
    refine ⟨f.toLinearEquiv z, ?_, ?_⟩
    · exact (map_mem_map_iff f.toLinearEquiv L z).2 hz
    · calc
        r.projectionToOrthogonal (f.toLinearEquiv x)
            (f.map_isAnisotropic hx)
            (f.toLinearEquiv z) =
            f.orthogonalLinearEquiv x
              (q.projectionToOrthogonal x hx z) :=
          (f.map_projectionToOrthogonal x hx z).symm
        _ = f.orthogonalLinearEquiv x
              ((f.orthogonalLinearEquiv x).symm y) := by
          rw [hprojection]
        _ = y := (f.orthogonalLinearEquiv x).apply_symm_apply y

/-- An integral ambient isometry restricts to an integral isometry of the
projected lattices. -/
noncomputable def Isometry.projectedLatticeIsometry
    {M : Lattice K W} (f : Isometry q r L M)
    (x : V) (hx : q.IsAnisotropic x) :
    Isometry
      (q.orthogonalSpace x hx)
      (r.orthogonalSpace (f.toLinearEquiv x)
        (f.toQuadraticSpaceIsometry.map_isAnisotropic hx))
      (projectedLattice q L x hx)
      (projectedLattice r M (f.toLinearEquiv x)
        (f.toQuadraticSpaceIsometry.map_isAnisotropic hx)) where
  toLinearEquiv := f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x
  map_bilin y z := f.map_bilin (y : V) (z : V)
  map_mem y := by
    have heq :
        projectedLattice r M (f.toLinearEquiv x)
            (f.toQuadraticSpaceIsometry.map_isAnisotropic hx) =
          map (f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x)
            (projectedLattice q L x hx) := by
      let g := f.toQuadraticSpaceIsometry
      let hfx := g.map_isAnisotropic hx
      calc
        projectedLattice r M (g.toLinearEquiv x) hfx =
            projectedLattice r (map g.toLinearEquiv L)
              (g.toLinearEquiv x) hfx :=
          congrArg (fun N : Lattice K W ↦
            projectedLattice r N (g.toLinearEquiv x) hfx) f.map_eq.symm
        _ = map (g.orthogonalLinearEquiv x)
              (projectedLattice q L x hx) :=
          projectedLattice_map_isometry g x hx
    rw [heq]
    exact (map_mem_map_iff
      (f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x)
      (projectedLattice q L x hx) y).symm

/-- Version of `projectedLatticeIsometry` whose target vector is supplied
explicitly.  This avoids exposing a reducible expression for the image
vector when an ambient isometry is assembled from an orthogonal
decomposition. -/
noncomputable def Isometry.projectedLatticeIsometryOfEq
    {M : Lattice K W} (f : Isometry q r L M)
    (x : V) (hx : q.IsAnisotropic x)
    (y : W) (hy : r.IsAnisotropic y)
    (hxy : f.toLinearEquiv x = y) :
    Isometry
      (q.orthogonalSpace x hx)
      (r.orthogonalSpace y hy)
      (projectedLattice q L x hx)
      (projectedLattice r M y hy) := by
  subst y
  exact f.projectedLatticeIsometry x hx

end Lattice

end Bong
