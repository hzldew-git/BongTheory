/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalMap

/-!
# Projecting a lattice isometry

An ambient lattice isometry induces an isometry of the orthogonal
complements and carries the corresponding projected lattices onto one
another.
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

/-- Project a lattice isometry along an anisotropic source vector. -/
noncomputable def Isometry.projected
    (f : Isometry q r L M) (x : V) (hx : q.IsAnisotropic x) :
    Isometry
      (q.orthogonalSpace x hx)
      (r.orthogonalSpace (f.toLinearEquiv x)
        (f.toQuadraticSpaceIsometry.map_isAnisotropic hx))
      (L.projectedLattice q x hx)
      (M.projectedLattice r (f.toLinearEquiv x)
        (f.toQuadraticSpaceIsometry.map_isAnisotropic hx)) where
  toLinearEquiv := f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x
  map_bilin :=
    (f.toQuadraticSpaceIsometry.orthogonalIsometry x hx).map_bilin
  map_mem := by
    intro y
    let e := f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x
    have htarget :
        M.projectedLattice r (f.toLinearEquiv x)
            (f.toQuadraticSpaceIsometry.map_isAnisotropic hx) =
          Lattice.map e (L.projectedLattice q x hx) := by
      calc
        M.projectedLattice r (f.toLinearEquiv x)
              (f.toQuadraticSpaceIsometry.map_isAnisotropic hx) =
            (Lattice.map f.toLinearEquiv L).projectedLattice r
              (f.toLinearEquiv x)
              (f.toQuadraticSpaceIsometry.map_isAnisotropic hx) := by
                rw [f.map_eq]
        _ = Lattice.map e (L.projectedLattice q x hx) :=
          Lattice.projectedLattice_map_isometry
            f.toQuadraticSpaceIsometry x hx
    rw [htarget]
    exact (Lattice.map_mem_map_iff e
      (L.projectedLattice q x hx) y).symm

@[simp]
theorem Isometry.projected_apply
    (f : Isometry q r L M) (x : V) (hx : q.IsAnisotropic x)
    (y : q.vectorOrthogonal x) :
    (f.projected x hx).toLinearEquiv y =
      f.toQuadraticSpaceIsometry.orthogonalLinearEquiv x y :=
  rfl

/-- Restate the projected target along an explicit equality for the image of
the projection axis.  Packaging the dependent transport here keeps concrete
coordinate calculations out of later projection arguments. -/
noncomputable def Isometry.projectedAlongImageEq
    (f : Isometry q r L M) (x : V) (hx : q.IsAnisotropic x)
    (y : W) (hy : r.IsAnisotropic y)
    (hxy : f.toLinearEquiv x = y) :
    Isometry
      (q.orthogonalSpace x hx)
      (r.orthogonalSpace y hy)
      (L.projectedLattice q x hx)
      (M.projectedLattice r y hy) := by
  subst y
  exact f.projected x hx

end Lattice

end Bong
