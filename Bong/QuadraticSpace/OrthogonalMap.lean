/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.Isometry
import Bong.Lattice.Projection

/-!
# Isometries on orthogonal complements

An isometry carries `x^perp` to `(f x)^perp` and commutes with the associated
orthogonal projections.
-/

namespace Bong

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}

/-- Isometries carry anisotropic vectors to anisotropic vectors. -/
theorem Isometry.map_isAnisotropic (f : Isometry q r) {x : V}
    (hx : q.IsAnisotropic x) : r.IsAnisotropic (f.toLinearEquiv x) := by
  rw [IsAnisotropic, f.map_quadratic]
  exact hx

/-- The induced linear equivalence of orthogonal complements. -/
def Isometry.orthogonalLinearEquiv (f : Isometry q r) (x : V) :
    q.vectorOrthogonal x ≃ₗ[K] r.vectorOrthogonal (f.toLinearEquiv x) where
  toFun y := ⟨f.toLinearEquiv y, by
    rw [r.mem_vectorOrthogonal_iff, f.map_bilin]
    exact (q.mem_vectorOrthogonal_iff x y).1 y.property⟩
  invFun z := ⟨f.toLinearEquiv.symm z, by
    rw [q.mem_vectorOrthogonal_iff]
    have hmap := f.map_bilin x (f.toLinearEquiv.symm z)
    rw [f.toLinearEquiv.apply_symm_apply] at hmap
    rw [← hmap]
    exact (r.mem_vectorOrthogonal_iff (f.toLinearEquiv x) z).1 z.property⟩
  left_inv y := by
    apply Subtype.ext
    exact f.toLinearEquiv.symm_apply_apply y
  right_inv z := by
    apply Subtype.ext
    exact f.toLinearEquiv.apply_symm_apply z
  map_add' y z := by
    apply Subtype.ext
    exact f.toLinearEquiv.map_add y z
  map_smul' a y := by
    apply Subtype.ext
    exact f.toLinearEquiv.map_smul a y

@[simp]
theorem Isometry.orthogonalLinearEquiv_coe (f : Isometry q r) (x : V)
    (y : q.vectorOrthogonal x) :
    (f.orthogonalLinearEquiv x y : W) = f.toLinearEquiv (y : V) :=
  rfl

/-- The induced equivalence is an isometry of restricted quadratic spaces. -/
def Isometry.orthogonalIsometry (f : Isometry q r) (x : V)
    (hx : q.IsAnisotropic x) :
    Isometry (q.orthogonalSpace x hx)
      (r.orthogonalSpace (f.toLinearEquiv x) (f.map_isAnisotropic hx)) where
  toLinearEquiv := f.orthogonalLinearEquiv x
  map_bilin y z := f.map_bilin y z

/-- An isometry commutes with anisotropic-line orthogonal projection. -/
theorem Isometry.map_orthogonalProjection (f : Isometry q r) (x : V)
    (y : V) :
    r.orthogonalProjection (f.toLinearEquiv x) (f.toLinearEquiv y) =
      f.toLinearEquiv (q.orthogonalProjection x y) := by
  rw [r.orthogonalProjection_apply, q.orthogonalProjection_apply,
    f.map_bilin, f.map_quadratic]
  simp

/-- Restricted orthogonal projections commute with an isometry. -/
theorem Isometry.map_projectionToOrthogonal (f : Isometry q r) (x : V)
    (hx : q.IsAnisotropic x) (y : V) :
    f.orthogonalLinearEquiv x (q.projectionToOrthogonal x hx y) =
      r.projectionToOrthogonal (f.toLinearEquiv x)
        (f.map_isAnisotropic hx) (f.toLinearEquiv y) := by
  apply Subtype.ext
  exact (f.map_orthogonalProjection x y).symm

end QuadraticSpace

end Bong
