/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals

/-!
# Orthogonal projection of a quadratic lattice

For an anisotropic vector `x`, the projection onto `x⊥` is

`prₓ⊥(y) = y - (B(x, y) / Q(x)) • x`.

The image of a full lattice under this projection is constructed as a full
lattice in the quadratic space `x⊥`.  This is the operation used in the
recursive definition of a BONG.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The linear map given by the explicit orthogonal-projection formula. -/
def orthogonalProjection (q : QuadraticSpace K V) (x : V) : V →ₗ[K] V :=
  LinearMap.id - (q.quadratic x)⁻¹ • (q.bilin x).smulRight x

@[simp]
theorem orthogonalProjection_apply (q : QuadraticSpace K V) (x y : V) :
    q.orthogonalProjection x y = y - (q.bilin x y / q.quadratic x) • x := by
  simp [orthogonalProjection, div_eq_mul_inv, mul_comm, smul_smul]

theorem bilin_orthogonalProjection_eq_zero (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) (y : V) : q.bilin x (q.orthogonalProjection x y) = 0 := by
  rw [orthogonalProjection_apply]
  simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
  change q.bilin x y - (q.bilin x y / q.quadratic x) * q.quadratic x = 0
  change q.quadratic x ≠ 0 at hx
  rw [div_mul_cancel₀ _ hx, sub_self]

theorem orthogonalProjection_mem_vectorOrthogonal (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) (y : V) : q.orthogonalProjection x y ∈ q.vectorOrthogonal x :=
  (q.mem_vectorOrthogonal_iff x _).2 (q.bilin_orthogonalProjection_eq_zero hx y)

theorem orthogonalProjection_eq_self (q : QuadraticSpace K V) {x y : V}
    (hy : y ∈ q.vectorOrthogonal x) :
    q.orthogonalProjection x y = y := by
  rw [orthogonalProjection_apply, (q.mem_vectorOrthogonal_iff x y).1 hy]
  simp

@[simp]
theorem orthogonalProjection_self (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) : q.orthogonalProjection x x = 0 := by
  rw [orthogonalProjection_apply]
  change x - (q.quadratic x / q.quadratic x) • x = 0
  rw [div_self hx]
  simp

theorem orthogonalProjection_idempotent (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) (y : V) :
    q.orthogonalProjection x (q.orthogonalProjection x y) = q.orthogonalProjection x y :=
  q.orthogonalProjection_eq_self (q.orthogonalProjection_mem_vectorOrthogonal hx y)

theorem range_orthogonalProjection (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) :
    LinearMap.range (q.orthogonalProjection x) = q.vectorOrthogonal x := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    exact q.orthogonalProjection_mem_vectorOrthogonal hx z
  · intro y hy
    exact ⟨y, q.orthogonalProjection_eq_self hy⟩

/-- Orthogonal projection with codomain restricted to `x⊥`. -/
def projectionToOrthogonal (q : QuadraticSpace K V) (x : V) (hx : q.IsAnisotropic x) :
    V →ₗ[K] q.vectorOrthogonal x :=
  (q.orthogonalProjection x).codRestrict (q.vectorOrthogonal x)
    (q.orthogonalProjection_mem_vectorOrthogonal hx)

@[simp]
theorem projectionToOrthogonal_coe (q : QuadraticSpace K V) (x : V)
    (hx : q.IsAnisotropic x) (y : V) :
    (q.projectionToOrthogonal x hx y : V) = q.orthogonalProjection x y :=
  rfl

theorem projectionToOrthogonal_surjective (q : QuadraticSpace K V) (x : V)
    (hx : q.IsAnisotropic x) : Function.Surjective (q.projectionToOrthogonal x hx) := by
  intro y
  refine ⟨(y : V), Subtype.ext ?_⟩
  exact q.orthogonalProjection_eq_self y.property

end QuadraticSpace

namespace Lattice

variable {K : Type*} {V : Type*} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [AddCommGroup V] [Module K V]

/-- The image lattice `prₓ⊥ L`, regarded as a lattice in `x⊥`. -/
noncomputable def projectedLattice (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (hx : q.IsAnisotropic x) : Lattice K (q.vectorOrthogonal x) where
  toSubmodule := L.toSubmodule.map
    ((q.projectionToOrthogonal x hx).restrictScalars (IntegerRing K))
  fg := L.fg.map ((q.projectionToOrthogonal x hx).restrictScalars (IntegerRing K))
  span_eq_top := by
    apply top_unique
    intro y _
    rcases q.projectionToOrthogonal_surjective x hx y with ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (L.toSubmodule : Set V) := by
      rw [L.span_eq_top]
      exact Submodule.mem_top
    have hpv : q.projectionToOrthogonal x hx v ∈
        Submodule.span K
          (q.projectionToOrthogonal x hx '' (L.toSubmodule : Set V)) :=
      Submodule.apply_mem_span_image_of_mem_span (q.projectionToOrthogonal x hx) hv
    apply (Submodule.span_mono ?_) hpv
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.mem_map_of_mem hz

@[simp]
theorem projectedLattice_toSubmodule (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (hx : q.IsAnisotropic x) :
    (projectedLattice q L x hx).toSubmodule =
      L.toSubmodule.map ((q.projectionToOrthogonal x hx).restrictScalars (IntegerRing K)) :=
  rfl

theorem projection_mem_projectedLattice (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (hx : q.IsAnisotropic x) {y : V} (hy : y ∈ L) :
    q.projectionToOrthogonal x hx y ∈ projectedLattice q L x hx :=
  Submodule.mem_map_of_mem hy

theorem mem_projectedLattice_iff (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (hx : q.IsAnisotropic x) (y : q.vectorOrthogonal x) :
    y ∈ projectedLattice q L x hx ↔
      ∃ z : V, z ∈ L ∧ q.projectionToOrthogonal x hx z = y :=
  Iff.rfl

/-- Orthogonal projection is monotone in the lattice argument. -/
theorem projectedLattice_mono (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) (x : V) (hx : q.IsAnisotropic x) :
    projectedLattice q L x hx ≤ projectedLattice q M x hx :=
  Submodule.map_mono hLM

/-- Orthogonal projection carries a lattice sum to the sum of the projections. -/
theorem projectedLattice_sup (q : QuadraticSpace K V) (L M : Lattice K V)
    (x : V) (hx : q.IsAnisotropic x) :
    projectedLattice q (sup L M) x hx =
      sup (projectedLattice q L x hx) (projectedLattice q M x hx) := by
  apply Lattice.ext
  exact Submodule.map_sup
    (p := L.toSubmodule) (p' := M.toSubmodule)
    ((q.projectionToOrthogonal x hx).restrictScalars (IntegerRing K))

/-- A projected sublattice does not enlarge the projection of its over-lattice. -/
theorem projectedLattice_sup_eq_left_of_le (q : QuadraticSpace K V)
    (L M : Lattice K V) (x : V) (hx : q.IsAnisotropic x)
    (h : projectedLattice q M x hx ≤ projectedLattice q L x hx) :
    projectedLattice q (sup L M) x hx = projectedLattice q L x hx := by
  rw [projectedLattice_sup, sup_eq_left_of_le h]

end Lattice

end Bong
