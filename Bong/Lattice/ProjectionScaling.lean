/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Isometry
import Bong.Lattice.Modular
import Bong.Lattice.Projection

/-!
# Orthogonal projection along a rescaled vector

Multiplying an anisotropic vector by a nonzero scalar leaves its orthogonal
complement and its orthogonal projection unchanged.  The subtype carrying the
orthogonal complement does change syntactically, so this file supplies the
canonical identity-on-vectors equivalence and transports projected lattices
across it.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A nonzero rescaling does not change the orthogonal complement of a
vector. -/
theorem vectorOrthogonal_smul (q : QuadraticSpace K V) (x : V)
    {a : K} (ha : a ≠ 0) :
    q.vectorOrthogonal (a • x) = q.vectorOrthogonal x := by
  ext y
  rw [q.mem_vectorOrthogonal_iff, q.mem_vectorOrthogonal_iff,
    LinearMap.BilinForm.smul_left]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left ha
  · intro h
    rw [h, mul_zero]

/-- A nonzero rescaling preserves anisotropy. -/
theorem isAnisotropic_smul (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) {a : K} (ha : a ≠ 0) :
    q.IsAnisotropic (a • x) := by
  change q.quadratic (a • x) ≠ 0
  rw [q.quadratic_smul]
  exact mul_ne_zero (pow_ne_zero 2 ha) hx

/-- Orthogonal projection is unchanged when its anisotropic axis is
rescaled by a nonzero scalar. -/
theorem orthogonalProjection_smul (q : QuadraticSpace K V) {x : V}
    (_hx : q.IsAnisotropic x) {a : K} (ha : a ≠ 0) :
    q.orthogonalProjection (a • x) = q.orthogonalProjection x := by
  ext y
  rw [q.orthogonalProjection_apply, q.orthogonalProjection_apply,
    q.quadratic_smul, LinearMap.BilinForm.smul_left, smul_smul]
  have hcoefficient :
      (a * q.bilin x y / (a ^ 2 * q.quadratic x)) * a =
        q.bilin x y / q.quadratic x := by
    field_simp [ha, _hx]
  rw [hcoefficient]

/-- The canonical identity-on-vectors equivalence between the two subtype
models of the same orthogonal complement. -/
def vectorOrthogonalSMulEquiv (q : QuadraticSpace K V) (x : V)
    {a : K} (ha : a ≠ 0) :
    q.vectorOrthogonal (a • x) ≃ₗ[K] q.vectorOrthogonal x where
  toFun y := ⟨y, by
    rw [← q.vectorOrthogonal_smul x ha]
    exact y.property⟩
  invFun y := ⟨y, by
    rw [q.vectorOrthogonal_smul x ha]
    exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_vectorOrthogonalSMulEquiv (q : QuadraticSpace K V) (x : V)
    {a : K} (ha : a ≠ 0) (y : q.vectorOrthogonal (a • x)) :
    ((q.vectorOrthogonalSMulEquiv x ha y : q.vectorOrthogonal x) : V) = y :=
  rfl

@[simp]
theorem coe_vectorOrthogonalSMulEquiv_symm (q : QuadraticSpace K V)
    (x : V) {a : K} (ha : a ≠ 0) (y : q.vectorOrthogonal x) :
    (((q.vectorOrthogonalSMulEquiv x ha).symm y :
      q.vectorOrthogonal (a • x)) : V) = y :=
  rfl

/-- The identity-on-vectors equivalence is an isometry between the two
orthogonal quadratic spaces. -/
def orthogonalSpaceSMulIsometry (q : QuadraticSpace K V) {x : V}
    (hx : q.IsAnisotropic x) {a : K} (ha : a ≠ 0) :
    Isometry (q.orthogonalSpace (a • x) (q.isAnisotropic_smul hx ha))
      (q.orthogonalSpace x hx) where
  toLinearEquiv := q.vectorOrthogonalSMulEquiv x ha
  map_bilin _ _ := rfl

end QuadraticSpace

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- After the canonical subtype transport, projecting along a nonzero
rescaling gives the same lattice as projecting along the original vector. -/
theorem map_projectedLattice_smul (q : QuadraticSpace K V)
    (L : Lattice K V) {x : V} (hx : q.IsAnisotropic x)
    {a : K} (ha : a ≠ 0) :
    map (q.vectorOrthogonalSMulEquiv x ha)
        (projectedLattice q L (a • x) (q.isAnisotropic_smul hx ha)) =
      projectedLattice q L x hx := by
  apply Lattice.ext
  ext y
  change y ∈ map (q.vectorOrthogonalSMulEquiv x ha)
      (projectedLattice q L (a • x) (q.isAnisotropic_smul hx ha)) ↔
    y ∈ projectedLattice q L x hx
  rw [mem_map_iff, mem_projectedLattice_iff, mem_projectedLattice_iff]
  constructor
  · rintro ⟨z, hz, hprojection⟩
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    have h := congrArg Subtype.val hprojection
    rw [QuadraticSpace.projectionToOrthogonal_coe] at h ⊢
    rw [q.orthogonalProjection_smul hx ha] at h
    simpa using h
  · rintro ⟨z, hz, hprojection⟩
    refine ⟨z, hz, ?_⟩
    apply Subtype.ext
    have h := congrArg Subtype.val hprojection
    rw [QuadraticSpace.projectionToOrthogonal_coe] at h ⊢
    rw [q.orthogonalProjection_smul hx ha]
    simpa using h

/-- Projecting a globally rescaled lattice along the correspondingly
rescaled vector is the global rescaling of the original projected lattice.
The two orthogonal-complement subtype models are identified by the canonical
identity-on-vectors equivalence. -/
theorem map_projectedLattice_rescale_smul (q : QuadraticSpace K V)
    (L : Lattice K V) {x : V} (hx : q.IsAnisotropic x) (a : Kˣ) :
    map (q.vectorOrthogonalSMulEquiv x a.ne_zero)
        (projectedLattice q (rescale a L) ((a : K) • x)
          (q.isAnisotropic_smul hx a.ne_zero)) =
      rescale a (projectedLattice q L x hx) := by
  apply Lattice.ext
  ext y
  change y ∈ map (q.vectorOrthogonalSMulEquiv x a.ne_zero)
      (projectedLattice q (rescale a L) ((a : K) • x)
        (q.isAnisotropic_smul hx a.ne_zero)) ↔
    y ∈ rescale a (projectedLattice q L x hx)
  rw [mem_map_iff, mem_rescale_iff]
  constructor
  · intro hy
    rw [mem_projectedLattice_iff] at hy
    rcases hy with ⟨z, hz, hprojection⟩
    rw [mem_rescale_iff] at hz
    rcases hz with ⟨w, hw, rfl⟩
    refine ⟨q.projectionToOrthogonal x hx w,
      projection_mem_projectedLattice q L x hx hw, ?_⟩
    apply Subtype.ext
    have h := congrArg Subtype.val hprojection
    rw [QuadraticSpace.projectionToOrthogonal_coe,
      q.orthogonalProjection_smul hx a.ne_zero] at h
    simpa using h
  · rintro ⟨w, hw, hwy⟩
    rw [mem_projectedLattice_iff] at hw ⊢
    rcases hw with ⟨z, hz, hprojection⟩
    refine ⟨(a : K) • z, smul_mem_rescale a L hz, ?_⟩
    apply Subtype.ext
    have hprojection' := congrArg Subtype.val hprojection
    have hwy' := congrArg Subtype.val hwy
    rw [QuadraticSpace.projectionToOrthogonal_coe] at hprojection'
    rw [QuadraticSpace.projectionToOrthogonal_coe]
    change q.orthogonalProjection ((a : K) • x) ((a : K) • z) = (y : V)
    rw [q.orthogonalProjection_smul hx a.ne_zero,
      LinearMap.map_smul, hprojection']
    simpa using hwy'

/-- The inverse-transport form of `map_projectedLattice_rescale_smul`,
used when recursively rescaling a BONG tail. -/
theorem map_rescale_projectedLattice_smul_symm (q : QuadraticSpace K V)
    (L : Lattice K V) {x : V} (hx : q.IsAnisotropic x) (a : Kˣ) :
    map (q.vectorOrthogonalSMulEquiv x a.ne_zero).symm
        (rescale a (projectedLattice q L x hx)) =
      projectedLattice q (rescale a L) ((a : K) • x)
        (q.isAnisotropic_smul hx a.ne_zero) := by
  let e := q.vectorOrthogonalSMulEquiv x a.ne_zero
  have hforward := map_projectedLattice_rescale_smul q L hx a
  apply Lattice.ext
  ext y
  change y ∈ map e.symm (rescale a (projectedLattice q L x hx)) ↔
    y ∈ projectedLattice q (rescale a L) ((a : K) • x)
      (q.isAnisotropic_smul hx a.ne_zero)
  rw [mem_map_iff, ← hforward]
  change e y ∈ map e
      (projectedLattice q (rescale a L) ((a : K) • x)
        (q.isAnisotropic_smul hx a.ne_zero)) ↔
    y ∈ projectedLattice q (rescale a L) ((a : K) • x)
      (q.isAnisotropic_smul hx a.ne_zero)
  exact map_mem_map_iff e _ y

/-- A quadratic-space isometry from a lattice to its image, bundled as a
lattice isometry. -/
noncomputable def Isometry.toMap (q : QuadraticSpace K V)
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} (f : QuadraticSpace.Isometry q r)
    (L : Lattice K V) : Isometry q r L (map f.toLinearEquiv L) where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := (map_mem_map_iff f.toLinearEquiv L x).symm

/-- Bundle a quadratic-space isometry as a lattice isometry once its image
lattice has been identified. -/
noncomputable def Isometry.ofMapEq (q : QuadraticSpace K V)
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} (f : QuadraticSpace.Isometry q r)
    (L : Lattice K V) (M : Lattice K W)
    (hmap : map f.toLinearEquiv L = M) : Isometry q r L M where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := by
    rw [← hmap, map_mem_map_iff]

end Lattice

end Bong
