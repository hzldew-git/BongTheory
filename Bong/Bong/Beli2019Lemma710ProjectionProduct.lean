/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710OrthogonalSum
import Bong.Lattice.OrthogonalMap

/-!
# Beli (2019), Lemma 7.10: projection of an orthogonal product

If `x` lies in the left factor of an orthogonal product, projection along
`(x, 0)` acts by projection along `x` on the left and by the identity on the
right.  We identify the resulting orthogonal complement and projected
lattice with the corresponding product.  This is the recursive geometric
bridge needed to concatenate BONG blocks in Lemma 7.10.
-/

namespace Bong

open Dyadic

universe u v w

namespace QuadraticSpace

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- An anisotropic vector in the left factor stays anisotropic in an
orthogonal sum. -/
theorem IsAnisotropic.orthogonalSum_inl
    {q : QuadraticSpace K V} {r : QuadraticSpace K W} {x : V}
    (hx : q.IsAnisotropic x) :
    (q.orthogonalSum r).IsAnisotropic (x, 0) := by
  change q.quadratic x + r.quadratic 0 ≠ 0
  simpa only [r.quadratic_zero, add_zero, QuadraticSpace.IsAnisotropic] using hx

/-- Projection along a vector in the left factor is the product of the left
projection and the identity on the right factor. -/
@[simp]
theorem orthogonalProjection_orthogonalSum_inl
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (x : V) (z : V × W) :
    (q.orthogonalSum r).orthogonalProjection (x, 0) z =
      (q.orthogonalProjection x z.1, z.2) := by
  apply Prod.ext
  · simp [QuadraticSpace.orthogonalProjection_apply,
      QuadraticSpace.orthogonalSum_quadratic_apply]
  · simp [QuadraticSpace.orthogonalProjection_apply,
      QuadraticSpace.orthogonalSum_quadratic_apply]

/-- The canonical linear equivalence
`(x,0)⊥ ≃ x⊥ × W`. -/
def orthogonalSumVectorOrthogonalEquiv
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (x : V) :
    (q.orthogonalSum r).vectorOrthogonal (x, 0) ≃ₗ[K]
      q.vectorOrthogonal x × W where
  toFun z :=
    (⟨z.val.1, by
      rw [q.mem_vectorOrthogonal_iff]
      have hz := ((q.orthogonalSum r).mem_vectorOrthogonal_iff
        (x, 0) z).1 z.property
      simpa using hz⟩, z.val.2)
  invFun z :=
    ⟨(z.1, z.2), by
      rw [(q.orthogonalSum r).mem_vectorOrthogonal_iff]
      simpa using (q.mem_vectorOrthogonal_iff x z.1).1 z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl rfl
  right_inv z :=
    Prod.ext (Subtype.ext rfl) rfl
  map_add' _ _ :=
    Prod.ext (Subtype.ext rfl) rfl
  map_smul' _ _ :=
    Prod.ext (Subtype.ext rfl) rfl

@[simp]
theorem orthogonalSumVectorOrthogonalEquiv_apply
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) (x : V)
    (z : (q.orthogonalSum r).vectorOrthogonal (x, 0)) :
    q.orthogonalSumVectorOrthogonalEquiv r x z =
      (⟨z.val.1, by
        rw [q.mem_vectorOrthogonal_iff]
        have hz := ((q.orthogonalSum r).mem_vectorOrthogonal_iff
          (x, 0) z).1 z.property
        simpa using hz⟩, z.val.2) :=
  rfl

@[simp]
theorem orthogonalSumVectorOrthogonalEquiv_projectionToOrthogonal
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    {x : V} (hx : q.IsAnisotropic x) (z : V × W) :
    q.orthogonalSumVectorOrthogonalEquiv r x
        ((q.orthogonalSum r).projectionToOrthogonal (x, 0)
          hx.orthogonalSum_inl z) =
      (q.projectionToOrthogonal x hx z.1, z.2) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((q.orthogonalSum r).orthogonalProjection (x, 0) z).1 =
      q.orthogonalProjection x z.1
    exact congrArg Prod.fst
      (q.orthogonalProjection_orthogonalSum_inl r x z)
  · change ((q.orthogonalSum r).orthogonalProjection (x, 0) z).2 = z.2
    rw [q.orthogonalProjection_orthogonalSum_inl r x z]

/-- The canonical complement equivalence is an isometry from the orthogonal
space of `(x,0)` to the orthogonal sum of the left complement and the right
space. -/
def orthogonalSpaceOrthogonalSumInlIsometry
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    {x : V} (hx : q.IsAnisotropic x) :
    Isometry
      ((q.orthogonalSum r).orthogonalSpace (x, 0)
        hx.orthogonalSum_inl)
      ((q.orthogonalSpace x hx).orthogonalSum r) where
  toLinearEquiv := q.orthogonalSumVectorOrthogonalEquiv r x
  map_bilin y z := by
    change q.bilin y.val.1 z.val.1 + r.bilin y.val.2 z.val.2 =
      q.bilin y.val.1 z.val.1 + r.bilin y.val.2 z.val.2
    rfl

/-- When the left factor is trivial, projection to the right coordinate is a
linear equivalence. -/
def orthogonalSumSndLinearEquivOfSubsingleton
    (hV : Subsingleton V) : (V × W) ≃ₗ[K] W :=
  letI := hV
  { toFun := Prod.snd
    invFun := fun y => (0, y)
    left_inv := fun z => Prod.ext (hV.elim 0 z.1) rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- A trivial left orthogonal factor can be deleted isometrically. -/
def orthogonalSumSndIsometryOfSubsingleton
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (hV : Subsingleton V) : Isometry (q.orthogonalSum r) r where
  toLinearEquiv := orthogonalSumSndLinearEquivOfSubsingleton hV
  map_bilin z t := by
    have hz : z.1 = 0 := hV.elim _ _
    have ht : t.1 = 0 := hV.elim _ _
    change r.bilin z.2 t.2 = q.bilin z.1 t.1 + r.bilin z.2 t.2
    simp [hz, ht]

end QuadraticSpace

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The orthogonal product with a trivial left space is isometric to its
right factor, including its integral lattice. -/
noncomputable def orthogonalProductSndIsometryOfSubsingleton
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (L : Lattice K V) (M : Lattice K W) (hV : Subsingleton V) :
    Isometry (q.orthogonalSum r) r (product L M) M where
  toLinearEquiv :=
    QuadraticSpace.orthogonalSumSndLinearEquivOfSubsingleton hV
  map_bilin :=
    (q.orthogonalSumSndIsometryOfSubsingleton r hV).map_bilin
  map_mem z := by
    rw [mem_product_iff]
    constructor
    · exact And.right
    · intro hz
      refine ⟨?_, hz⟩
      have hzero : z.1 = 0 := hV.elim _ _
      rw [hzero]
      exact L.zero_mem

/-- Under the canonical complement equivalence, the projection of an
orthogonal product is the product of the projected left lattice and the
unchanged right lattice. -/
theorem map_projectedLattice_orthogonalProduct
    {x : V} (hx : q.IsAnisotropic x) :
    map (q.orthogonalSumVectorOrthogonalEquiv r x)
        ((product L M).projectedLattice (q.orthogonalSum r) (x, 0)
          hx.orthogonalSum_inl) =
      product (L.projectedLattice q x hx) M := by
  apply Lattice.ext
  ext z
  change z ∈ map (q.orthogonalSumVectorOrthogonalEquiv r x)
      ((product L M).projectedLattice (q.orthogonalSum r) (x, 0)
        hx.orthogonalSum_inl) ↔
    z ∈ product (L.projectedLattice q x hx) M
  rw [mem_map_iff, mem_product_iff]
  constructor
  · intro hz
    rcases (mem_projectedLattice_iff (q.orthogonalSum r)
      (product L M) (x, 0) hx.orthogonalSum_inl _).1 hz with
      ⟨y, hy, hprojection⟩
    have hyProduct := mem_product_iff.mp hy
    have hprojection' := congrArg
      (q.orthogonalSumVectorOrthogonalEquiv r x) hprojection
    rw [LinearEquiv.apply_symm_apply,
      q.orthogonalSumVectorOrthogonalEquiv_projectionToOrthogonal
        r hx y] at hprojection'
    refine ⟨?_, ?_⟩
    · apply (mem_projectedLattice_iff q L x hx z.1).2
      exact ⟨y.1, hyProduct.1, congrArg Prod.fst hprojection'⟩
    · have hsnd : y.2 = z.2 := by
        simpa using congrArg Prod.snd hprojection'
      rw [← hsnd]
      exact hyProduct.2
  · rintro ⟨hzLeft, hzRight⟩
    rcases (mem_projectedLattice_iff q L x hx z.1).1 hzLeft with
      ⟨y, hy, hprojection⟩
    apply (mem_projectedLattice_iff (q.orthogonalSum r)
      (product L M) (x, 0) hx.orthogonalSum_inl _).2
    refine ⟨(y, z.2), mem_product_iff.mpr ⟨hy, hzRight⟩, ?_⟩
    apply (q.orthogonalSumVectorOrthogonalEquiv r x).injective
    rw [LinearEquiv.apply_symm_apply,
      q.orthogonalSumVectorOrthogonalEquiv_projectionToOrthogonal
        r hx (y, z.2), hprojection]

/-- The projected orthogonal product is canonically isometric to the product
of the projected left lattice and the unchanged right lattice. -/
noncomputable def projectedOrthogonalProductIsometry
    {x : V} (hx : q.IsAnisotropic x) :
    Isometry
      ((q.orthogonalSum r).orthogonalSpace (x, 0)
        hx.orthogonalSum_inl)
      ((q.orthogonalSpace x hx).orthogonalSum r)
      ((product L M).projectedLattice (q.orthogonalSum r) (x, 0)
        hx.orthogonalSum_inl)
      (product (L.projectedLattice q x hx) M) where
  toLinearEquiv := q.orthogonalSumVectorOrthogonalEquiv r x
  map_bilin y z := by
    change q.bilin y.val.1 z.val.1 + r.bilin y.val.2 z.val.2 =
      q.bilin y.val.1 z.val.1 + r.bilin y.val.2 z.val.2
    rfl
  map_mem z := by
    rw [← map_mem_map_iff (q.orthogonalSumVectorOrthogonalEquiv r x)
      ((product L M).projectedLattice (q.orthogonalSum r) (x, 0)
        hx.orthogonalSum_inl) z,
      map_projectedLattice_orthogonalProduct hx]

end Lattice

end Bong
