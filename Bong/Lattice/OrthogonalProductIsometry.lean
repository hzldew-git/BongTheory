/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.OrthogonalSum
import Bong.Bong.Representation
import Bong.Lattice.Isometry
import Bong.Lattice.Product
import Mathlib.LinearAlgebra.Determinant

/-!
# Products of lattice isometries
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w z v' w'

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {V' : Type v'} [AddCommGroup V'] [Module K V']
  {W' : Type w'} [AddCommGroup W'] [Module K W']
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K Z}
  {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
  {L : Lattice K V} {M : Lattice K W}
  {N : Lattice K Z}
  {L' : Lattice K V'} {M' : Lattice K W'}

/-- Componentwise product of two lattice isometries.  This basic name is
kept distinct from the paper-specific helper historically used in the proof
of Lemma 7.10. -/
noncomputable def Isometry.orthogonalProductBasic
    (f : Isometry q q' L L') (g : Isometry r r' M M') :
    Isometry (q.orthogonalSum r) (q'.orthogonalSum r')
      (product L M) (product L' M') where
  toLinearEquiv := f.toLinearEquiv.prodCongr g.toLinearEquiv
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.orthogonalSum_bilin_apply,
      LinearEquiv.prodCongr_apply]
    rw [f.map_bilin, g.map_bilin]
  map_mem := by
    intro x
    rw [mem_product_iff, mem_product_iff]
    simp only [LinearEquiv.prodCongr_apply]
    exact and_congr (f.map_mem x.1) (g.map_mem x.2)

@[simp]
theorem Isometry.orthogonalProductBasic_apply
    (f : Isometry q q' L L') (g : Isometry r r' M M') (x : V × W) :
    (f.orthogonalProductBasic g).toLinearEquiv x =
      (f.toLinearEquiv x.1, g.toLinearEquiv x.2) :=
  rfl

/-- The determinant of a componentwise product is the product of the two
component determinants. -/
theorem Isometry.det_orthogonalProductBasic
    {q₁ q₂ : QuadraticSpace K V} {L₁ L₂ : Lattice K V}
    {r₁ r₂ : QuadraticSpace K W} {M₁ M₂ : Lattice K W}
    (f : Isometry q₁ q₂ L₁ L₂)
    (g : Isometry r₁ r₂ M₁ M₂) :
    LinearEquiv.det (f.orthogonalProductBasic g).toLinearEquiv =
      LinearEquiv.det f.toLinearEquiv * LinearEquiv.det g.toLinearEquiv := by
  letI : Module.Finite K V := L₁.moduleFinite
  letI : Module.Finite K W := M₁.moduleFinite
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_mul]
  change LinearMap.det
      (f.toLinearEquiv.toLinearMap.prodMap g.toLinearEquiv.toLinearMap) =
    LinearMap.det f.toLinearEquiv.toLinearMap *
      LinearMap.det g.toLinearEquiv.toLinearMap
  exact LinearMap.det_prodMap _ _

/-- Exchange the two factors of a concrete orthogonal product. -/
noncomputable def orthogonalProductSwap :
    Isometry (q.orthogonalSum r) (r.orthogonalSum q)
      (product L M) (product M L) where
  toLinearEquiv := LinearEquiv.prodComm K V W
  map_bilin := by
    intro x y
    change r.bilin x.2 y.2 + q.bilin x.1 y.1 =
      q.bilin x.1 y.1 + r.bilin x.2 y.2
    exact add_comm _ _
  map_mem := by
    intro x
    change x.1 ∈ L ∧ x.2 ∈ M ↔ x.2 ∈ M ∧ x.1 ∈ L
    exact and_comm

@[simp]
theorem orthogonalProductSwap_apply (x : V × W) :
    (orthogonalProductSwap (q := q) (r := r)
      (L := L) (M := M)).toLinearEquiv x = (x.2, x.1) :=
  rfl

/-- Reassociate a concrete three-factor orthogonal product from
`(L ⊥ M) ⊥ N` to `L ⊥ (M ⊥ N)`. -/
noncomputable def orthogonalProductAssoc :
    Isometry ((q.orthogonalSum r).orthogonalSum s)
      (q.orthogonalSum (r.orthogonalSum s))
      (product (product L M) N) (product L (product M N)) where
  toLinearEquiv := LinearEquiv.prodAssoc K V W Z
  map_bilin := by
    intro x y
    change
      q.bilin x.1.1 y.1.1 +
          (r.bilin x.1.2 y.1.2 + s.bilin x.2 y.2) =
        (q.bilin x.1.1 y.1.1 + r.bilin x.1.2 y.1.2) +
          s.bilin x.2 y.2
    ring
  map_mem := by
    intro x
    change
      (x.1.1 ∈ L ∧ x.1.2 ∈ M) ∧ x.2 ∈ N ↔
        x.1.1 ∈ L ∧ x.1.2 ∈ M ∧ x.2 ∈ N
    tauto

@[simp]
theorem orthogonalProductAssoc_apply (x : (V × W) × Z) :
    (orthogonalProductAssoc (q := q) (r := r) (s := s)
      (L := L) (M := M) (N := N)).toLinearEquiv x =
      (x.1.1, (x.1.2, x.2)) :=
  rfl

/-- Exchange the first two factors while retaining a third factor on the
right.  This is the permutation needed for the Type-I construction in
Beli (2019), Lemma 7.14(ii). -/
noncomputable def orthogonalProductRotateLeft :
    Isometry (q.orthogonalSum (r.orthogonalSum s))
      ((r.orthogonalSum q).orthogonalSum s)
      (product L (product M N)) (product (product M L) N) where
  toLinearEquiv :=
    (LinearEquiv.prodAssoc K V W Z).symm.trans
      ((LinearEquiv.prodComm K V W).prodCongr
        (LinearEquiv.refl K Z))
  map_bilin := by
    intro x y
    change
      (r.bilin x.2.1 y.2.1 + q.bilin x.1 y.1) +
          s.bilin x.2.2 y.2.2 =
        q.bilin x.1 y.1 +
          (r.bilin x.2.1 y.2.1 + s.bilin x.2.2 y.2.2)
    ring
  map_mem := by
    intro x
    change
      x.1 ∈ L ∧ x.2.1 ∈ M ∧ x.2.2 ∈ N ↔
        (x.2.1 ∈ M ∧ x.1 ∈ L) ∧ x.2.2 ∈ N
    tauto

@[simp]
theorem orthogonalProductRotateLeft_apply (x : V × (W × Z)) :
    (orthogonalProductRotateLeft (q := q) (r := r) (s := s)
      (L := L) (M := M) (N := N)).toLinearEquiv x =
      ((x.2.1, x.1), x.2.2) :=
  rfl

/-- Componentwise product of two integral lattice representations. -/
def Representation.orthogonalProductBasic
    (f : Representation q q' L L') (g : Representation r r' M M') :
    Representation (q.orthogonalSum r) (q'.orthogonalSum r')
      (product L M) (product L' M') where
  toLinearMap :=
    { toFun := fun x ↦ (f.toLinearMap x.1, g.toLinearMap x.2)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro c x
        ext <;> simp }
  injective := by
    intro x y hxy
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst hxy)
    · exact g.injective (congrArg Prod.snd hxy)
  map_bilin := by
    intro x y
    change
      q'.bilin (f.toLinearMap x.1) (f.toLinearMap y.1) +
          r'.bilin (g.toLinearMap x.2) (g.toLinearMap y.2) =
        q.bilin x.1 y.1 + r.bilin x.2 y.2
    rw [f.map_bilin, g.map_bilin]
  map_mem := by
    intro x hx
    rw [mem_product_iff] at hx ⊢
    exact ⟨f.map_mem hx.1, g.map_mem hx.2⟩

@[simp]
theorem Representation.orthogonalProductBasic_apply
    (f : Representation q q' L L') (g : Representation r r' M M')
    (x : V × W) :
    (f.orthogonalProductBasic g).toLinearMap x =
      (f.toLinearMap x.1, g.toLinearMap x.2) :=
  rfl

/-- Orthogonal products preserve integral representability componentwise. -/
theorem Represents.orthogonalProductBasic
    (hV : Represents q' q L' L) (hW : Represents r' r M' M) :
    Represents (q'.orthogonalSum r') (q.orthogonalSum r)
      (product L' M') (product L M) := by
  rcases hV with ⟨f⟩
  rcases hW with ⟨g⟩
  exact ⟨f.orthogonalProductBasic g⟩

end Lattice

end Bong
