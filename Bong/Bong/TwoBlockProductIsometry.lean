/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44
import Bong.Lattice.Product
import Bong.QuadraticSpace.OrthogonalSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Product realization of a two-block BONG split

A `TwoBlockSplitWitness` records an integral orthogonal decomposition into
two consecutive BONG segments.  This file turns that record into the actual
lattice isometry from the concrete orthogonal product of the two segment
lattices to the original lattice.
-/

namespace Bong

open Dyadic
open Module

universe u v

namespace BONG.TwoBlockSplitWitness

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n cut : Nat}
  {b : BONG V q L n} {hcut : cut ≤ n}

/-- The two segment carriers are orthogonal in the ambient quadratic
space. -/
theorem left_right_orthogonal
    (S : TwoBlockSplitWitness b cut hcut)
    (x : S.left.carrier) (y : S.right.carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  have h := S.decomposition.orthogonal
    (0 : Fin 2) (1 : Fin 2) (by decide)
  rw [S.component_zero, S.component_one] at h
  exact h x y

/-- Orthogonality in the reverse order. -/
theorem right_left_orthogonal
    (S : TwoBlockSplitWitness b cut hcut)
    (y : S.right.carrier) (x : S.left.carrier) :
    q.bilin (y : V) (x : V) = 0 := by
  rw [q.isSymm.eq]
  exact S.left_right_orthogonal x y

/-- The two consecutive coordinate carriers are complementary. -/
theorem carriers_isCompl
    (S : TwoBlockSplitWitness b cut hcut) :
    IsCompl S.left.carrier S.right.carrier := by
  letI : Module.Finite K V := L.moduleFinite
  apply (Submodule.isCompl_iff_disjoint
    S.left.carrier S.right.carrier ?_).2
  · rw [disjoint_iff_inf_le]
    intro z hz
    have hzLeft : z ∈ S.left.carrier := hz.1
    have hzRight : z ∈ S.right.carrier := hz.2
    let zLeft : S.left.carrier := ⟨z, hzLeft⟩
    let zRight : S.right.carrier := ⟨z, hzRight⟩
    have hzero : zLeft = 0 := by
      apply S.left.nondegenerate.1 zLeft
      intro y
      change q.bilin (z : V) (y : V) = 0
      exact S.right_left_orthogonal zRight y
    change z = 0
    exact congrArg Subtype.val hzero
  · rw [S.left.carrier_eq_segmentCarrier,
      S.right.carrier_eq_segmentCarrier,
      b.finrank_segmentCarrier,
      b.finrank_segmentCarrier,
      ← b.length_eq_finrank]
    omega

/-- The complementary-carrier equivalence, concretely `(x,y) ↦ x+y`. -/
noncomputable def toAmbientLinearEquiv
    (S : TwoBlockSplitWitness b cut hcut) :
    (S.left.carrier × S.right.carrier) ≃ₗ[K] V :=
  S.left.carrier.prodEquivOfIsCompl S.right.carrier S.carriers_isCompl

@[simp]
theorem toAmbientLinearEquiv_apply
    (S : TwoBlockSplitWitness b cut hcut)
    (z : S.left.carrier × S.right.carrier) :
    S.toAmbientLinearEquiv z = (z.1 : V) + (z.2 : V) :=
  rfl

/-- The integral sum recorded by the split witness is precisely the sum of
the two segment ambient submodules. -/
theorem ambientSubmodule_sup_eq
    (S : TwoBlockSplitWitness b cut hcut) :
    S.left.toQuadraticSublattice.ambientSubmodule ⊔
        S.right.toQuadraticSublattice.ambientSubmodule =
      L.toSubmodule := by
  have h := S.decomposition.sum_eq
  calc
    S.left.toQuadraticSublattice.ambientSubmodule ⊔
        S.right.toQuadraticSublattice.ambientSubmodule =
        (⨆ i : Fin 2,
          (S.decomposition.component i).ambientSubmodule) := by
      apply le_antisymm
      · apply sup_le
        · rw [← S.component_zero]
          exact le_iSup (fun i : Fin 2 ↦
            (S.decomposition.component i).ambientSubmodule) 0
        · rw [← S.component_one]
          exact le_iSup (fun i : Fin 2 ↦
            (S.decomposition.component i).ambientSubmodule) 1
      · apply iSup_le
        rw [Fin.forall_fin_two]
        constructor
        · rw [S.component_zero]
          exact le_sup_left
        · rw [S.component_one]
          exact le_sup_right
    _ = L.toSubmodule := h

/-- A two-block split is the concrete orthogonal product of its consecutive
segment lattices. -/
noncomputable def toProductLatticeIsometry
    (S : TwoBlockSplitWitness b cut hcut) :
    Lattice.Isometry
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      q
      (Lattice.product S.left.lattice S.right.lattice)
      L where
  toLinearEquiv := S.toAmbientLinearEquiv
  map_bilin := by
    intro x y
    change q.bilin ((x.1 : V) + (x.2 : V))
        ((y.1 : V) + (y.2 : V)) =
      q.bilin (x.1 : V) (y.1 : V) +
        q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    rw [S.left_right_orthogonal x.1 y.2,
      S.right_left_orthogonal x.2 y.1]
    simp
  map_mem := by
    intro z
    rw [Lattice.mem_product_iff]
    constructor
    · intro hz
      change S.toAmbientLinearEquiv z ∈ L.toSubmodule
      rw [← S.ambientSubmodule_sup_eq]
      rw [Submodule.mem_sup]
      refine ⟨(z.1 : V), ?_, (z.2 : V), ?_, ?_⟩
      · rw [Lattice.QuadraticSublattice.mem_ambientSubmodule_iff]
        exact ⟨z.1, hz.1, rfl⟩
      · rw [Lattice.QuadraticSublattice.mem_ambientSubmodule_iff]
        exact ⟨z.2, hz.2, rfl⟩
      · rfl
    · intro hz
      have hzSup : S.toAmbientLinearEquiv z ∈
          S.left.toQuadraticSublattice.ambientSubmodule ⊔
            S.right.toQuadraticSublattice.ambientSubmodule := by
        rw [S.ambientSubmodule_sup_eq]
        exact hz
      rw [Submodule.mem_sup] at hzSup
      rcases hzSup with ⟨x, hx, y, hy, hxy⟩
      rw [Lattice.QuadraticSublattice.mem_ambientSubmodule_iff] at hx hy
      rcases hx with ⟨xLeft, hxLeft, rfl⟩
      rcases hy with ⟨yRight, hyRight, rfl⟩
      change xLeft ∈ S.left.lattice at hxLeft
      change yRight ∈ S.right.lattice at hyRight
      have hpair : (xLeft, yRight) = z := by
        apply S.toAmbientLinearEquiv.injective
        change (xLeft : V) + (yRight : V) =
          S.toAmbientLinearEquiv z
        exact hxy
      have hfst := congrArg Prod.fst hpair
      have hsnd := congrArg Prod.snd hpair
      change xLeft = z.1 at hfst
      change yRight = z.2 at hsnd
      constructor
      · rw [← hfst]
        exact hxLeft
      · rw [← hsnd]
        exact hyRight

/-- The inverse product isometry sends a vector in the left carrier to the
literal left coordinate. -/
@[simp]
theorem toProductLatticeIsometry_symm_apply_left
    (S : TwoBlockSplitWitness b cut hcut) (x : S.left.carrier) :
    S.toProductLatticeIsometry.symm.toLinearEquiv (x : V) = (x, 0) := by
  apply S.toProductLatticeIsometry.toLinearEquiv.injective
  change S.toProductLatticeIsometry.toLinearEquiv
      (S.toProductLatticeIsometry.toLinearEquiv.symm (x : V)) =
    S.toProductLatticeIsometry.toLinearEquiv (x, 0)
  rw [S.toProductLatticeIsometry.toLinearEquiv.apply_symm_apply]
  change (x : V) = (x : V) + (0 : V)
  simp

/-- The inverse product isometry sends a vector in the right carrier to the
literal right coordinate. -/
@[simp]
theorem toProductLatticeIsometry_symm_apply_right
    (S : TwoBlockSplitWitness b cut hcut) (y : S.right.carrier) :
    S.toProductLatticeIsometry.symm.toLinearEquiv (y : V) = (0, y) := by
  apply S.toProductLatticeIsometry.toLinearEquiv.injective
  change S.toProductLatticeIsometry.toLinearEquiv
      (S.toProductLatticeIsometry.toLinearEquiv.symm (y : V)) =
    S.toProductLatticeIsometry.toLinearEquiv (0, y)
  rw [S.toProductLatticeIsometry.toLinearEquiv.apply_symm_apply]
  change (y : V) = (0 : V) + (y : V)
  simp

/-- The left segment lattice embeds in the original lattice. -/
theorem left_contained
    (S : TwoBlockSplitWitness b cut hcut)
    (y : S.left.carrier) (hy : y ∈ S.left.lattice) :
    (y : V) ∈ L := by
  have h := (S.toProductLatticeIsometry.map_mem (y, 0)).mp
    (Lattice.mem_product_iff.mpr ⟨hy, S.right.lattice.zero_mem⟩)
  change S.toAmbientLinearEquiv (y, 0) ∈ L at h
  change (y : V) + 0 ∈ L at h
  simpa using h

/-- The right segment lattice embeds in the original lattice. -/
theorem right_contained
    (S : TwoBlockSplitWitness b cut hcut)
    (y : S.right.carrier) (hy : y ∈ S.right.lattice) :
    (y : V) ∈ L := by
  have h := (S.toProductLatticeIsometry.map_mem (0, y)).mp
    (Lattice.mem_product_iff.mpr ⟨S.left.lattice.zero_mem, hy⟩)
  change S.toAmbientLinearEquiv (0, y) ∈ L at h
  change (0 : V) + (y : V) ∈ L at h
  simpa using h

/-- Every original-lattice vector lying in the left carrier belongs to the
left segment lattice. -/
theorem left_contains_parent
    (S : TwoBlockSplitWitness b cut hcut)
    (y : S.left.carrier) (hy : (y : V) ∈ L) :
    y ∈ S.left.lattice := by
  have hambient : S.toAmbientLinearEquiv (y, 0) ∈ L := by
    change (y : V) + 0 ∈ L
    simpa using hy
  have h := (S.toProductLatticeIsometry.map_mem (y, 0)).mpr hambient
  exact (Lattice.mem_product_iff.mp h).1

/-- A two-block split canonically upgrades its left segment to a prefix
witness. -/
noncomputable def leftPrefixWitness
    (S : TwoBlockSplitWitness b cut hcut) :
    PrefixWitness b cut hcut where
  toSegmentWitness := S.left
  contained := S.left_contained
  contains_parent := S.left_contains_parent

end BONG.TwoBlockSplitWitness

end Bong
