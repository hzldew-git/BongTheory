/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44Proof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The three-block splitting construction in Beli (2003), Corollary 4.4

This file constructs the ambient isometry for the consecutive prefix, binary
pair, and suffix at a selected adjacent pair.  It is the geometric core of the
unconditional proof of Corollary 4.4(ii).
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Immediately before a strict descent, every earlier order is bounded by
the order at the left endpoint.  This is the parity-chain consequence of
goodness used in Corollary 4.4(ii). -/
theorem order_le_of_lt_index_of_next_lt
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.val + 1 < n)
    (hdesc : b.order ⟨i.val + 1, hi⟩ < b.order i)
    (j : Fin n) (hji : j.val < i.val) :
    b.order j ≤ b.order i := by
  by_cases hiOne : i.val = 1
  · have hjZero : j.val = 0 := by omega
    let zero : Fin n := ⟨0, by omega⟩
    have hzeroStep : zero.val + 2 < n := by
      dsimp only [zero]
      omega
    have hgoodStep := hgood zero hzeroStep
    have hzeroTwo : b.order j ≤ b.order ⟨i.val + 1, hi⟩ := by
      convert hgoodStep using 1 <;>
        apply congrArg b.order <;>
        apply Fin.ext <;>
        dsimp only [zero] <;>
        omega
    exact hzeroTwo.trans hdesc.le
  · have hiTwo : 2 ≤ i.val := by omega
    let g : GoodBONG q L n := ⟨b, hgood⟩
    have hpenultimate :
        g.order ⟨i.val - 2, by omega⟩ ≤ b.order i := by
      change b.order ⟨i.val - 2, by omega⟩ ≤ b.order i
      let pen : Fin n := ⟨i.val - 2, by omega⟩
      have hpenStep : pen.val + 2 < n := by
        dsimp only [pen]
        omega
      have h := hgood pen hpenStep
      have hindex : (⟨pen.val + 2, hpenStep⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp only [pen]
        omega
      rw [hindex] at h
      simpa only [pen] using h
    have hlast : g.order ⟨i.val - 1, by omega⟩ ≤ b.order i := by
      change b.order ⟨i.val - 1, by omega⟩ ≤ b.order i
      let last : Fin n := ⟨i.val - 1, by omega⟩
      have hlastStep : last.val + 2 < n := by
        dsimp only [last]
        omega
      have h := hgood last hlastStep
      have hindex : (⟨last.val + 2, hlastStep⟩ : Fin n) =
          ⟨i.val + 1, hi⟩ := by
        apply Fin.ext
        dsimp only [last]
        omega
      rw [hindex] at h
      exact h.trans hdesc.le
    have h := g.order_le_of_lt_cut_of_last_two_le i.val hiTwo
      (by omega) (b.order i) hpenultimate hlast j hji
    exact h

/-- The sum map from the product of the three consecutive coordinate
carriers to the ambient quadratic space. -/
noncomputable def threeBlockSumLinearMap
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    (((b.segmentWitness 0 start (by omega)).carrier ×
        (b.segmentWitness start 2 (by omega)).carrier) ×
      (b.segmentWitness (start + 2) (n - (start + 2)) (by omega)).carrier) →ₗ[K]
      V where
  toFun z := (z.1.1 : V) + (z.1.2 : V) + (z.2 : V)
  map_add' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    abel
  map_smul' := by
    intro a x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add]
    simp

/-- The three-block sum map is injective because the three carriers are
pairwise orthogonal and each restricted form is nondegenerate. -/
theorem threeBlockSumLinearMap_injective
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    Function.Injective (b.threeBlockSumLinearMap start hpair) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  have hsum : (z.1.1 : V) + (z.1.2 : V) + (z.2 : V) = 0 := by
    exact hz
  have hxzero : z.1.1 = 0 := by
    apply left.nondegenerate.1
    intro w
    change q.bilin (z.1.1 : V) (w : V) = 0
    have hyw : q.bilin (z.1.2 : V) (w : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        0 start start 2 (by omega) (by omega) (by omega) w z.1.2
    have hzw : q.bilin (z.2 : V) (w : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        0 start (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) w z.2
    have hbil := congrArg (fun t : V => q.bilin t (w : V)) hsum
    simpa only [map_add, LinearMap.add_apply, map_zero,
      LinearMap.zero_apply, hyw, hzw, add_zero] using hbil
  have hyzero : z.1.2 = 0 := by
    apply pair.nondegenerate.1
    intro w
    change q.bilin (z.1.2 : V) (w : V) = 0
    have hxw : q.bilin (z.1.1 : V) (w : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        0 start start 2 (by omega) (by omega) (by omega) z.1.1 w
    have hzw : q.bilin (z.2 : V) (w : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        start 2 (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) w z.2
    have hbil := congrArg (fun t : V => q.bilin t (w : V)) hsum
    simpa only [map_add, LinearMap.add_apply, map_zero,
      LinearMap.zero_apply, hxw, hzw, zero_add, add_zero] using hbil
  have hzzero : z.2 = 0 := by
    apply right.nondegenerate.1
    intro w
    change q.bilin (z.2 : V) (w : V) = 0
    have hxw : q.bilin (z.1.1 : V) (w : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        0 start (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) z.1.1 w
    have hyw : q.bilin (z.1.2 : V) (w : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        start 2 (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) z.1.2 w
    have hbil := congrArg (fun t : V => q.bilin t (w : V)) hsum
    simpa only [map_add, LinearMap.add_apply, map_zero,
      LinearMap.zero_apply, hxw, hyw, zero_add, add_zero] using hbil
  exact Prod.ext (Prod.ext hxzero hyzero) hzzero

/-- The sum map is a linear equivalence: its source has the same dimension as
the ambient BONG space. -/
noncomputable def threeBlockSumLinearEquiv
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    (((b.segmentWitness 0 start (by omega)).carrier ×
        (b.segmentWitness start 2 (by omega)).carrier) ×
      (b.segmentWitness (start + 2) (n - (start + 2)) (by omega)).carrier) ≃ₗ[K]
      V := by
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  letI : FiniteDimensional K V := b.basis.finiteDimensional_of_finite
  apply (b.threeBlockSumLinearMap start hpair).linearEquivOfInjective
    (b.threeBlockSumLinearMap_injective start hpair)
  rw [finrank_prod, finrank_prod,
    left.carrier_eq_segmentCarrier, pair.carrier_eq_segmentCarrier,
    right.carrier_eq_segmentCarrier,
    b.finrank_segmentCarrier, b.finrank_segmentCarrier,
    b.finrank_segmentCarrier, ← b.length_eq_finrank]
  omega

@[simp]
theorem threeBlockSumLinearEquiv_apply
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n)
    (z : ((b.segmentWitness 0 start (by omega)).carrier ×
        (b.segmentWitness start 2 (by omega)).carrier) ×
      (b.segmentWitness (start + 2) (n - (start + 2)) (by omega)).carrier) :
    b.threeBlockSumLinearEquiv start hpair z =
      (z.1.1 : V) + (z.1.2 : V) + (z.2 : V) :=
  rfl

/-- The three-block sum equivalence is an isometry from the iterated
orthogonal product of the restricted forms. -/
noncomputable def threeBlockSumIsometry
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    (((q.restrict (b.segmentWitness 0 start (by omega)).carrier
          (b.segmentWitness 0 start (by omega)).nondegenerate).orthogonalSum
        (q.restrict (b.segmentWitness start 2 (by omega)).carrier
          (b.segmentWitness start 2 (by omega)).nondegenerate)).orthogonalSum
      (q.restrict
        (b.segmentWitness (start + 2) (n - (start + 2)) (by omega)).carrier
        (b.segmentWitness (start + 2) (n - (start + 2))
          (by omega)).nondegenerate)).Isometry q where
  toLinearEquiv := b.threeBlockSumLinearEquiv start hpair
  map_bilin := by
    intro x y
    change q.bilin ((x.1.1 : V) + (x.1.2 : V) + (x.2 : V))
        ((y.1.1 : V) + (y.1.2 : V) + (y.2 : V)) =
      (q.bilin (x.1.1 : V) (y.1.1 : V) +
        q.bilin (x.1.2 : V) (y.1.2 : V)) +
        q.bilin (x.2 : V) (y.2 : V)
    have hxyLeftPair : q.bilin (x.1.1 : V) (y.1.2 : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        0 start start 2 (by omega) (by omega) (by omega) x.1.1 y.1.2
    have hxyLeftRight : q.bilin (x.1.1 : V) (y.2 : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        0 start (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) x.1.1 y.2
    have hxyPairRight : q.bilin (x.1.2 : V) (y.2 : V) = 0 :=
      b.segmentCarriers_orthogonal_of_end_le_start
        start 2 (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) x.1.2 y.2
    have hxyPairLeft : q.bilin (x.1.2 : V) (y.1.1 : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        0 start start 2 (by omega) (by omega) (by omega) y.1.1 x.1.2
    have hxyRightLeft : q.bilin (x.2 : V) (y.1.1 : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        0 start (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) y.1.1 x.2
    have hxyRightPair : q.bilin (x.2 : V) (y.1.2 : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal_of_end_le_start
        start 2 (start + 2) (n - (start + 2))
        (by omega) (by omega) (by omega) y.1.2 x.2
    simp only [map_add, LinearMap.add_apply, hxyLeftPair, hxyLeftRight,
      hxyPairRight, hxyPairLeft, hxyRightLeft, hxyRightPair, add_zero,
      zero_add]

/-- The product of the three canonical consecutive segment lattices. -/
noncomputable def threeBlockProductLattice
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    Lattice K (((b.segmentWitness 0 start (by omega)).carrier ×
        (b.segmentWitness start 2 (by omega)).carrier) ×
      (b.segmentWitness (start + 2) (n - (start + 2))
        (by omega)).carrier) :=
  Lattice.product
    (Lattice.product
      (b.segmentWitness 0 start (by omega)).lattice
      (b.segmentWitness start 2 (by omega)).lattice)
    (b.segmentWitness (start + 2) (n - (start + 2)) (by omega)).lattice

/-- The three canonical segment components, in their original ambient
quadratic space. -/
noncomputable def threeBlockComponent
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    Fin 3 → Lattice.QuadraticSublattice q :=
  fun i => Fin.cases
    (b.segmentWitness 0 start (by omega)).toQuadraticSublattice
    (fun j => Fin.cases
      (b.segmentWitness start 2 (by omega)).toQuadraticSublattice
      (fun _ => (b.segmentWitness (start + 2) (n - (start + 2))
        (by omega)).toQuadraticSublattice) j) i

/-- The product lattice transported to the original ambient space by the
three-block sum isometry. -/
noncomputable def threeBlockMappedLattice
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    Lattice K V :=
  Lattice.map (b.threeBlockSumIsometry start hpair).toLinearEquiv
    (b.threeBlockProductLattice start hpair)

/-- The join of the three segment components is exactly the transported
three-fold product lattice. -/
theorem iSup_threeBlockComponent_eq_mappedLattice
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n) :
    (⨆ i, (b.threeBlockComponent start hpair i).ambientSubmodule) =
      (b.threeBlockMappedLattice start hpair).toSubmodule := by
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  let f := b.threeBlockSumIsometry start hpair
  let prefixLattice := Lattice.product left.lattice pair.lattice
  let productLattice := Lattice.product prefixLattice right.lattice
  let mappedLattice := Lattice.map f.toLinearEquiv productLattice
  let leftComponent := left.toQuadraticSublattice
  let pairComponent := pair.toQuadraticSublattice
  let rightComponent := right.toQuadraticSublattice
  let component : Fin 3 → Lattice.QuadraticSublattice q :=
    fun i => Fin.cases leftComponent
      (fun j => Fin.cases pairComponent (fun _ => rightComponent) j) i
  change (⨆ i, (component i).ambientSubmodule) = mappedLattice.toSubmodule
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · change leftComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hprefix : (x, 0) ∈ prefixLattice :=
        Lattice.mem_product_iff.mpr ⟨hx, pair.lattice.zero_mem⟩
      have htriple : ((x, 0), 0) ∈ productLattice :=
        Lattice.mem_product_iff.mpr ⟨hprefix, right.lattice.zero_mem⟩
      have hmap := (Lattice.map_mem_map_iff
        f.toLinearEquiv productLattice ((x, 0), 0)).2 htriple
      change f.toLinearEquiv ((x, 0), 0) ∈ mappedLattice at hmap
      change (x : V) + 0 + 0 ∈ mappedLattice at hmap
      simpa using hmap
    · change pairComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hprefix : (0, y) ∈ prefixLattice :=
        Lattice.mem_product_iff.mpr ⟨left.lattice.zero_mem, hy⟩
      have htriple : ((0, y), 0) ∈ productLattice :=
        Lattice.mem_product_iff.mpr ⟨hprefix, right.lattice.zero_mem⟩
      have hmap := (Lattice.map_mem_map_iff
        f.toLinearEquiv productLattice ((0, y), 0)).2 htriple
      change f.toLinearEquiv ((0, y), 0) ∈ mappedLattice at hmap
      change 0 + (y : V) + 0 ∈ mappedLattice at hmap
      simpa using hmap
    · change rightComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      have hprefix : (0, 0) ∈ prefixLattice :=
        Lattice.mem_product_iff.mpr
          ⟨left.lattice.zero_mem, pair.lattice.zero_mem⟩
      have htriple : ((0, 0), w) ∈ productLattice :=
        Lattice.mem_product_iff.mpr ⟨hprefix, hw⟩
      have hmap := (Lattice.map_mem_map_iff
        f.toLinearEquiv productLattice ((0, 0), w)).2 htriple
      change f.toLinearEquiv ((0, 0), w) ∈ mappedLattice at hmap
      change 0 + 0 + (w : V) ∈ mappedLattice at hmap
      simpa using hmap
  · intro z hz
    have hzProduct : f.toLinearEquiv.symm z ∈ productLattice :=
      (Lattice.mem_map_iff f.toLinearEquiv productLattice z).1 hz
    have hzOuter := Lattice.mem_product_iff.mp hzProduct
    have hzInner := Lattice.mem_product_iff.mp hzOuter.1
    let x := (f.toLinearEquiv.symm z).1.1
    let y := (f.toLinearEquiv.symm z).1.2
    let w := (f.toLinearEquiv.symm z).2
    have hzEq : (x : V) + (y : V) + (w : V) = z := by
      change f.toLinearEquiv (f.toLinearEquiv.symm z) = z
      exact f.toLinearEquiv.apply_symm_apply z
    have hxAmbient : (x : V) ∈ leftComponent.ambientSubmodule :=
      ⟨x, hzInner.1, rfl⟩
    have hyAmbient : (y : V) ∈ pairComponent.ambientSubmodule :=
      ⟨y, hzInner.2, rfl⟩
    have hwAmbient : (w : V) ∈ rightComponent.ambientSubmodule :=
      ⟨w, hzOuter.2, rfl⟩
    rw [← hzEq]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact le_iSup (fun i => (component i).ambientSubmodule) 0 hxAmbient
      · exact le_iSup (fun i => (component i).ambientSubmodule) 1 hyAmbient
    · exact le_iSup (fun i => (component i).ambientSubmodule) 2 hwAmbient

/-- Once the transported product lattice is identified with `L`, the
canonical three segment lattices form the required split witness. -/
theorem exists_threeBlockSplit_of_mappedLattice_eq
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n)
    (hmapped : b.threeBlockMappedLattice start hpair = L) :
    Nonempty (b.ThreeBlockSplitWitness ⟨start, by omega⟩ hpair) := by
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  let component := b.threeBlockComponent start hpair
  have hsum : (⨆ i, (component i).ambientSubmodule) = L.toSubmodule := by
    rw [b.iSup_threeBlockComponent_eq_mappedLattice start hpair, hmapped]
  let decomposition : Lattice.OrthogonalDecomposition q L 3 := {
    component := component
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start start 2 (by omega) (by omega) (by omega) x y
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) x y
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start start 2 (by omega) (by omega) (by omega) y x
      · exact (hij rfl).elim
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          start 2 (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) x y
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) y x
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          start 2 (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) y x
      · exact (hij rfl).elim
    sum_eq := hsum
  }
  exact ⟨{
    leftBlock := left
    pairBlock := pair
    rightBlock := right
    decomposition := decomposition
    component_zero := rfl
    component_one := rfl
    component_two := rfl
  }⟩

/-- Three nonempty consecutive stages reconstruct the original lattice when
the orders of every earlier stage are bounded by the head order of the next
stage.  The middle stage has length two. -/
theorem exists_threeBlockSplit_of_orderBounds_of_nonemptySuffix
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n)
    (hsuffix : start + 2 < n)
    (hleftPair : ∀ i : Fin start,
      (b.segmentWitness 0 start (by omega)).bong.order i ≤
        (b.segmentWitness start 2 (by omega)).bong.order 0)
    (hleftRight : ∀ i : Fin start,
      (b.segmentWitness 0 start (by omega)).bong.order i ≤
        (b.segmentWitness (start + 2) (n - (start + 2))
          (by omega)).bong.order ⟨0, by omega⟩)
    (hpairRight : ∀ i : Fin 2,
      (b.segmentWitness start 2 (by omega)).bong.order i ≤
        (b.segmentWitness (start + 2) (n - (start + 2))
          (by omega)).bong.order ⟨0, by omega⟩) :
    Nonempty (b.ThreeBlockSplitWitness ⟨start, by omega⟩ hpair) := by
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  let f := b.threeBlockSumIsometry start hpair
  let prefixLattice := Lattice.product left.lattice pair.lattice
  let productLattice := Lattice.product prefixLattice right.lattice
  let mappedLattice := Lattice.map f.toLinearEquiv productLattice
  let F : Lattice.Isometry
      (((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict pair.carrier pair.nondegenerate)).orthogonalSum
        (q.restrict right.carrier right.nondegenerate)) q
      productLattice mappedLattice := {
    toLinearEquiv := f.toLinearEquiv
    map_bilin := f.map_bilin
    map_mem := fun z =>
      (Lattice.map_mem_map_iff f.toLinearEquiv productLattice z).symm
  }
  let prefixRaw := left.bong.orthogonalProductRight pair.bong hleftPair
  have hprefixLength : 2 + start = start + 2 := by omega
  let prefixBONG := prefixRaw.castLength hprefixLength
  have hrightPos : 0 < n - (start + 2) := by omega
  let m := n - (start + 2) - 1
  have hrightLength : n - (start + 2) = m + 1 := by
    dsimp only [m]
    omega
  let rightBONG : BONG right.carrier
      (q.restrict right.carrier right.nondegenerate) right.lattice (m + 1) :=
    right.bong.castLength hrightLength
  have hrightOrder : rightBONG.order 0 =
      right.bong.order ⟨0, hrightPos⟩ := by
    rw [BONG.order_castLength_index]
    apply congrArg right.bong.order
    apply Fin.ext
    rfl
  have hprefixRight : ∀ i : Fin (start + 2),
      prefixBONG.order i ≤ rightBONG.order 0 := by
    intro i
    rw [BONG.order_castLength_index, hrightOrder]
    let rawIndex : Fin (2 + start) :=
      ⟨i.val, by omega⟩
    change prefixRaw.order rawIndex ≤ right.bong.order ⟨0, hrightPos⟩
    by_cases hi : i.val < start
    · let j : Fin start := ⟨i.val, hi⟩
      have hindex : rawIndex = orthogonalProductLeftIndex 2 j := by
        apply Fin.ext
        rfl
      rw [hindex, order_orthogonalProductRight_left]
      exact hleftRight j
    · let j : Fin 2 := ⟨i.val - start, by omega⟩
      have hindex : rawIndex = orthogonalProductRightIndex start j := by
        apply Fin.ext
        change i.val = start + j.val
        dsimp only [j]
        omega
      rw [hindex, order_orthogonalProductRight_right]
      exact hpairRight j
  let productRaw := prefixBONG.orthogonalProductRight rightBONG hprefixRight
  have hproductLength : (m + 1) + (start + 2) = n := by
    dsimp only [m]
    omega
  let productBONG := productRaw.castLength hproductLength
  let assembled := productBONG.mapLatticeIsometry F
  have hambient : ∀ i : Fin n,
      assembled.ambientVector i = b.ambientVector i := by
    intro i
    by_cases hleft : i.val < start
    · let j : Fin start := ⟨i.val, hleft⟩
      let innerIndex : Fin (2 + start) :=
        orthogonalProductLeftIndex 2 j
      let prefixIndex : Fin (start + 2) :=
        Fin.cast hprefixLength innerIndex
      have hindex : i = Fin.cast hproductLength
          (orthogonalProductLeftIndex (m + 1) prefixIndex) := by
        apply Fin.ext
        simp only [prefixIndex, innerIndex, Fin.coe_cast,
          orthogonalProductLeftIndex_val]
        dsimp only [j]
      rw [hindex]
      simp only [assembled, BONG.ambientVector_mapLatticeIsometry,
        productBONG, BONG.ambientVector_castLength]
      have houter := ambientVector_orthogonalProductRight_left
        prefixBONG rightBONG hprefixRight prefixIndex
      change f.toLinearEquiv
          (productRaw.ambientVector
            (orthogonalProductLeftIndex (m + 1) prefixIndex)) = _
      rw [houter]
      change f.toLinearEquiv (prefixBONG.ambientVector prefixIndex, 0) = _
      have hprefixAmbient : prefixBONG.ambientVector prefixIndex =
          prefixRaw.ambientVector innerIndex := by
        rw [BONG.ambientVector_castLength]
        apply congrArg prefixRaw.ambientVector
        apply Fin.ext
        rfl
      rw [hprefixAmbient]
      have hinner := ambientVector_orthogonalProductRight_left
        left.bong pair.bong hleftPair j
      change f.toLinearEquiv ((prefixRaw.ambientVector innerIndex :
        left.carrier × pair.carrier), (0 : right.carrier)) = _
      rw [hinner]
      change (left.bong.ambientVector j : V) + 0 + 0 = _
      rw [add_zero, add_zero, left.ambientVector_eq]
      apply congrArg b.ambientVector
      apply Fin.ext
      simp [prefixIndex, innerIndex]
    · by_cases hpairIndex : i.val < start + 2
      · have hstart : start ≤ i.val := Nat.le_of_not_gt hleft
        let j : Fin 2 := ⟨i.val - start, by omega⟩
        let innerIndex : Fin (2 + start) :=
          orthogonalProductRightIndex start j
        let prefixIndex : Fin (start + 2) :=
          Fin.cast hprefixLength innerIndex
        have hindex : i = Fin.cast hproductLength
            (orthogonalProductLeftIndex (m + 1) prefixIndex) := by
          apply Fin.ext
          simp only [prefixIndex, innerIndex, Fin.coe_cast,
            orthogonalProductLeftIndex_val, orthogonalProductRightIndex_val]
          dsimp only [j]
          omega
        rw [hindex]
        simp only [assembled, BONG.ambientVector_mapLatticeIsometry,
          productBONG, BONG.ambientVector_castLength]
        have houter := ambientVector_orthogonalProductRight_left
          prefixBONG rightBONG hprefixRight prefixIndex
        change f.toLinearEquiv
            (productRaw.ambientVector
              (orthogonalProductLeftIndex (m + 1) prefixIndex)) = _
        rw [houter]
        change f.toLinearEquiv (prefixBONG.ambientVector prefixIndex, 0) = _
        have hprefixAmbient : prefixBONG.ambientVector prefixIndex =
            prefixRaw.ambientVector innerIndex := by
          rw [BONG.ambientVector_castLength]
          apply congrArg prefixRaw.ambientVector
          apply Fin.ext
          rfl
        rw [hprefixAmbient]
        have hinner := ambientVector_orthogonalProductRight_right
          left.bong pair.bong hleftPair j
        change f.toLinearEquiv ((prefixRaw.ambientVector innerIndex :
          left.carrier × pair.carrier), (0 : right.carrier)) = _
        rw [hinner]
        change 0 + (pair.bong.ambientVector j : V) + 0 = _
        rw [zero_add, add_zero, pair.ambientVector_eq]
        apply congrArg b.ambientVector
        apply Fin.ext
        dsimp only [j]
        omega
      · have hstart : start + 2 ≤ i.val := Nat.le_of_not_gt hpairIndex
        let j : Fin (m + 1) := ⟨i.val - (start + 2), by
          dsimp only [m]
          omega⟩
        have hindex : i = Fin.cast hproductLength
            (orthogonalProductRightIndex (start + 2) j) := by
          apply Fin.ext
          change i.val = start + 2 + j.val
          dsimp only [j]
          omega
        rw [hindex]
        simp only [assembled, BONG.ambientVector_mapLatticeIsometry,
          productBONG, BONG.ambientVector_castLength]
        have houter := ambientVector_orthogonalProductRight_right
          prefixBONG rightBONG hprefixRight j
        change f.toLinearEquiv
            (productRaw.ambientVector
              (orthogonalProductRightIndex (start + 2) j)) = _
        rw [houter]
        change f.toLinearEquiv (0, rightBONG.ambientVector j) = _
        have hcast := BONG.ambientVector_castLength right.bong
          hrightLength j
        change 0 + 0 + (rightBONG.ambientVector j : V) = _
        rw [zero_add, zero_add, hcast, right.ambientVector_eq]
        apply congrArg b.ambientVector
        apply Fin.ext
        simp only [SegmentWitness.sourceIndex_val, Fin.val_cast,
          orthogonalProductRightIndex_val]
  have hmapped : mappedLattice = L :=
    assembled.lattice_eq_of_ambientVector_eq b hambient
  let leftComponent := left.toQuadraticSublattice
  let pairComponent := pair.toQuadraticSublattice
  let rightComponent := right.toQuadraticSublattice
  let component : Fin 3 → Lattice.QuadraticSublattice q :=
    fun i => Fin.cases leftComponent
      (fun j => Fin.cases pairComponent (fun _ => rightComponent) j) i
  have hsum : (⨆ i, (component i).ambientSubmodule) =
      mappedLattice.toSubmodule := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · change leftComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        have hprefix : (x, 0) ∈ prefixLattice :=
          Lattice.mem_product_iff.mpr ⟨hx, pair.lattice.zero_mem⟩
        have htriple : ((x, 0), 0) ∈ productLattice :=
          Lattice.mem_product_iff.mpr ⟨hprefix, right.lattice.zero_mem⟩
        have hmap := (Lattice.map_mem_map_iff
          f.toLinearEquiv productLattice ((x, 0), 0)).2 htriple
        change f.toLinearEquiv ((x, 0), 0) ∈ mappedLattice at hmap
        change (x : V) + 0 + 0 ∈ mappedLattice at hmap
        simpa using hmap
      · change pairComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
        intro z hz
        rcases hz with ⟨y, hy, rfl⟩
        have hprefix : (0, y) ∈ prefixLattice :=
          Lattice.mem_product_iff.mpr ⟨left.lattice.zero_mem, hy⟩
        have htriple : ((0, y), 0) ∈ productLattice :=
          Lattice.mem_product_iff.mpr ⟨hprefix, right.lattice.zero_mem⟩
        have hmap := (Lattice.map_mem_map_iff
          f.toLinearEquiv productLattice ((0, y), 0)).2 htriple
        change f.toLinearEquiv ((0, y), 0) ∈ mappedLattice at hmap
        change 0 + (y : V) + 0 ∈ mappedLattice at hmap
        simpa using hmap
      · change rightComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
        intro z hz
        rcases hz with ⟨w, hw, rfl⟩
        have hprefix : (0, 0) ∈ prefixLattice :=
          Lattice.mem_product_iff.mpr
            ⟨left.lattice.zero_mem, pair.lattice.zero_mem⟩
        have htriple : ((0, 0), w) ∈ productLattice :=
          Lattice.mem_product_iff.mpr ⟨hprefix, hw⟩
        have hmap := (Lattice.map_mem_map_iff
          f.toLinearEquiv productLattice ((0, 0), w)).2 htriple
        change f.toLinearEquiv ((0, 0), w) ∈ mappedLattice at hmap
        change 0 + 0 + (w : V) ∈ mappedLattice at hmap
        simpa using hmap
    · intro z hz
      have hzProduct : f.toLinearEquiv.symm z ∈ productLattice :=
        (Lattice.mem_map_iff f.toLinearEquiv productLattice z).1 hz
      have hzOuter := Lattice.mem_product_iff.mp hzProduct
      have hzInner := Lattice.mem_product_iff.mp hzOuter.1
      let x := (f.toLinearEquiv.symm z).1.1
      let y := (f.toLinearEquiv.symm z).1.2
      let w := (f.toLinearEquiv.symm z).2
      have hzEq : (x : V) + (y : V) + (w : V) = z := by
        change f.toLinearEquiv (f.toLinearEquiv.symm z) = z
        exact f.toLinearEquiv.apply_symm_apply z
      have hxAmbient : (x : V) ∈ leftComponent.ambientSubmodule :=
        ⟨x, hzInner.1, rfl⟩
      have hyAmbient : (y : V) ∈ pairComponent.ambientSubmodule :=
        ⟨y, hzInner.2, rfl⟩
      have hwAmbient : (w : V) ∈ rightComponent.ambientSubmodule :=
        ⟨w, hzOuter.2, rfl⟩
      rw [← hzEq]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact le_iSup (fun i => (component i).ambientSubmodule) 0 hxAmbient
        · exact le_iSup (fun i => (component i).ambientSubmodule) 1 hyAmbient
      · exact le_iSup (fun i => (component i).ambientSubmodule) 2 hwAmbient
  let decomposition : Lattice.OrthogonalDecomposition q L 3 := {
    component := component
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start start 2 (by omega) (by omega) (by omega) x y
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) x y
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start start 2 (by omega) (by omega) (by omega) y x
      · exact (hij rfl).elim
      · exact b.segmentCarriers_orthogonal_of_end_le_start
          start 2 (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) x y
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          0 start (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) y x
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal_of_end_le_start
          start 2 (start + 2) (n - (start + 2))
          (by omega) (by omega) (by omega) y x
      · exact (hij rfl).elim
    sum_eq := by simpa only [hmapped] using hsum
  }
  exact ⟨{
    leftBlock := left
    pairBlock := pair
    rightBlock := right
    decomposition := decomposition
    component_zero := rfl
    component_one := rfl
    component_two := rfl
  }⟩

/-- At a terminal binary pair, concatenating the prefix and the pair already
reconstructs the whole BONG.  The canonical zero-dimensional suffix is added
through the unique product equivalence. -/
theorem threeBlockMappedLattice_eq_of_terminal_orderBounds
    (b : BONG V q L n) (start : Nat) (hpair : start + 1 < n)
    (hterminal : n = start + 2)
    (hleftPair : ∀ i : Fin start,
      (b.segmentWitness 0 start (by omega)).bong.order i ≤
        (b.segmentWitness start 2 (by omega)).bong.order 0) :
    b.threeBlockMappedLattice start hpair = L := by
  let left := b.segmentWitness 0 start (by omega)
  let pair := b.segmentWitness start 2 (by omega)
  let right := b.segmentWitness (start + 2) (n - (start + 2)) (by omega)
  let f := b.threeBlockSumIsometry start hpair
  let prefixLattice := Lattice.product left.lattice pair.lattice
  let productLattice := Lattice.product prefixLattice right.lattice
  let mappedLattice := Lattice.map f.toLinearEquiv productLattice
  change mappedLattice = L
  have hrightCarrier : right.carrier = ⊥ := by
    rw [right.carrier_eq_segmentCarrier]
    apply le_antisymm
    · rw [BONG.segmentCarrier, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exfalso
      have hj := j.isLt
      omega
    · exact bot_le
  letI : Subsingleton right.carrier := {
    allEq := by
      intro x y
      apply Subtype.ext
      have hxmem : (x : V) ∈ (⊥ : Submodule K V) := by
        rw [← hrightCarrier]
        exact x.property
      have hymem : (y : V) ∈ (⊥ : Submodule K V) := by
        rw [← hrightCarrier]
        exact y.property
      have hxzero : (x : V) = 0 := by simpa using hxmem
      have hyzero : (y : V) = 0 := by simpa using hymem
      exact hxzero.trans hyzero.symm
  }
  letI : Unique right.carrier := {
    default := 0
    uniq := fun x => Subsingleton.elim x 0
  }
  let e : (left.carrier × pair.carrier) ≃ₗ[K]
      ((left.carrier × pair.carrier) × right.carrier) :=
    (LinearEquiv.prodUnique (R := K)
      (M := left.carrier × pair.carrier) (M₂ := right.carrier)).symm
  have hdefault : (default : right.carrier) = 0 :=
    Subsingleton.elim default 0
  let E : ((q.restrict left.carrier left.nondegenerate).orthogonalSum
      (q.restrict pair.carrier pair.nondegenerate)).Isometry
      (((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict pair.carrier pair.nondegenerate)).orthogonalSum
        (q.restrict right.carrier right.nondegenerate)) := {
    toLinearEquiv := e
    map_bilin := by
      intro x y
      simp [e, hdefault]
  }
  let G : Lattice.Isometry
      ((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict pair.carrier pair.nondegenerate))
      (((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict pair.carrier pair.nondegenerate)).orthogonalSum
        (q.restrict right.carrier right.nondegenerate))
      prefixLattice productLattice := {
    toLinearEquiv := e
    map_bilin := E.map_bilin
    map_mem := by
      intro x
      simp only [e, LinearEquiv.prodUnique_symm_apply, hdefault]
      change x ∈ prefixLattice ↔
        x ∈ prefixLattice ∧ (0 : right.carrier) ∈ right.lattice
      simp
  }
  let F : Lattice.Isometry
      (((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict pair.carrier pair.nondegenerate)).orthogonalSum
        (q.restrict right.carrier right.nondegenerate)) q
      productLattice mappedLattice := {
    toLinearEquiv := f.toLinearEquiv
    map_bilin := f.map_bilin
    map_mem := fun z =>
      (Lattice.map_mem_map_iff f.toLinearEquiv productLattice z).symm
  }
  let prefixRaw := left.bong.orthogonalProductRight pair.bong hleftPair
  have hprefixLength : 2 + start = n := by omega
  let prefixBONG := prefixRaw.castLength hprefixLength
  let tripleBONG := prefixBONG.mapLatticeIsometry G
  let assembled := tripleBONG.mapLatticeIsometry F
  have hambient : ∀ i : Fin n,
      assembled.ambientVector i = b.ambientVector i := by
    intro i
    let rawIndex : Fin (2 + start) := ⟨i.val, by omega⟩
    have hcast : prefixBONG.ambientVector i =
        prefixRaw.ambientVector rawIndex := by
      rw [BONG.ambientVector_castLength]
    by_cases hleft : i.val < start
    · let j : Fin start := ⟨i.val, hleft⟩
      have hindex : rawIndex = orthogonalProductLeftIndex 2 j := by
        apply Fin.ext
        rfl
      simp only [assembled, tripleBONG,
        BONG.ambientVector_mapLatticeIsometry]
      change f.toLinearEquiv (e (prefixBONG.ambientVector i)) = _
      rw [show e (prefixBONG.ambientVector i) =
        (prefixBONG.ambientVector i, (0 : right.carrier)) by
          simp [e, hdefault]]
      change f.toLinearEquiv (prefixBONG.ambientVector i, 0) = _
      rw [hcast, hindex,
        ambientVector_orthogonalProductRight_left]
      change (left.bong.ambientVector j : V) + 0 + 0 = _
      rw [add_zero, add_zero, left.ambientVector_eq]
      apply congrArg b.ambientVector
      apply Fin.ext
      change 0 + j.val = i.val
      dsimp only [j]
      omega
    · have hstart : start ≤ i.val := Nat.le_of_not_gt hleft
      let j : Fin 2 := ⟨i.val - start, by omega⟩
      have hindex : rawIndex = orthogonalProductRightIndex start j := by
        apply Fin.ext
        change i.val = start + j.val
        dsimp only [j]
        omega
      simp only [assembled, tripleBONG,
        BONG.ambientVector_mapLatticeIsometry]
      change f.toLinearEquiv (e (prefixBONG.ambientVector i)) = _
      rw [show e (prefixBONG.ambientVector i) =
        (prefixBONG.ambientVector i, (0 : right.carrier)) by
          simp [e, hdefault]]
      change f.toLinearEquiv (prefixBONG.ambientVector i, 0) = _
      rw [hcast, hindex,
        ambientVector_orthogonalProductRight_right]
      change 0 + (pair.bong.ambientVector j : V) + 0 = _
      rw [zero_add, add_zero, pair.ambientVector_eq]
      apply congrArg b.ambientVector
      apply Fin.ext
      dsimp only [j]
      omega
  exact assembled.lattice_eq_of_ambientVector_eq b hambient

/-- Beli (2003), Corollary 4.4(ii) when the selected binary pair has a
nonempty suffix, proved without a `BeliCorollary44Laws` instance. -/
theorem beliCorollary44_ii_nonterminal_unconditional
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.val + 1 < n)
    (hsuffix : i.val + 2 < n)
    (horder : b.order ⟨i.val + 1, hi⟩ < b.order i) :
    b.HasThreeBlockSplit i hi := by
  apply b.exists_threeBlockSplit_of_orderBounds_of_nonemptySuffix
    i.val hi hsuffix
  · intro j
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    simp only [SegmentWitness.sourceIndex, Nat.zero_add, Nat.add_zero]
    have h := b.order_le_of_lt_index_of_next_lt hgood i hi horder
      (⟨j.val, by omega⟩ : Fin n) j.isLt
    convert h using 1
    · apply congrArg b.order
      apply Fin.ext
      rfl
  · intro j
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    simp only [SegmentWitness.sourceIndex, Nat.zero_add, Nat.add_zero]
    have hleft := b.order_le_of_lt_index_of_next_lt hgood i hi horder
      (⟨j.val, by omega⟩ : Fin n) j.isLt
    have htwo := hgood i hsuffix
    exact hleft.trans htwo
  · intro j
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    simp only [SegmentWitness.sourceIndex, Nat.add_zero]
    fin_cases j
    · exact hgood i hsuffix
    · have htwo := hgood i hsuffix
      exact horder.le.trans htwo

/-- Beli (2003), Corollary 4.4(ii), including the terminal binary-pair case,
proved without a `BeliCorollary44Laws` instance. -/
theorem beliCorollary44_ii_unconditional
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.val + 1 < n)
    (horder : b.order ⟨i.val + 1, hi⟩ < b.order i) :
    b.HasThreeBlockSplit i hi := by
  by_cases hsuffix : i.val + 2 < n
  · exact b.beliCorollary44_ii_nonterminal_unconditional
      hgood i hi hsuffix horder
  · have hterminal : n = i.val + 2 := by omega
    apply b.exists_threeBlockSplit_of_mappedLattice_eq i.val hi
    apply b.threeBlockMappedLattice_eq_of_terminal_orderBounds
      i.val hi hterminal
    intro j
    rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
    simp only [SegmentWitness.sourceIndex, Nat.zero_add, Nat.add_zero]
    have h := b.order_le_of_lt_index_of_next_lt hgood i hi horder
      (⟨j.val, by omega⟩ : Fin n) j.isLt
    convert h using 1
    apply congrArg b.order
    apply Fin.ext
    rfl

end BONG

end Bong
