/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44
import Bong.Bong.Beli2019Lemma710BONGProduct

/-!
# The splitting construction in Beli (2003), Corollary 4.4

This file begins the unconditional proof of Corollary 4.4.  The main
construction below glues two consecutive segment BONGs whenever every order
in the left segment is bounded by the head order of the right segment.  The
resulting product BONG has exactly the original ambient vectors, so Beli's
already proved reconstruction theorem identifies its lattice with the
original lattice.
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

/-- Casting only the length index does not change BONG orders. -/
@[simp]
theorem order_castLength_index {m r : Nat} (b : BONG V q L m)
    (h : m = r) (i : Fin r) :
    (b.castLength h).order i =
      b.order ⟨i.val, by simpa [h] using i.isLt⟩ := by
  subst r
  rfl

/-- The coordinate spaces on the two sides of a cut are orthogonal. -/
theorem segmentCarriers_orthogonal
    (b : BONG V q L n) (cut : Nat) (hcut : cut ≤ n)
    (x : (b.segmentWitness 0 cut (by omega)).carrier)
    (y : (b.segmentWitness cut (n - cut) (by omega)).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  let left := b.segmentWitness 0 cut (by omega)
  let right := b.segmentWitness cut (n - cut) (by omega)
  have hx : x ∈ Submodule.span K (Set.range left.bong.ambientVector) := by
    rw [left.bong.span_ambientVector_eq_top]
    trivial
  refine Submodule.span_induction
    (p := fun (z : left.carrier) _ => q.bilin (z : V) (y : V) = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    have hy : y ∈ Submodule.span K (Set.range right.bong.ambientVector) := by
      rw [right.bong.span_ambientVector_eq_top]
      trivial
    refine Submodule.span_induction
      (p := fun (z : right.carrier) _ =>
        q.bilin (left.bong.ambientVector i : V) (z : V) = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      rw [left.ambientVector_eq, right.ambientVector_eq]
      apply (LinearMap.BilinForm.iIsOrtho_def.mp
        b.ambientVector_iIsOrtho)
      intro hij
      have hval := congrArg Fin.val hij
      simp only [SegmentWitness.sourceIndex_val] at hval
      omega
    · simp
    · intro z w _ _ hz hw
      simpa only [Submodule.coe_add, LinearMap.BilinForm.add_right,
        hz, hw, add_zero]
    · intro a z _ hz
      simp only [Submodule.coe_smul, LinearMap.BilinForm.smul_right, hz]
      simp
  · simp
  · intro z w _ _ hz hw
    simpa only [Submodule.coe_add, LinearMap.BilinForm.add_left,
      hz, hw, add_zero]
  · intro a z _ hz
    simp only [Submodule.coe_smul, LinearMap.BilinForm.smul_left, hz]
    simp

/-- Two disjoint consecutive coordinate segments, with the first ending no
later than the second starts, have orthogonal carriers. -/
theorem segmentCarriers_orthogonal_of_end_le_start
    (b : BONG V q L n)
    (firstStart firstLength secondStart secondLength : Nat)
    (hfirst : firstStart + firstLength ≤ n)
    (hsecond : secondStart + secondLength ≤ n)
    (hbefore : firstStart + firstLength ≤ secondStart)
    (x : (b.segmentWitness firstStart firstLength hfirst).carrier)
    (y : (b.segmentWitness secondStart secondLength hsecond).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  let first := b.segmentWitness firstStart firstLength hfirst
  let second := b.segmentWitness secondStart secondLength hsecond
  have hx : x ∈ Submodule.span K (Set.range first.bong.ambientVector) := by
    rw [first.bong.span_ambientVector_eq_top]
    trivial
  refine Submodule.span_induction
    (p := fun (z : first.carrier) _ => q.bilin (z : V) (y : V) = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    have hy : y ∈ Submodule.span K (Set.range second.bong.ambientVector) := by
      rw [second.bong.span_ambientVector_eq_top]
      trivial
    refine Submodule.span_induction
      (p := fun (z : second.carrier) _ =>
        q.bilin (first.bong.ambientVector i : V) (z : V) = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      rw [first.ambientVector_eq, second.ambientVector_eq]
      apply (LinearMap.BilinForm.iIsOrtho_def.mp
        b.ambientVector_iIsOrtho)
      intro hij
      have hval := congrArg Fin.val hij
      change firstStart + i.val = secondStart + j.val at hval
      omega
    · simp
    · intro z w _ _ hz hw
      simpa only [Submodule.coe_add, LinearMap.BilinForm.add_right,
        hz, hw, add_zero]
    · intro a z _ hz
      simp only [Submodule.coe_smul, LinearMap.BilinForm.smul_right, hz]
      simp
  · simp
  · intro z w _ _ hz hw
    simpa only [Submodule.coe_add, LinearMap.BilinForm.add_left,
      hz, hw, add_zero]
  · intro a z _ hz
    simp only [Submodule.coe_smul, LinearMap.BilinForm.smul_left, hz]
    simp

/-- The coordinate spaces on the two sides of a cut are complementary. -/
theorem segmentCarriers_isCompl
    (b : BONG V q L n) (cut : Nat) (hcut : cut ≤ n) :
    IsCompl (b.segmentWitness 0 cut (by omega)).carrier
      (b.segmentWitness cut (n - cut) (by omega)).carrier := by
  let left := b.segmentWitness 0 cut (by omega)
  let right := b.segmentWitness cut (n - cut) (by omega)
  letI : FiniteDimensional K V := b.basis.finiteDimensional_of_finite
  apply (Submodule.isCompl_iff_disjoint left.carrier right.carrier ?_).2
  · rw [disjoint_iff_inf_le]
    intro z hz
    let zx : left.carrier := ⟨z, hz.1⟩
    let zy : right.carrier := ⟨z, hz.2⟩
    have hzero : zx = 0 := by
      apply left.nondegenerate.1 zx
      intro w
      change q.bilin (z : V) (w : V) = 0
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal cut hcut w zy
    change z = 0
    exact congrArg Subtype.val hzero
  · rw [left.carrier_eq_segmentCarrier, right.carrier_eq_segmentCarrier,
      b.finrank_segmentCarrier, b.finrank_segmentCarrier,
      ← b.length_eq_finrank]
    omega

/-- The concrete sum map from the two coordinate spaces to the ambient
quadratic space. -/
noncomputable def segmentProductLinearEquiv
    (b : BONG V q L n) (cut : Nat) (hcut : cut ≤ n) :
    ((b.segmentWitness 0 cut (by omega)).carrier ×
      (b.segmentWitness cut (n - cut) (by omega)).carrier) ≃ₗ[K] V :=
  (b.segmentWitness 0 cut (by omega)).carrier.prodEquivOfIsCompl
    (b.segmentWitness cut (n - cut) (by omega)).carrier
    (b.segmentCarriers_isCompl cut hcut)

@[simp]
theorem segmentProductLinearEquiv_apply
    (b : BONG V q L n) (cut : Nat) (hcut : cut ≤ n)
    (z : (b.segmentWitness 0 cut (by omega)).carrier ×
      (b.segmentWitness cut (n - cut) (by omega)).carrier) :
    b.segmentProductLinearEquiv cut hcut z = (z.1 : V) + (z.2 : V) :=
  rfl

/-- The sum map is an isometry from the orthogonal product of the two
coordinate spaces. -/
noncomputable def segmentProductIsometry
    (b : BONG V q L n) (cut : Nat) (hcut : cut ≤ n) :
    ((q.restrict (b.segmentWitness 0 cut (by omega)).carrier
        (b.segmentWitness 0 cut (by omega)).nondegenerate).orthogonalSum
      (q.restrict (b.segmentWitness cut (n - cut) (by omega)).carrier
        (b.segmentWitness cut (n - cut) (by omega)).nondegenerate)).Isometry q where
  toLinearEquiv := b.segmentProductLinearEquiv cut hcut
  map_bilin := by
    intro x y
    change q.bilin ((x.1 : V) + (x.2 : V))
        ((y.1 : V) + (y.2 : V)) =
      q.bilin (x.1 : V) (y.1 : V) +
        q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    rw [b.segmentCarriers_orthogonal cut hcut x.1 y.2]
    have hcross : q.bilin (x.2 : V) (y.1 : V) = 0 := by
      rw [q.isSymm.eq]
      exact b.segmentCarriers_orthogonal cut hcut y.1 x.2
    rw [hcross]
    simp

/-- The concrete two-segment reconstruction.  Exposing the witness, rather
than only its nonemptiness, lets later local calculations use the canonical
segment lattices definitionally. -/
noncomputable def twoBlockSplitOfLeftOrdersLeRightHead
    (b : BONG V q L n) (cut : Nat) (hcutPos : 0 < cut)
    (hcutLt : cut < n)
    (horders : ∀ i : Fin cut,
      (b.segmentWitness 0 cut (by omega)).bong.order i ≤
        (b.segmentWitness cut (n - cut) (by omega)).bong.order
          ⟨0, by omega⟩) :
    TwoBlockSplitWitness b cut hcutLt.le := by
  let left := b.segmentWitness 0 cut (by omega)
  let right := b.segmentWitness cut (n - cut) (by omega)
  let f := b.segmentProductIsometry cut hcutLt.le
  let productLattice := Lattice.product left.lattice right.lattice
  let mappedLattice := Lattice.map f.toLinearEquiv productLattice
  let F : Lattice.Isometry
      ((q.restrict left.carrier left.nondegenerate).orthogonalSum
        (q.restrict right.carrier right.nondegenerate)) q
      productLattice mappedLattice := {
    toLinearEquiv := f.toLinearEquiv
    map_bilin := f.map_bilin
    map_mem := fun z =>
      (Lattice.map_mem_map_iff f.toLinearEquiv productLattice z).symm
  }
  have hrightPos : 0 < n - cut := by omega
  let m := n - cut - 1
  have hrightLength : n - cut = m + 1 := by
    dsimp only [m]
    omega
  let rightBONG : BONG right.carrier
      (q.restrict right.carrier right.nondegenerate) right.lattice (m + 1) :=
    right.bong.castLength hrightLength
  have hproductOrders : ∀ i : Fin cut,
      left.bong.order i ≤ rightBONG.order 0 := by
    intro i
    rw [BONG.order_castLength_index]
    convert horders i using 1
    apply congrArg right.bong.order
    apply Fin.ext
    rfl
  let productBONG := left.bong.orthogonalProductRight rightBONG hproductOrders
  have hproductLength : (m + 1) + cut = n := by
    dsimp only [m]
    omega
  let productBONG' := productBONG.castLength hproductLength
  let assembled := productBONG'.mapLatticeIsometry F
  have hambient : ∀ i : Fin n,
      assembled.ambientVector i = b.ambientVector i := by
    intro i
    by_cases hi : i.val < cut
    · let j : Fin cut := ⟨i.val, hi⟩
      have hindex : i = Fin.cast hproductLength
          (orthogonalProductLeftIndex (m + 1) j) := by
        apply Fin.ext
        rfl
      rw [hindex]
      simp only [assembled, BONG.ambientVector_mapLatticeIsometry,
        productBONG', BONG.ambientVector_castLength]
      have hleft := ambientVector_orthogonalProductRight_left
        left.bong rightBONG hproductOrders j
      change f.toLinearEquiv
          (productBONG.ambientVector
            (orthogonalProductLeftIndex (m + 1) j)) = _
      rw [hleft]
      change (left.bong.ambientVector j : V) + 0 = _
      rw [add_zero, left.ambientVector_eq]
      apply congrArg b.ambientVector
      apply Fin.ext
      simp
    · have hiRight : cut ≤ i.val := Nat.le_of_not_gt hi
      let j : Fin (m + 1) := ⟨i.val - cut, by
        dsimp only [m]
        omega⟩
      have hindex : i = Fin.cast hproductLength
          (orthogonalProductRightIndex cut j) := by
        apply Fin.ext
        change i.val = cut + j.val
        dsimp only [j]
        omega
      rw [hindex]
      simp only [assembled, BONG.ambientVector_mapLatticeIsometry,
        productBONG', BONG.ambientVector_castLength]
      have hright := ambientVector_orthogonalProductRight_right
        left.bong rightBONG hproductOrders j
      change f.toLinearEquiv
          (productBONG.ambientVector
            (orthogonalProductRightIndex cut j)) = _
      rw [hright]
      change 0 + (rightBONG.ambientVector j : V) = _
      rw [zero_add]
      have hcast := BONG.ambientVector_castLength right.bong
        hrightLength j
      change (rightBONG.ambientVector j : V) = _
      rw [hcast, right.ambientVector_eq]
      congr 1
  have hmapped : mappedLattice = L :=
    assembled.lattice_eq_of_ambientVector_eq b hambient
  let leftComponent := left.toQuadraticSublattice
  let rightComponent := right.toQuadraticSublattice
  let component : Fin 2 → Lattice.QuadraticSublattice q :=
    fun i => Fin.cases leftComponent (fun _ => rightComponent) i
  have hsum : (⨆ i, (component i).ambientSubmodule) =
      mappedLattice.toSubmodule := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · change leftComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        have hpair : (x, 0) ∈ productLattice :=
          Lattice.mem_product_iff.mpr ⟨hx, right.lattice.zero_mem⟩
        have hmap := (Lattice.map_mem_map_iff
          f.toLinearEquiv productLattice (x, 0)).2 hpair
        change f.toLinearEquiv (x, 0) ∈ mappedLattice at hmap
        change (x : V) + 0 ∈ mappedLattice at hmap
        simpa using hmap
      · change rightComponent.ambientSubmodule ≤ mappedLattice.toSubmodule
        intro z hz
        rcases hz with ⟨y, hy, rfl⟩
        have hpair : (0, y) ∈ productLattice :=
          Lattice.mem_product_iff.mpr ⟨left.lattice.zero_mem, hy⟩
        have hmap := (Lattice.map_mem_map_iff
          f.toLinearEquiv productLattice (0, y)).2 hpair
        change f.toLinearEquiv (0, y) ∈ mappedLattice at hmap
        change 0 + (y : V) ∈ mappedLattice at hmap
        simpa using hmap
    · intro z hz
      have hzProduct : f.toLinearEquiv.symm z ∈ productLattice := by
        exact (Lattice.mem_map_iff f.toLinearEquiv productLattice z).1 hz
      have hzParts := Lattice.mem_product_iff.mp hzProduct
      let x := (f.toLinearEquiv.symm z).1
      let y := (f.toLinearEquiv.symm z).2
      have hzEq : (x : V) + (y : V) = z := by
        change f.toLinearEquiv (f.toLinearEquiv.symm z) = z
        exact f.toLinearEquiv.apply_symm_apply z
      have hxAmbient : (x : V) ∈ leftComponent.ambientSubmodule :=
        ⟨x, hzParts.1, rfl⟩
      have hyAmbient : (y : V) ∈ rightComponent.ambientSubmodule :=
        ⟨y, hzParts.2, rfl⟩
      rw [← hzEq]
      apply Submodule.add_mem
      · exact le_iSup (fun i => (component i).ambientSubmodule) 0 hxAmbient
      · exact le_iSup (fun i => (component i).ambientSubmodule) 1 hyAmbient
  let decomposition : Lattice.OrthogonalDecomposition q L 2 := {
    component := component
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact b.segmentCarriers_orthogonal cut hcutLt.le x y
      · rw [q.isSymm.eq]
        exact b.segmentCarriers_orthogonal cut hcutLt.le y x
      · exact (hij rfl).elim
    sum_eq := by simpa only [hmapped] using hsum
  }
  exact {
    left := left
    right := right
    decomposition := decomposition
    component_zero := rfl
    component_one := rfl
  }

/-- A general two-segment reconstruction theorem.  This is the integral
content used in Corollary 4.4(i): the order bound makes the left-first
orthogonal product a BONG, and equality of all its vectors recovers `L`. -/
theorem exists_twoBlockSplit_of_leftOrders_le_rightHead
    (b : BONG V q L n) (cut : Nat) (hcutPos : 0 < cut)
    (hcutLt : cut < n)
    (horders : ∀ i : Fin cut,
      (b.segmentWitness 0 cut (by omega)).bong.order i ≤
        (b.segmentWitness cut (n - cut) (by omega)).bong.order
          ⟨0, by omega⟩) :
    b.HasTwoBlockSplit cut hcutLt.le :=
  ⟨b.twoBlockSplitOfLeftOrdersLeRightHead cut hcutPos hcutLt horders⟩

/-- Beli (2003), Corollary 4.4(i), proved without a
`BeliCorollary44Laws` instance.  Goodness propagates the adjacent boundary
inequality backwards along the two parity chains; the preceding reconstruction
theorem then gives the actual orthogonal lattice split. -/
theorem beliCorollary44_i_unconditional
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hi : i.1 + 1 < n)
    (horder : b.order i ≤ b.order ⟨i.1 + 1, hi⟩) :
    b.HasTwoBlockSplit (i.1 + 1) (by omega) := by
  let cut := i.val + 1
  have hcutPos : 0 < cut := by
    dsimp only [cut]
    omega
  have hcutLt : cut < n := by
    dsimp only [cut]
    omega
  apply b.exists_twoBlockSplit_of_leftOrders_le_rightHead
    cut hcutPos hcutLt
  intro j
  rw [SegmentWitness.order_eq, SegmentWitness.order_eq]
  simp only [SegmentWitness.sourceIndex, Nat.zero_add, Nat.add_zero]
  by_cases hcutOne : cut = 1
  · convert horder using 1 <;>
      apply congrArg b.order <;>
      apply Fin.ext <;>
      dsimp only [cut] at hcutOne ⊢ <;>
      omega
  · have hcutTwo : 2 ≤ cut := by omega
    let g : GoodBONG q L n := ⟨b, hgood⟩
    have hpenultimate :
        g.order ⟨cut - 2, by omega⟩ ≤ b.order ⟨cut, by omega⟩ := by
      change b.order ⟨cut - 2, by omega⟩ ≤ b.order ⟨cut, by omega⟩
      let pen : Fin n := ⟨cut - 2, by omega⟩
      have hpenStep : pen.val + 2 < n := by
        dsimp only [pen]
        omega
      have h := hgood pen hpenStep
      have hindex :
          (⟨pen.val + 2, hpenStep⟩ : Fin n) = ⟨cut, hcutLt⟩ := by
        apply Fin.ext
        dsimp only [pen]
        omega
      rw [hindex] at h
      simpa only [pen] using h
    have hlast :
        g.order ⟨cut - 1, by omega⟩ ≤ b.order ⟨cut, by omega⟩ := by
      change b.order ⟨cut - 1, by omega⟩ ≤ b.order ⟨cut, by omega⟩
      convert horder using 1 <;>
        apply congrArg b.order <;>
        apply Fin.ext <;>
        dsimp only [cut] <;>
        omega
    have h := g.order_le_of_lt_cut_of_last_two_le cut hcutTwo hcutLt.le
      (b.order ⟨cut, by omega⟩) hpenultimate hlast
      (⟨j.val, by omega⟩ : Fin n) (by exact j.isLt)
    exact h

end BONG

end Bong
