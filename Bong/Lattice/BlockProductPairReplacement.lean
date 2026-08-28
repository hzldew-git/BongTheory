/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BlockProductOrthogonalDecomposition

/-!
# Replacing the first two blocks of a coordinate product

An integral isometry may mix the first two members of a finite orthogonal
family while the remaining blocks are transported componentwise.  This is
the assembly operation needed to turn O'Meara's 93:19 binary exchange into
a new Jordan splitting of the same whole lattice.
-/

namespace Bong

open Dyadic Module

namespace BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The dependent linear equivalence which applies one map to the first two
coordinates and independent maps to all later coordinates. -/
noncomputable def blockProductPairLinearEquiv
    {n : Nat}
    {C : Fin (n + 2) → Type v} {D : Fin (n + 2) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (head : (C 0 × C 1) ≃ₗ[K] (D 0 × D 1))
    (tail : ∀ i : Fin n, C i.succ.succ ≃ₗ[K] D i.succ.succ) :
    BlockProductSpace (n + 1) C ≃ₗ[K] BlockProductSpace (n + 1) D where
  toFun x := fun i ↦
    Fin.cases (head (x 0, x 1)).1
      (fun j ↦ Fin.cases (head (x 0, x 1)).2
        (fun k ↦ tail k (x k.succ.succ)) j) i
  invFun y := fun i ↦
    Fin.cases (head.symm (y 0, y 1)).1
      (fun j ↦ Fin.cases (head.symm (y 0, y 1)).2
        (fun k ↦ (tail k).symm (y k.succ.succ)) j) i
  left_inv x := by
    funext i
    cases i using Fin.cases with
    | zero =>
        change (head.symm (head (x 0, x 1))).1 = x 0
        rw [head.symm_apply_apply]
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            change (head.symm (head (x 0, x 1))).2 = x 1
            rw [head.symm_apply_apply]
        | succ i =>
            change (tail i).symm (tail i (x i.succ.succ)) =
              x i.succ.succ
            rw [(tail i).symm_apply_apply]
  right_inv y := by
    funext i
    cases i using Fin.cases with
    | zero =>
        change (head (head.symm (y 0, y 1))).1 = y 0
        rw [head.apply_symm_apply]
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            change (head (head.symm (y 0, y 1))).2 = y 1
            rw [head.apply_symm_apply]
        | succ i =>
            change tail i ((tail i).symm (y i.succ.succ)) =
              y i.succ.succ
            rw [(tail i).apply_symm_apply]
  map_add' x y := by
    funext i
    cases i using Fin.cases with
    | zero =>
        exact congrArg Prod.fst
          (head.map_add (x 0, x 1) (y 0, y 1))
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            exact congrArg Prod.snd
              (head.map_add (x 0, x 1) (y 0, y 1))
        | succ i => exact (tail i).map_add _ _
  map_smul' c x := by
    funext i
    cases i using Fin.cases with
    | zero =>
        exact congrArg Prod.fst (head.map_smul c (x 0, x 1))
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            exact congrArg Prod.snd (head.map_smul c (x 0, x 1))
        | succ i => exact (tail i).map_smul c (x i.succ.succ)

@[simp]
theorem blockProductPairLinearEquiv_zero
    {n : Nat}
    {C : Fin (n + 2) → Type v} {D : Fin (n + 2) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (head : (C 0 × C 1) ≃ₗ[K] (D 0 × D 1))
    (tail : ∀ i : Fin n, C i.succ.succ ≃ₗ[K] D i.succ.succ)
    (x : BlockProductSpace (n + 1) C) :
    blockProductPairLinearEquiv head tail x 0 = (head (x 0, x 1)).1 :=
  rfl

@[simp]
theorem blockProductPairLinearEquiv_one
    {n : Nat}
    {C : Fin (n + 2) → Type v} {D : Fin (n + 2) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (head : (C 0 × C 1) ≃ₗ[K] (D 0 × D 1))
    (tail : ∀ i : Fin n, C i.succ.succ ≃ₗ[K] D i.succ.succ)
    (x : BlockProductSpace (n + 1) C) :
    blockProductPairLinearEquiv head tail x 1 = (head (x 0, x 1)).2 :=
  rfl

@[simp]
theorem blockProductPairLinearEquiv_succ_succ
    {n : Nat}
    {C : Fin (n + 2) → Type v} {D : Fin (n + 2) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (head : (C 0 × C 1) ≃ₗ[K] (D 0 × D 1))
    (tail : ∀ i : Fin n, C i.succ.succ ≃ₗ[K] D i.succ.succ)
    (x : BlockProductSpace (n + 1) C) (i : Fin n) :
    blockProductPairLinearEquiv head tail x i.succ.succ =
      tail i (x i.succ.succ) :=
  rfl

/-- Replace the first two blocks by an arbitrary integral isometric pair
and transport every later block independently. -/
noncomputable def blockProductPairIsometry
    {n : Nat}
    {C : Fin (n + 2) → Type v} {D : Fin (n + 2) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (rs : ∀ i, QuadraticSpace K (D i))
    (Ls : ∀ i, Lattice K (C i))
    (Ms : ∀ i, Lattice K (D i))
    (head : Lattice.Isometry
      ((qs 0).orthogonalSum (qs 1))
      ((rs 0).orthogonalSum (rs 1))
      (Lattice.product (Ls 0) (Ls 1))
      (Lattice.product (Ms 0) (Ms 1)))
    (tail : ∀ i : Fin n, Lattice.Isometry
      (qs i.succ.succ) (rs i.succ.succ)
      (Ls i.succ.succ) (Ms i.succ.succ)) :
    Lattice.Isometry
      (blockOrthogonalForm (n + 1) C qs)
      (blockOrthogonalForm (n + 1) D rs)
      (blockProductLattice (n + 1) C Ls)
      (blockProductLattice (n + 1) D Ms) where
  toLinearEquiv := blockProductPairLinearEquiv head.toLinearEquiv
    (fun i ↦ (tail i).toLinearEquiv)
  map_bilin x y := by
    rw [blockOrthogonalForm_bilin_apply,
      blockOrthogonalForm_bilin_apply,
      Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hhead := head.map_bilin (x 0, x 1) (y 0, y 1)
    change
      (rs 0).bilin (head.toLinearEquiv (x 0, x 1)).1
          (head.toLinearEquiv (y 0, y 1)).1 +
        (rs 1).bilin (head.toLinearEquiv (x 0, x 1)).2
          (head.toLinearEquiv (y 0, y 1)).2 =
      (qs 0).bilin (x 0) (y 0) + (qs 1).bilin (x 1) (y 1) at hhead
    change
      (rs 0).bilin (head.toLinearEquiv (x 0, x 1)).1
          (head.toLinearEquiv (y 0, y 1)).1 +
        ((rs 1).bilin (head.toLinearEquiv (x 0, x 1)).2
            (head.toLinearEquiv (y 0, y 1)).2 +
          ∑ i : Fin n,
            (rs i.succ.succ).bilin
              ((tail i).toLinearEquiv (x i.succ.succ))
              ((tail i).toLinearEquiv (y i.succ.succ))) = _
    calc
      _ =
          ((rs 0).bilin (head.toLinearEquiv (x 0, x 1)).1
              (head.toLinearEquiv (y 0, y 1)).1 +
            (rs 1).bilin (head.toLinearEquiv (x 0, x 1)).2
              (head.toLinearEquiv (y 0, y 1)).2) +
            ∑ i : Fin n,
              (rs i.succ.succ).bilin
                ((tail i).toLinearEquiv (x i.succ.succ))
                ((tail i).toLinearEquiv (y i.succ.succ)) := by abel
      _ =
          ((qs 0).bilin (x 0) (y 0) + (qs 1).bilin (x 1) (y 1)) +
            ∑ i : Fin n,
              (qs i.succ.succ).bilin (x i.succ.succ) (y i.succ.succ) := by
        rw [hhead]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact (tail i).map_bilin (x i.succ.succ) (y i.succ.succ)
      _ =
          (qs 0).bilin (x 0) (y 0) +
            ((qs 1).bilin (x 1) (y 1) +
              ∑ i : Fin n,
                (qs i.succ.succ).bilin (x i.succ.succ) (y i.succ.succ)) := by
        abel
  map_mem x := by
    rw [mem_blockProductLattice_iff, mem_blockProductLattice_iff]
    constructor
    · intro hx
      have hhead : head.toLinearEquiv (x 0, x 1) ∈
          Lattice.product (Ms 0) (Ms 1) :=
        (head.map_mem (x 0, x 1)).1 ⟨hx 0, hx 1⟩
      intro i
      cases i using Fin.cases with
      | zero =>
          change (head.toLinearEquiv (x 0, x 1)).1 ∈ Ms 0
          exact hhead.1
      | succ i =>
          cases i using Fin.cases with
          | zero =>
              change (head.toLinearEquiv (x 0, x 1)).2 ∈ Ms 1
              exact hhead.2
          | succ i =>
              change (tail i).toLinearEquiv (x i.succ.succ) ∈ Ms i.succ.succ
              exact ((tail i).map_mem (x i.succ.succ)).1 (hx i.succ.succ)
    · intro hx
      have hmappedHead : head.toLinearEquiv (x 0, x 1) ∈
          Lattice.product (Ms 0) (Ms 1) := by
        constructor
        · have hzero := hx 0
          change (head.toLinearEquiv (x 0, x 1)).1 ∈ Ms 0 at hzero
          exact hzero
        · have hone := hx 1
          change (head.toLinearEquiv (x 0, x 1)).2 ∈ Ms 1 at hone
          exact hone
      have hhead : (x 0, x 1) ∈ Lattice.product (Ls 0) (Ls 1) :=
        (head.map_mem (x 0, x 1)).2 hmappedHead
      intro i
      cases i using Fin.cases with
      | zero => exact hhead.1
      | succ i =>
          cases i using Fin.cases with
          | zero => exact hhead.2
          | succ i =>
              have hi := hx i.succ.succ
              change (tail i).toLinearEquiv (x i.succ.succ) ∈
                Ms i.succ.succ at hi
              exact ((tail i).map_mem (x i.succ.succ)).2 hi

end BONG

end Bong
