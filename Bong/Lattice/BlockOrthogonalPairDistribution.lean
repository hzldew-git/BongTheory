/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41ProductModel

/-!
# Distributing finite block products over orthogonal pairs

The coordinate product of a family of orthogonal pairs is canonically the
orthogonal product of the two coordinate products.  This file records the
canonical linear equivalence together with its quadratic-space and integral
lattice forms.  It also records that a common scalar rescaling commutes with
a finite block orthogonal product.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Reassociate a finite family of pairs into a pair of finite families. -/
def blockProductPairLinearEquiv
    {n : Nat}
    (A : Fin (n + 1) → Type v) (B : Fin (n + 1) → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)] :
    BlockProductSpace n (fun i ↦ A i × B i) ≃ₗ[K]
      BlockProductSpace n A × BlockProductSpace n B where
  toFun x := (fun i ↦ (x i).1, fun i ↦ (x i).2)
  invFun x := fun i ↦ (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem blockProductPairLinearEquiv_apply_fst
    {n : Nat}
    (A : Fin (n + 1) → Type v) (B : Fin (n + 1) → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    (x : BlockProductSpace n (fun i ↦ A i × B i)) (i : Fin (n + 1)) :
    ((blockProductPairLinearEquiv (K := K) A B x).1 i) = (x i).1 :=
  rfl

@[simp]
theorem blockProductPairLinearEquiv_apply_snd
    {n : Nat}
    (A : Fin (n + 1) → Type v) (B : Fin (n + 1) → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    (x : BlockProductSpace n (fun i ↦ A i × B i)) (i : Fin (n + 1)) :
    ((blockProductPairLinearEquiv (K := K) A B x).2 i) = (x i).2 :=
  rfl

/-- A block product of orthogonal pairs is the orthogonal sum of the two
block products. -/
def blockOrthogonalPairIsometry
    {n : Nat}
    (A : Fin (n + 1) → Type v) (B : Fin (n + 1) → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    (p : ∀ i, QuadraticSpace K (A i))
    (q : ∀ i, QuadraticSpace K (B i)) :
    QuadraticSpace.Isometry
      (blockOrthogonalForm n (fun i ↦ A i × B i)
        (fun i ↦ (p i).orthogonalSum (q i)))
      ((blockOrthogonalForm n A p).orthogonalSum
        (blockOrthogonalForm n B q)) where
  toLinearEquiv := blockProductPairLinearEquiv A B
  map_bilin x y := by
    simp only [QuadraticSpace.orthogonalSum_bilin_apply,
      blockOrthogonalForm_bilin_apply,
      blockProductPairLinearEquiv_apply_fst,
      blockProductPairLinearEquiv_apply_snd]
    rw [Finset.sum_add_distrib]

/-- Integral form of `blockOrthogonalPairIsometry`. -/
noncomputable def blockOrthogonalPairLatticeIsometry
    {n : Nat}
    (A : Fin (n + 1) → Type v) (B : Fin (n + 1) → Type w)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    (p : ∀ i, QuadraticSpace K (A i))
    (q : ∀ i, QuadraticSpace K (B i))
    (L : ∀ i, Lattice K (A i)) (M : ∀ i, Lattice K (B i)) :
    Lattice.Isometry
      (blockOrthogonalForm n (fun i ↦ A i × B i)
        (fun i ↦ (p i).orthogonalSum (q i)))
      ((blockOrthogonalForm n A p).orthogonalSum
        (blockOrthogonalForm n B q))
      (blockProductLattice n (fun i ↦ A i × B i)
        (fun i ↦ Lattice.product (L i) (M i)))
      (Lattice.product (blockProductLattice n A L)
        (blockProductLattice n B M)) where
  toLinearEquiv := blockProductPairLinearEquiv A B
  map_bilin := (blockOrthogonalPairIsometry A B p q).map_bilin
  map_mem x := by
    rw [mem_blockProductLattice_iff, Lattice.mem_product_iff,
      mem_blockProductLattice_iff, mem_blockProductLattice_iff]
    constructor
    · intro h
      exact ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩
    · rintro ⟨hL, hM⟩ i
      exact ⟨hL i, hM i⟩

/-- A common unit rescaling commutes with a finite block orthogonal product. -/
def blockOrthogonalRescaleIsometry
    {n : Nat}
    (A : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    (p : ∀ i, QuadraticSpace K (A i)) (s : Kˣ) :
    QuadraticSpace.Isometry
      (blockOrthogonalForm n A (fun i ↦ (p i).rescaleUnit s))
      ((blockOrthogonalForm n A p).rescaleUnit s) where
  toLinearEquiv := LinearEquiv.refl K (BlockProductSpace n A)
  map_bilin x y := by
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      blockOrthogonalForm_bilin_apply, LinearEquiv.refl_apply]
    rw [Finset.mul_sum]

/-- Integral form of `blockOrthogonalRescaleIsometry`; the underlying block
lattice is unchanged by rescaling the form. -/
def blockOrthogonalRescaleLatticeIsometry
    {n : Nat}
    (A : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    (p : ∀ i, QuadraticSpace K (A i))
    (L : ∀ i, Lattice K (A i)) (s : Kˣ) :
    Lattice.Isometry
      (blockOrthogonalForm n A (fun i ↦ (p i).rescaleUnit s))
      ((blockOrthogonalForm n A p).rescaleUnit s)
      (blockProductLattice n A L) (blockProductLattice n A L) where
  toLinearEquiv := LinearEquiv.refl K (BlockProductSpace n A)
  map_bilin := (blockOrthogonalRescaleIsometry A p s).map_bilin
  map_mem _ := Iff.rfl

end BONG

end Bong
