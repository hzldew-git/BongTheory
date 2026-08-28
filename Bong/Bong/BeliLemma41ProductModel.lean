/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41OrderBounds
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.BasisUnits
import Bong.Lattice.BasisIsometry
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite ordered products of BONG blocks

This file constructs the finite orthogonal product used in Beli (2003),
Lemma 4.1.  A nonempty family of component spaces is represented by its
dependent function space.  The explicit head--tail equivalence below lets us
reuse the binary orthogonal-product constructor without introducing custom
recursive type-class instances.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace QuadraticSpace

variable {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Pull a quadratic space back along a linear equivalence. -/
def pullbackLinearEquiv (q : QuadraticSpace K W) (e : V ≃ₗ[K] W) :
    QuadraticSpace K V where
  bilin := LinearMap.mk₂ K (fun x y => q.bilin (e x) (e y))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
  isSymm := ⟨by
    intro x y
    exact q.isSymm.eq (e x) (e y)⟩
  nondegenerate := by
    constructor
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply q.nondegenerate.1
      intro y
      simpa using hx (e.symm y)
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply q.nondegenerate.2
      intro y
      simpa using hx (e.symm y)

@[simp]
theorem pullbackLinearEquiv_bilin_apply
    (q : QuadraticSpace K W) (e : V ≃ₗ[K] W) (x y : V) :
    (q.pullbackLinearEquiv e).bilin x y = q.bilin (e x) (e y) :=
  rfl

/-- The defining equivalence is an isometry from the pullback form. -/
def pullbackLinearEquivIsometry
    (q : QuadraticSpace K W) (e : V ≃ₗ[K] W) :
    Isometry (q.pullbackLinearEquiv e) q where
  toLinearEquiv := e
  map_bilin _ _ := rfl

end QuadraticSpace

namespace BONG

/-- The product of a nonempty dependent family of component spaces. -/
abbrev BlockProductSpace (n : Nat) (C : Fin (n + 1) → Type v) :=
  ∀ i, C i

/-- Total length of a nonempty family of finite BONG blocks. -/
def blockTotalRank (n : Nat) (ranks : Fin (n + 1) → Nat) : Nat :=
  ∑ i, ranks i

@[simp]
theorem blockTotalRank_zero (ranks : Fin 1 → Nat) :
    blockTotalRank 0 ranks = ranks 0 := by
  simp [blockTotalRank]

theorem blockTotalRank_succ (n : Nat) (ranks : Fin (n + 2) → Nat) :
    blockTotalRank (n + 1) ranks =
      ranks 0 + blockTotalRank n (fun i => ranks i.succ) := by
  exact Fin.sum_univ_succ ranks

/-- Split dependent block indices into the zeroth block and all successor
blocks. -/
def blockIndexConsEquiv (n : Nat) (ranks : Fin (n + 2) → Nat) :
    Fin (ranks 0) ⊕ (Σ i : Fin (n + 1), Fin (ranks i.succ)) ≃
      Σ i : Fin (n + 2), Fin (ranks i) where
  toFun
    | Sum.inl j => ⟨0, j⟩
    | Sum.inr ⟨i, j⟩ => ⟨i.succ, j⟩
  invFun a := Fin.cases
    (motive := fun i => Fin (ranks i) →
      Fin (ranks 0) ⊕ (Σ j : Fin (n + 1), Fin (ranks j.succ)))
    (fun j => Sum.inl j)
    (fun i j => Sum.inr ⟨i, j⟩) a.1 a.2
  left_inv x := by
    rcases x with j | ⟨i, j⟩
    · rfl
    · rfl
  right_inv a := by
    rcases a with ⟨i, j⟩
    revert j
    refine Fin.cases ?_ (fun k => ?_) i
    · intro j
      rfl
    · intro j
      rfl

@[simp]
theorem blockIndexConsEquiv_inl
    (n : Nat) (ranks : Fin (n + 2) → Nat) (j : Fin (ranks 0)) :
    blockIndexConsEquiv n ranks (Sum.inl j) = ⟨0, j⟩ :=
  rfl

@[simp]
theorem blockIndexConsEquiv_inr
    (n : Nat) (ranks : Fin (n + 2) → Nat)
    (a : Σ i : Fin (n + 1), Fin (ranks i.succ)) :
    blockIndexConsEquiv n ranks (Sum.inr a) = ⟨a.1.succ, a.2⟩ := by
  rcases a with ⟨i, j⟩
  rfl

/-- Block-index equivalence for a single block. -/
noncomputable def blockIndexEquivSingleton (ranks : Fin 1 → Nat) :
    Fin (blockTotalRank 0 ranks) ≃ Σ i, Fin (ranks i) :=
  (finCongr (blockTotalRank_zero ranks)).trans
    (Equiv.uniqueSigma (fun i : Fin 1 => Fin (ranks i))).symm

/-- Assemble the index equivalence of a head block and a recursively
concatenated tail. -/
def blockIndexEquivCons (n : Nat) (ranks : Fin (n + 2) → Nat)
    (tail : Fin (blockTotalRank n (fun i => ranks i.succ)) ≃
      Σ i : Fin (n + 1), Fin (ranks i.succ)) :
    Fin (blockTotalRank (n + 1) ranks) ≃ Σ i, Fin (ranks i) :=
  (finCongr (blockTotalRank_succ n ranks)).trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (Equiv.refl (Fin (ranks 0))) tail).trans
        (blockIndexConsEquiv n ranks)))

/-- Position of a local head-block index in the concatenated index set. -/
def blockLeftIndex (n : Nat) (ranks : Fin (n + 2) → Nat)
    (i : Fin (ranks 0)) : Fin (blockTotalRank (n + 1) ranks) :=
  ⟨i.val, by rw [blockTotalRank_succ]; omega⟩

/-- Position of a recursively concatenated tail index after the head block. -/
def blockRightIndex (n : Nat) (ranks : Fin (n + 2) → Nat)
    (i : Fin (blockTotalRank n (fun j => ranks j.succ))) :
    Fin (blockTotalRank (n + 1) ranks) :=
  ⟨ranks 0 + i.val, by rw [blockTotalRank_succ]; omega⟩

@[simp]
theorem blockLeftIndex_val (n : Nat) (ranks : Fin (n + 2) → Nat)
    (i : Fin (ranks 0)) :
    (blockLeftIndex n ranks i).val = i.val :=
  rfl

@[simp]
theorem blockRightIndex_val (n : Nat) (ranks : Fin (n + 2) → Nat)
    (i : Fin (blockTotalRank n (fun j => ranks j.succ))) :
    (blockRightIndex n ranks i).val = ranks 0 + i.val :=
  rfl

@[simp]
theorem blockIndexEquivCons_left
    (n : Nat) (ranks : Fin (n + 2) → Nat)
    (tail : Fin (blockTotalRank n (fun i => ranks i.succ)) ≃
      Σ i : Fin (n + 1), Fin (ranks i.succ))
    (i : Fin (ranks 0)) :
    blockIndexEquivCons n ranks tail (blockLeftIndex n ranks i) =
      ⟨0, i⟩ := by
  unfold blockIndexEquivCons
  simp only [Equiv.trans_apply]
  have hcast :
      finCongr (blockTotalRank_succ n ranks) (blockLeftIndex n ranks i) =
        Fin.castAdd (blockTotalRank n (fun j => ranks j.succ)) i := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp]
theorem blockIndexEquivCons_right
    (n : Nat) (ranks : Fin (n + 2) → Nat)
    (tail : Fin (blockTotalRank n (fun i => ranks i.succ)) ≃
      Σ i : Fin (n + 1), Fin (ranks i.succ))
    (i : Fin (blockTotalRank n (fun j => ranks j.succ))) :
    blockIndexEquivCons n ranks tail (blockRightIndex n ranks i) =
      ⟨(tail i).1.succ, (tail i).2⟩ := by
  unfold blockIndexEquivCons
  simp only [Equiv.trans_apply]
  have hcast :
      finCongr (blockTotalRank_succ n ranks) (blockRightIndex n ranks i) =
        Fin.natAdd (ranks 0) i := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Lexicographic order on the dependent indices of a family of blocks. -/
def BlockIndexBefore {n : Nat} {ranks : Fin (n + 1) → Nat}
    (a b : Σ i, Fin (ranks i)) : Prop :=
  a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)

/-- A one-block product is canonically its only component. -/
def blockProductSingleton
    (C : Fin 1 → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] :
    BlockProductSpace 0 C ≃ₗ[K] C 0 where
  toFun x := x 0
  invFun x := fun i => Fin.cases x (fun j => Fin.elim0 j) i
  left_inv x := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Split a nonempty product with at least two blocks into its head and tail. -/
def blockProductSplit
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] :
    BlockProductSpace (n + 1) C ≃ₗ[K]
      C 0 × BlockProductSpace n (fun i => C i.succ) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv x := by
    ext <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse head--tail split embeds a head vector as the zeroth
coordinate. -/
theorem blockProductSplit_symm_inl
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)] (x : C 0) :
    (blockProductSplit (K := K) n C).symm (x, 0) = Pi.single 0 x := by
  classical
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [blockProductSplit]
  · simp [blockProductSplit, Pi.single_eq_of_ne]

/-- The inverse head--tail split embeds a tail coordinate at its successor
position. -/
theorem blockProductSplit_symm_inr_single
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (a : Fin (n + 1)) (x : C a.succ) :
    (blockProductSplit (K := K) n C).symm (0, Pi.single a x) =
      Pi.single a.succ x := by
  classical
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [blockProductSplit, Pi.single_eq_of_ne]
  · by_cases h : j = a
    · subst j
      simp [blockProductSplit]
    · simp [blockProductSplit, Pi.single_eq_of_ne, h]

/-- Orthogonal direct-sum form on a finite dependent product. -/
def blockOrthogonalForm
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i)) :
    QuadraticSpace K (BlockProductSpace n C) where
  bilin := LinearMap.mk₂ K
    (fun x y => ∑ i, (qs i).bilin (x i) (y i))
    (by intros; simp [Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum])
    (by intros; simp [Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum])
  isSymm := ⟨by
    intro x y
    change (∑ i, (qs i).bilin (x i) (y i)) =
      ∑ i, (qs i).bilin (y i) (x i)
    apply Finset.sum_congr rfl
    intro i _
    exact (qs i).isSymm.eq (x i) (y i)⟩
  nondegenerate := by
    classical
    constructor
    · intro x hx
      funext i
      apply (qs i).nondegenerate.1
      intro z
      have h := hx (Pi.single i z)
      change (∑ j, (qs j).bilin (x j) ((Pi.single i z) j)) = 0 at h
      rw [Fintype.sum_eq_single i] at h
      · simpa using h
      · intro j hji
        rw [Pi.single_eq_of_ne hji]
        simp
    · intro x hx
      funext i
      apply (qs i).nondegenerate.2
      intro z
      have h := hx (Pi.single i z)
      change (∑ j, (qs j).bilin ((Pi.single i z) j) (x j)) = 0 at h
      rw [Fintype.sum_eq_single i] at h
      · simpa using h
      · intro j hji
        rw [Pi.single_eq_of_ne hji]
        simp

@[simp]
theorem blockOrthogonalForm_bilin_apply
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (x y : BlockProductSpace n C) :
    (blockOrthogonalForm n C qs).bilin x y =
      ∑ i, (qs i).bilin (x i) (y i) :=
  rfl

/-- The one-block product form is isometric to its only component. -/
def blockOrthogonalSingletonIsometry
    (C : Fin 1 → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i)) :
    QuadraticSpace.Isometry (blockOrthogonalForm 0 C qs) (qs 0) where
  toLinearEquiv := blockProductSingleton C
  map_bilin x y := by
    rw [blockOrthogonalForm_bilin_apply]
    simp [blockProductSingleton]

/-- The head--tail splitting is an orthogonal-space isometry. -/
def blockOrthogonalSplitIsometry
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i)) :
    QuadraticSpace.Isometry (blockOrthogonalForm (n + 1) C qs)
      ((qs 0).orthogonalSum
        (blockOrthogonalForm n (fun i => C i.succ) (fun i => qs i.succ))) where
  toLinearEquiv := blockProductSplit n C
  map_bilin x y := by
    change (qs 0).bilin (x 0) (y 0) +
        (∑ i : Fin (n + 1), (qs i.succ).bilin (x i.succ) (y i.succ)) =
      ∑ i : Fin (n + 2), (qs i).bilin (x i) (y i)
    exact (Fin.sum_univ_succ
      (fun i : Fin (n + 2) => (qs i).bilin (x i) (y i))).symm

/-- Concatenation of chosen component lattice bases in the product space. -/
noncomputable def blockProductBasis
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (Ls : ∀ i, Lattice K (C i)) :
    Basis (Σ i, (Ls i).BasisIndex) K (BlockProductSpace n C) :=
  Pi.basis (fun i => (Ls i).ambientBasis)

/-- Coordinatewise product of a finite nonempty family of full lattices. -/
noncomputable def blockProductLattice
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (Ls : ∀ i, Lattice K (C i)) :
    Lattice K (BlockProductSpace n C) :=
  Lattice.basisLattice (blockProductBasis n C Ls)

/-- A lattice is recovered from the chosen ambient extension of its
integral basis. -/
theorem basisLattice_ambientBasis_eq
    {W : Type v} [AddCommGroup W] [Module K W] (L : Lattice K W) :
    Lattice.basisLattice L.ambientBasis = L := by
  apply Lattice.ext
  exact L.toSubmodule_eq_span_ambientBasis.symm

/-- Membership in the product lattice is coordinatewise membership. -/
theorem mem_blockProductLattice_iff
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (Ls : ∀ i, Lattice K (C i)) (x : BlockProductSpace n C) :
    x ∈ blockProductLattice n C Ls ↔ ∀ i, x i ∈ Ls i := by
  rw [blockProductLattice,
    Lattice.mem_basisLattice_iff_repr_mem_integerRing]
  simp only [blockProductBasis, Pi.basis_repr]
  constructor
  · intro h i
    rw [← basisLattice_ambientBasis_eq (Ls i),
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    intro j
    exact h ⟨i, j⟩
  · intro h a
    exact (Lattice.mem_basisLattice_iff_repr_mem_integerRing
      (Ls a.1).ambientBasis (x a.1)).1
        (by simpa only [basisLattice_ambientBasis_eq] using h a.1) a.2

/-- A BONG of the coordinate product whose vectors occur block by block. -/
structure BlockBONGWitness
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (ranks : Fin (n + 1) → Nat)
    (c : ∀ i, BONG (C i) (qs i) (Ls i) (ranks i)) where
  /-- The concatenated product BONG. -/
  bong : BONG (BlockProductSpace n C)
    (blockOrthogonalForm n C qs) (blockProductLattice n C Ls)
    (blockTotalRank n ranks)
  /-- Global indices are dependent block indices. -/
  indexEquiv : Fin (blockTotalRank n ranks) ≃ Σ i, Fin (ranks i)
  /-- Global order is exactly lexicographic block order. -/
  order_iff : ∀ i j,
    i < j ↔ BlockIndexBefore (indexEquiv i) (indexEquiv j)
  /-- Every global vector is the corresponding one-coordinate block vector. -/
  ambientVector_eq : ∀ i,
    bong.ambientVector i =
      Pi.single (indexEquiv i).1
        ((c (indexEquiv i).1).ambientVector (indexEquiv i).2)

namespace BlockBONGWitness

variable {n : Nat} {C : Fin (n + 1) → Type v}
  [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
  {qs : ∀ i, QuadraticSpace K (C i)}
  {Ls : ∀ i, Lattice K (C i)}
  {ranks : Fin (n + 1) → Nat}
  {c : ∀ i, BONG (C i) (qs i) (Ls i) (ranks i)}

/-- The concatenated value is the corresponding component value. -/
theorem value_eq (w : BlockBONGWitness n C qs Ls ranks c)
    (i : Fin (blockTotalRank n ranks)) :
    w.bong.value i =
      (c (w.indexEquiv i).1).value (w.indexEquiv i).2 := by
  classical
  rw [← w.bong.quadratic_ambientVector i,
    ← (c (w.indexEquiv i).1).quadratic_ambientVector
      (w.indexEquiv i).2, w.ambientVector_eq]
  change (∑ j, (qs j).bilin
      ((Pi.single (w.indexEquiv i).1
        ((c (w.indexEquiv i).1).ambientVector (w.indexEquiv i).2)) j)
      ((Pi.single (w.indexEquiv i).1
        ((c (w.indexEquiv i).1).ambientVector (w.indexEquiv i).2)) j)) = _
  rw [Fintype.sum_eq_single (w.indexEquiv i).1]
  · simp only [Pi.single_eq_same, QuadraticSpace.quadratic]
  · intro j hji
    rw [Pi.single_eq_of_ne hji]
    simp

/-- The concatenated order is the corresponding component order. -/
theorem order_eq (w : BlockBONGWitness n C qs Ls ranks c)
    (i : Fin (blockTotalRank n ranks)) :
    w.bong.order i =
      (c (w.indexEquiv i).1).order (w.indexEquiv i).2 := by
  apply WithTop.coe_injective
  simp only [BONG.coe_order, w.value_eq]

/-- An order-preserving block enumeration starts with the first vector of the
first nonempty block.  This is the exact endpoint fact needed when a new head
block is joined to a recursively concatenated tail. -/
theorem indexEquiv_zero (w : BlockBONGWitness n C qs Ls ranks c)
    (hzero : 0 < ranks 0) (htotal : 0 < blockTotalRank n ranks) :
    w.indexEquiv ⟨0, htotal⟩ = ⟨0, ⟨0, hzero⟩⟩ := by
  let target : Σ i, Fin (ranks i) := ⟨0, ⟨0, hzero⟩⟩
  let k : Fin (blockTotalRank n ranks) := w.indexEquiv.symm target
  let z : Fin (blockTotalRank n ranks) := ⟨0, htotal⟩
  have hk : k = z := by
    apply Fin.ext
    by_contra hne
    have hneZero : k.val ≠ 0 := by
      simpa [z] using hne
    have hkpos : z < k := by
      change z.val < k.val
      simpa [z] using Nat.pos_of_ne_zero hneZero
    have hbefore := (w.order_iff z k).1 hkpos
    have htarget : w.indexEquiv k = target :=
      w.indexEquiv.apply_symm_apply target
    rw [htarget] at hbefore
    simpa [BlockIndexBefore, target] using hbefore
  change w.indexEquiv z = target
  rw [← hk]
  exact w.indexEquiv.apply_symm_apply target

end BlockBONGWitness

/-- The one-coordinate product lattice is its sole component lattice. -/
noncomputable def blockOrthogonalSingletonLatticeIsometry
    (C : Fin 1 → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i)) :
    Lattice.Isometry (blockOrthogonalForm 0 C qs) (qs 0)
      (blockProductLattice 0 C Ls) (Ls 0) where
  toLinearEquiv := blockProductSingleton C
  map_bilin := (blockOrthogonalSingletonIsometry C qs).map_bilin
  map_mem x := by
    rw [mem_blockProductLattice_iff]
    constructor
    · intro h
      exact h 0
    · intro h i
      fin_cases i
      exact h

/-- The head--tail splitting carries the coordinate product lattice to a
binary product lattice. -/
noncomputable def blockOrthogonalSplitLatticeIsometry
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i)) :
    Lattice.Isometry (blockOrthogonalForm (n + 1) C qs)
      ((qs 0).orthogonalSum
        (blockOrthogonalForm n (fun i => C i.succ) (fun i => qs i.succ)))
      (blockProductLattice (n + 1) C Ls)
      (Lattice.product (Ls 0)
        (blockProductLattice n (fun i => C i.succ) (fun i => Ls i.succ))) where
  toLinearEquiv := blockProductSplit n C
  map_bilin := (blockOrthogonalSplitIsometry n C qs).map_bilin
  map_mem x := by
    rw [mem_blockProductLattice_iff, Lattice.mem_product_iff,
      mem_blockProductLattice_iff, Fin.forall_fin_succ]
    rfl

namespace BlockBONGWitness

/-- Concatenation witness for a family consisting of one block. -/
noncomputable def singleton
    (C : Fin 1 → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (ranks : Fin 1 → Nat)
    (c : ∀ i, BONG (C i) (qs i) (Ls i) (ranks i)) :
    BlockBONGWitness 0 C qs Ls ranks c := by
  let iso := blockOrthogonalSingletonLatticeIsometry C qs Ls
  let raw := (c 0).mapLatticeIsometry iso.symm
  have hlength : ranks 0 = blockTotalRank 0 ranks :=
    (blockTotalRank_zero ranks).symm
  let result := raw.castLength hlength
  let e := blockIndexEquivSingleton ranks
  refine
    { bong := result
      indexEquiv := e
      order_iff := ?_
      ambientVector_eq := ?_ }
  · intro i j
    change i.val < j.val ↔
      BlockIndexBefore (e i) (e j)
    simp [e, blockIndexEquivSingleton, BlockIndexBefore]
  · intro i
    rw [show result = raw.castLength hlength by rfl,
      BONG.ambientVector_castLength,
      show raw = (c 0).mapLatticeIsometry iso.symm by rfl,
      BONG.ambientVector_mapLatticeIsometry]
    change (blockProductSingleton C).symm
        ((c 0).ambientVector ⟨i.val, by omega⟩) = _
    funext k
    fin_cases k
    simp [e, blockIndexEquivSingleton, blockProductSingleton]
    congr 1

/-- Add a head block to an already concatenated nonempty tail. -/
noncomputable def cons
    (n : Nat) (C : Fin (n + 2) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (ranks : Fin (n + 2) → Nat)
    (c : ∀ i, BONG (C i) (qs i) (Ls i) (ranks i))
    (hrank : ∀ i, 0 < ranks i)
    (hcross : ∀ i : Fin (ranks 0),
      (c 0).order i ≤
        (c (Fin.succ 0)).order ⟨0, hrank (Fin.succ 0)⟩)
    (tail : BlockBONGWitness n (fun i => C i.succ)
      (fun i => qs i.succ) (fun i => Ls i.succ)
      (fun i => ranks i.succ) (fun i => c i.succ)) :
    BlockBONGWitness (n + 1) C qs Ls ranks c := by
  let tailLength := blockTotalRank n (fun i => ranks i.succ)
  have htailPos : 0 < tailLength := by
    let a : Σ j : Fin (n + 1), Fin (ranks j.succ) :=
      ⟨0, ⟨0, hrank (Fin.succ 0)⟩⟩
    have h := (tail.indexEquiv.symm a).isLt
    exact Nat.zero_lt_of_lt h
  have htailLength : tailLength = (tailLength - 1) + 1 := by
    omega
  let tailBONG := tail.bong.castLength htailLength
  have horder : ∀ i : Fin (ranks 0),
      (c 0).order i ≤ tailBONG.order 0 := by
    intro i
    rw [show tailBONG = tail.bong.castLength htailLength by rfl,
      BONG.order_castLength]
    change (c 0).order i ≤ tail.bong.order ⟨0, htailPos⟩
    rw [tail.order_eq,
      tail.indexEquiv_zero (hrank (Fin.succ 0)) htailPos]
    exact hcross i
  let raw := (c 0).orthogonalProductRight tailBONG horder
  let split := blockOrthogonalSplitLatticeIsometry n C qs Ls
  let mapped := raw.mapLatticeIsometry split.symm
  have hresultLength :
      (tailLength - 1) + 1 + ranks 0 = blockTotalRank (n + 1) ranks := by
    rw [← htailLength]
    rw [blockTotalRank_succ]
    change tailLength + ranks 0 = ranks 0 + tailLength
    omega
  let result := mapped.castLength hresultLength
  let e := blockIndexEquivCons n ranks tail.indexEquiv
  refine
    { bong := result
      indexEquiv := e
      order_iff := ?_
      ambientVector_eq := ?_ }
  · intro i j
    by_cases hi : i.val < ranks 0
    · let ii : Fin (ranks 0) := ⟨i.val, hi⟩
      have hiEq : i = blockLeftIndex n ranks ii := by
        apply Fin.ext
        rfl
      by_cases hj : j.val < ranks 0
      · let jj : Fin (ranks 0) := ⟨j.val, hj⟩
        have hjEq : j = blockLeftIndex n ranks jj := by
          apply Fin.ext
          rfl
        rw [hiEq, hjEq]
        simp only [e, blockIndexEquivCons_left]
        simp [BlockIndexBefore]
        rfl
      · have hjBound : j.val - ranks 0 < tailLength := by
          have hjLt : j.val < ranks 0 + tailLength := by
            calc
              j.val < blockTotalRank (n + 1) ranks := j.isLt
              _ = ranks 0 + tailLength := blockTotalRank_succ n ranks
          omega
        let jj : Fin tailLength := ⟨j.val - ranks 0, hjBound⟩
        have hjEq : j = blockRightIndex n ranks jj := by
          apply Fin.ext
          simp [jj]
          omega
        rw [hiEq, hjEq]
        simp only [e, blockIndexEquivCons_left,
          blockIndexEquivCons_right]
        simp [BlockIndexBefore]
        omega
    · have hiBound : i.val - ranks 0 < tailLength := by
        have hiLt : i.val < ranks 0 + tailLength := by
          calc
            i.val < blockTotalRank (n + 1) ranks := i.isLt
            _ = ranks 0 + tailLength := blockTotalRank_succ n ranks
        omega
      let ii : Fin tailLength := ⟨i.val - ranks 0, hiBound⟩
      have hiEq : i = blockRightIndex n ranks ii := by
        apply Fin.ext
        simp [ii]
        omega
      by_cases hj : j.val < ranks 0
      · let jj : Fin (ranks 0) := ⟨j.val, hj⟩
        have hjEq : j = blockLeftIndex n ranks jj := by
          apply Fin.ext
          rfl
        rw [hiEq, hjEq]
        simp only [e, blockIndexEquivCons_right,
          blockIndexEquivCons_left]
        simp [BlockIndexBefore]
        omega
      · have hjBound : j.val - ranks 0 < tailLength := by
          have hjLt : j.val < ranks 0 + tailLength := by
            calc
              j.val < blockTotalRank (n + 1) ranks := j.isLt
              _ = ranks 0 + tailLength := blockTotalRank_succ n ranks
          omega
        let jj : Fin tailLength := ⟨j.val - ranks 0, hjBound⟩
        have hjEq : j = blockRightIndex n ranks jj := by
          apply Fin.ext
          simp [jj]
          omega
        rw [hiEq, hjEq]
        change ranks 0 + ii.val < ranks 0 + jj.val ↔
          BlockIndexBefore (e (blockRightIndex n ranks ii))
            (e (blockRightIndex n ranks jj))
        rw [Nat.add_lt_add_iff_left]
        change ii < jj ↔
          BlockIndexBefore (e (blockRightIndex n ranks ii))
            (e (blockRightIndex n ranks jj))
        rw [tail.order_iff]
        simp only [e, blockIndexEquivCons_right]
        simp [BlockIndexBefore]
  · intro i
    by_cases hi : i.val < ranks 0
    · let ii : Fin (ranks 0) := ⟨i.val, hi⟩
      have hiEq : i = blockLeftIndex n ranks ii := by
        apply Fin.ext
        rfl
      rw [hiEq]
      rw [show result = mapped.castLength hresultLength by rfl,
        BONG.ambientVector_castLength,
        show mapped = raw.mapLatticeIsometry split.symm by rfl,
        BONG.ambientVector_mapLatticeIsometry]
      change (blockProductSplit n C).symm
          (raw.ambientVector
            (BONG.orthogonalProductLeftIndex
              ((tailLength - 1) + 1) ii)) = _
      rw [show raw = (c 0).orthogonalProductRight tailBONG horder by rfl,
        BONG.ambientVector_orthogonalProductRight_left]
      have he :
          e (blockLeftIndex n ranks ii) = ⟨0, ii⟩ := by
        exact blockIndexEquivCons_left n ranks tail.indexEquiv ii
      rw [he]
      exact blockProductSplit_symm_inl (K := K) n C
        ((c 0).ambientVector ii)
    · have hiBound : i.val - ranks 0 < tailLength := by
        have hiLt : i.val < ranks 0 + tailLength := by
          calc
            i.val < blockTotalRank (n + 1) ranks := i.isLt
            _ = ranks 0 + tailLength := blockTotalRank_succ n ranks
        omega
      let ii : Fin tailLength := ⟨i.val - ranks 0, hiBound⟩
      have hiEq : i = blockRightIndex n ranks ii := by
        apply Fin.ext
        simp [ii]
        omega
      rw [hiEq]
      let iiCast : Fin ((tailLength - 1) + 1) := ⟨ii.val, by omega⟩
      rw [show result = mapped.castLength hresultLength by rfl,
        BONG.ambientVector_castLength,
        show mapped = raw.mapLatticeIsometry split.symm by rfl,
        BONG.ambientVector_mapLatticeIsometry]
      change (blockProductSplit n C).symm
          (raw.ambientVector
            (BONG.orthogonalProductRightIndex (ranks 0) iiCast)) = _
      rw [show raw = (c 0).orthogonalProductRight tailBONG horder by rfl,
        BONG.ambientVector_orthogonalProductRight_right]
      change (blockProductSplit n C).symm
          (0, tailBONG.ambientVector iiCast) = _
      rw [show tailBONG = tail.bong.castLength htailLength by rfl,
        BONG.ambientVector_castLength]
      have htailVector := tail.ambientVector_eq ii
      rw [htailVector]
      have he :
          e (blockRightIndex n ranks ii) =
            ⟨(tail.indexEquiv ii).1.succ,
              (tail.indexEquiv ii).2⟩ := by
        exact blockIndexEquivCons_right n ranks tail.indexEquiv ii
      rw [he]
      exact blockProductSplit_symm_inr_single (K := K) n C
        (tail.indexEquiv ii).1
        ((c (tail.indexEquiv ii).1.succ).ambientVector
          (tail.indexEquiv ii).2)

/-- Recursively concatenate a nonempty finite family.  Only the order of a
vector in an earlier block relative to the first vector of a later block is
required; no monotonicity inside a modular binary block is assumed. -/
noncomputable def ofFamily
    (n : Nat) (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (ranks : Fin (n + 1) → Nat)
    (c : ∀ i, BONG (C i) (qs i) (Ls i) (ranks i))
    (hrank : ∀ i, 0 < ranks i)
    (hcross : ∀ {i j : Fin (n + 1)}, i < j →
      ∀ k : Fin (ranks i),
        (c i).order k ≤ (c j).order ⟨0, hrank j⟩) :
    BlockBONGWitness n C qs Ls ranks c := by
  induction n with
  | zero =>
      exact singleton C qs Ls ranks c
  | succ n ih =>
      have htailCross :
          ∀ {i j : Fin (n + 1)}, i < j →
            ∀ k : Fin (ranks i.succ),
              (c i.succ).order k ≤
                (c j.succ).order ⟨0, hrank j.succ⟩ := by
        intro i j hij k
        exact hcross (i := i.succ) (j := j.succ) (by
          change i.val + 1 < j.val + 1
          omega) k
      let tail := ih
        (C := fun i ↦ C i.succ)
        (qs := fun i ↦ qs i.succ)
        (Ls := fun i ↦ Ls i.succ)
        (ranks := fun i ↦ ranks i.succ)
        (c := fun i ↦ c i.succ)
        (hrank := fun i ↦ hrank i.succ)
        htailCross
      exact cons n C qs Ls ranks c hrank
        (fun i ↦ hcross (i := 0) (j := Fin.succ 0) (by
          change (0 : Nat) < 0 + 1
          omega) i)
        tail

end BlockBONGWitness

open Lattice.OrthogonalDecomposition

/-- The canonical linear equivalence that adds the component vectors of an
orthogonal decomposition. -/
noncomputable def orthogonalDecompositionProductLinearEquiv
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (D : Lattice.OrthogonalDecomposition q L (n + 1)) :
    BlockProductSpace n (fun i ↦ (D.component i).carrier) ≃ₗ[K] V :=
  (DirectSum.linearEquivFunOnFintype K (Fin (n + 1))
      (fun i ↦ (D.component i).carrier)).symm.trans
    D.carrierDirectSumEquiv

/-- A vector supported in one product coordinate maps to the same component
vector in the ambient space. -/
@[simp]
theorem orthogonalDecompositionProductLinearEquiv_single
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (D : Lattice.OrthogonalDecomposition q L (n + 1))
    (i : Fin (n + 1)) (x : (D.component i).carrier) :
    orthogonalDecompositionProductLinearEquiv D (Pi.single i x) =
      (x : V) := by
  rw [orthogonalDecompositionProductLinearEquiv,
    LinearEquiv.trans_apply,
    DirectSum.linearEquivFunOnFintype_symm_single,
    Lattice.OrthogonalDecomposition.carrierDirectSumEquiv]
  change
    (DFinsupp.lsum ℕ
      (fun j ↦ (D.component j).carrier.subtype))
        (DFinsupp.single i x) = (x : V)
  rw [DFinsupp.lsum_single]
  rfl

/-- The coordinate product of the components of an orthogonal decomposition
is isometric, integrally and quadratically, to the ambient lattice. -/
noncomputable def orthogonalDecompositionProductIsometry
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (D : Lattice.OrthogonalDecomposition q L (n + 1)) :
    Lattice.Isometry
      (blockOrthogonalForm n
        (fun i => (D.component i).carrier)
        (fun i => (D.component i).space)) q
      (blockProductLattice n
        (fun i => (D.component i).carrier)
        (fun i => (D.component i).lattice)) L := by
  let sourceBasis := blockProductBasis n
    (fun i => (D.component i).carrier)
    (fun i => (D.component i).lattice)
  let targetBasis := D.componentAmbientBasis
  have hgram : ∀ a b,
      q.bilin (targetBasis a) (targetBasis b) =
        (blockOrthogonalForm n
          (fun i => (D.component i).carrier)
          (fun i => (D.component i).space)).bilin
            (sourceBasis a) (sourceBasis b) := by
    classical
    rintro ⟨i, ai⟩ ⟨j, aj⟩
    simp only [targetBasis, sourceBasis,
      D.componentAmbientBasis_apply, blockProductBasis, Pi.basis_apply,
      blockOrthogonalForm_bilin_apply]
    by_cases hij : i = j
    · subst j
      rw [Fintype.sum_eq_single i]
      · rw [Pi.single_eq_same, Pi.single_eq_same]
        rfl
      · intro k hki
        rw [Pi.single_eq_of_ne hki]
        simp
    · rw [D.orthogonal i j hij]
      symm
      apply Finset.sum_eq_zero
      intro k _
      by_cases hki : k = i
      · subst k
        rw [Pi.single_eq_of_ne hij]
        simp
      · rw [Pi.single_eq_of_ne hki]
        simp
  let f := orthogonalDecompositionProductLinearEquiv D
  have hmapBasis : ∀ a, f (sourceBasis a) = targetBasis a := by
    rintro ⟨i, ai⟩
    simp only [f, sourceBasis, targetBasis, blockProductBasis,
      Pi.basis_apply,
      orthogonalDecompositionProductLinearEquiv_single,
      D.componentAmbientBasis_apply]
  have hfBasis :
      f = sourceBasis.equiv targetBasis (Equiv.refl _) := by
    apply LinearEquiv.toLinearMap_injective
    apply sourceBasis.ext
    intro a
    change f (sourceBasis a) =
      (sourceBasis.equiv targetBasis (Equiv.refl _)) (sourceBasis a)
    rw [hmapBasis]
    simp [Basis.equiv]
  refine
    { toLinearEquiv := f
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    have hforms :
        q.bilin.comp f.toLinearMap f.toLinearMap =
          (blockOrthogonalForm n
            (fun i => (D.component i).carrier)
            (fun i => (D.component i).space)).bilin := by
      apply LinearMap.BilinForm.ext_basis sourceBasis
      intro a b
      rw [LinearMap.BilinForm.comp_apply]
      change q.bilin (f (sourceBasis a)) (f (sourceBasis b)) = _
      rw [hmapBasis a, hmapBasis b]
      exact hgram a b
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    change x ∈ blockProductLattice n
        (fun i => (D.component i).carrier)
        (fun i => (D.component i).lattice) ↔ f x ∈ L
    change x ∈ Lattice.basisLattice sourceBasis ↔ f x ∈ L
    have htargetMem :
        f x ∈ L ↔ f x ∈ Lattice.basisLattice targetBasis := by
      rw [D.basisLattice_componentAmbientBasis]
    rw [htargetMem,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr : targetBasis.repr (f x) = sourceBasis.repr x := by
      rw [hfBasis]
      simp [Basis.equiv]
    rw [hrepr]

end BONG

end Bong
