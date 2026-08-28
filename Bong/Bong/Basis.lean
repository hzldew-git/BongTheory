/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Basic
import Bong.Dyadic.QuadraticDefect
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The ambient orthogonal basis carried by a BONG

Although a BONG is defined recursively in successive orthogonal complements,
its vectors canonically lift to an orthogonal basis of the original quadratic
space.  This file constructs that basis and identifies its Gram determinant
with the product of the BONG values.

The construction is the linear-algebraic part of Beli's Lemma 2.1.  It does not
yet identify the Gram determinant with the volume ideal of the integral lattice.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

private noncomputable def basisNil {V' : Type v} [AddCommGroup V'] [Module K V']
    (_q : QuadraticSpace K V') (_L : Lattice K V') (exhausted : Subsingleton V') :
    Basis (Fin 0) K V' := by
  letI : Subsingleton V' := exhausted
  exact Basis.empty V'

private noncomputable def basisCons {V' : Type v} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'} {m : Nat}
    (x : V') (_generator : Lattice.IsNormGenerator q' L' x)
    (hx : q'.IsAnisotropic x)
    (_tail : BONG (q'.vectorOrthogonal x) (q'.orthogonalSpace x hx)
      (L'.projectedLattice q' x hx) m)
    (tailBasis : Basis (Fin m) K (q'.vectorOrthogonal x)) :
    Basis (Fin (m + 1)) K V' :=
  Basis.mkFinCons x tailBasis (by
    intro c y hy h
    have hbilin : q'.bilin x (c • x + (y : V')) = 0 := by
      rw [h]
      simp
    rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right] at hbilin
    have hy' : q'.bilin x y = 0 := (q'.mem_vectorOrthogonal_iff x y).1 hy
    change c * q'.quadratic x + q'.bilin x y = 0 at hbilin
    rw [hy', add_zero] at hbilin
    exact (mul_eq_zero.mp hbilin).resolve_right hx) (by
    intro z
    refine ⟨-(q'.bilin x z / q'.quadratic x), ?_⟩
    have hz := q'.orthogonalProjection_mem_vectorOrthogonal hx z
    simpa [q'.orthogonalProjection_apply, sub_eq_add_neg] using hz)

/-- The `Fin`-indexed ambient basis canonically determined by a recursive BONG. -/
noncomputable def basis {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : Basis (Fin n) K V :=
  BONG.rec (motive := fun V _ _ _ _ m _ => Basis (Fin m) K V) basisNil basisCons b

/-- The ambient vector family underlying a BONG. -/
noncomputable def ambientVector {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : Fin n → V :=
  b.basis

/-- Transport a BONG along equality of its lattice index. -/
noncomputable def castLattice {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (b : BONG V q M n) (h : M = N) : BONG V q N n :=
  h ▸ b

/-- Transporting the lattice index does not change BONG values. -/
@[simp]
theorem value_castLattice {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (b : BONG V q M n) (h : M = N) (i : Fin n) :
    (b.castLattice h).value i = b.value i := by
  subst N
  rfl

/-- Transporting the lattice index does not change integral BONG orders. -/
@[simp]
theorem order_castLattice {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (b : BONG V q M n) (h : M = N) (i : Fin n) :
    (b.castLattice h).order i = b.order i := by
  apply WithTop.coe_injective
  rw [coe_order, coe_order, value_castLattice]

/-- Transporting the lattice index does not change ambient BONG vectors. -/
@[simp]
theorem ambientVector_castLattice {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}
    (b : BONG V q M n) (h : M = N) (i : Fin n) :
    (b.castLattice h).ambientVector i = b.ambientVector i := by
  subst N
  rfl

@[simp]
theorem ambientVector_cons_zero {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {x : V} {hx : Lattice.IsNormGenerator q L x} {han : q.IsAnisotropic x}
    {b : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x han)
      (L.projectedLattice q x han) n} :
    (BONG.cons x hx han b).ambientVector 0 = x := by
  simp [ambientVector, basis, basisCons]

@[simp]
theorem ambientVector_cons_succ {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {x : V} {hx : Lattice.IsNormGenerator q L x} {han : q.IsAnisotropic x}
    {b : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x han)
      (L.projectedLattice q x han) n} (i : Fin n) :
    (BONG.cons x hx han b).ambientVector i.succ = (b.ambientVector i : V) := by
  simp [ambientVector, basis, basisCons]

/-- Tail ambient vectors are the positive-index ambient vectors of the
original BONG. -/
@[simp]
theorem coe_ambientVector_tail {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) (i : Fin n) :
    (b.tail.ambientVector i : V) = b.ambientVector i.succ := by
  cases b with
  | cons x generator anisotropic tail =>
      exact (ambientVector_cons_succ (K := K) (b := tail) i).symm

/-- The zeroth ambient basis vector is the recursive BONG head. -/
theorem ambientVector_zero_eq_head {V : Type v} [AddCommGroup V]
    [Module K V] {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 1)) : b.ambientVector 0 = b.head := by
  cases b with
  | cons x _ _ _ =>
      rw [ambientVector_cons_zero]
      change x = x
      rfl

@[simp]
theorem quadratic_ambientVector {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i : Fin n) :
    q.quadratic (b.ambientVector i) = b.value i := by
  induction b with
  | nil => exact Fin.elim0 i
  | cons x _ _ tail ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [ambientVector_cons_zero, value_cons_zero]
      · simpa using ih j

/-- The ambient vectors of a BONG are pairwise orthogonal. -/
theorem ambientVector_iIsOrtho {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : q.bilin.iIsOrtho b.ambientVector := by
  induction b with
  | nil =>
      rw [LinearMap.BilinForm.iIsOrtho_def]
      exact fun i => Fin.elim0 i
  | @cons V' _ _ q' L' n' x _ hx tail ih =>
      rw [LinearMap.BilinForm.iIsOrtho_def]
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j' =>
              simp only [ambientVector_cons_zero, ambientVector_cons_succ]
              exact (q'.mem_vectorOrthogonal_iff x (tail.ambientVector j')).1
                (tail.ambientVector j').property
      | succ i' =>
          cases j using Fin.cases with
          | zero =>
              simp only [ambientVector_cons_zero, ambientVector_cons_succ]
              rw [q'.isSymm.eq]
              exact (q'.mem_vectorOrthogonal_iff x (tail.ambientVector i')).1
                (tail.ambientVector i').property
          | succ j' =>
              simp only [ambientVector_cons_succ]
              apply (LinearMap.BilinForm.iIsOrtho_def.mp ih)
              intro h
              apply hij
              exact congrArg (@Fin.succ n') h

/-- The ambient BONG vectors are linearly independent. -/
theorem ambientVector_linearIndependent {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : LinearIndependent K b.ambientVector :=
  b.basis.linearIndependent

/-- The ambient BONG vectors span the full quadratic space. -/
theorem span_ambientVector_eq_top {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : Submodule.span K (Set.range b.ambientVector) = ⊤ :=
  b.basis.span_eq

/-- The length of a BONG is the dimension of its ambient quadratic space. -/
theorem length_eq_finrank {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : n = finrank K V := by
  letI := b.basis.finiteDimensional_of_finite
  simpa using (finrank_eq_card_basis b.basis).symm

/-- The Gram matrix of the ambient BONG basis. -/
noncomputable def gramMatrix {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : Matrix (Fin n) (Fin n) K :=
  LinearMap.BilinForm.toMatrix b.basis q.bilin

@[simp]
theorem gramMatrix_apply {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) (i j : Fin n) :
    b.gramMatrix i j = q.bilin (b.ambientVector i) (b.ambientVector j) :=
  LinearMap.BilinForm.toMatrix_apply b.basis q.bilin i j

/-- Orthogonality makes the BONG Gram matrix diagonal. -/
theorem gramMatrix_eq_diagonal {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : b.gramMatrix = Matrix.diagonal b.value := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [gramMatrix_apply, Matrix.diagonal_apply_eq]
    change q.quadratic (b.ambientVector i) = b.value i
    exact quadratic_ambientVector b i
  · rw [gramMatrix_apply]
    rw [(LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho) i j hij]
    simp [hij]

/-- The determinant of the Gram matrix in the ambient BONG basis. -/
noncomputable def gramDeterminant {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : K :=
  Matrix.det b.gramMatrix

@[simp]
theorem coe_valueProduct {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : (b.valueProduct : K) = ∏ i, b.value i := by
  simp [valueProduct, prefixProduct]

@[simp]
theorem valueProduct_nil {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (exhausted : Subsingleton V) :
    (BONG.nil q L exhausted).valueProduct = 1 := by
  apply Units.ext
  simp

@[simp]
theorem valueProduct_cons {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    {x : V} {generator : Lattice.IsNormGenerator q L x}
    {anisotropic : q.IsAnisotropic x}
    (tail : BONG (q.vectorOrthogonal x) (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) n) :
    (BONG.cons x generator anisotropic tail).valueProduct =
      (BONG.cons x generator anisotropic tail).valueUnit 0 * tail.valueProduct := by
  apply Units.ext
  simp [Fin.prod_univ_succ]

/-- The BONG Gram determinant is the product of its quadratic values. -/
theorem gramDeterminant_eq_valueProduct {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L n) : b.gramDeterminant = (b.valueProduct : K) := by
  rw [gramDeterminant, gramMatrix_eq_diagonal, Matrix.det_diagonal, coe_valueProduct]

/-- Value products in two BONG bases differ by the square of the change-of-basis
determinant. -/
theorem exists_valueProduct_eq_mul_square
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (b : BONG V q L n) (c : BONG V q M n) :
    ∃ p : Kˣ, c.valueProduct = b.valueProduct * p ^ 2 := by
  let P : Matrix (Fin n) (Fin n) K := b.basis.toMatrix c.basis
  have hmatrix : P.transpose * b.gramMatrix * P = c.gramMatrix := by
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b.basis c.basis q.bilin
  have hdet : c.gramDeterminant = b.gramDeterminant * Matrix.det P ^ 2 := by
    rw [gramDeterminant, gramDeterminant, ← hmatrix]
    simp only [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hc : c.gramDeterminant ≠ 0 := by
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c.basis).mp
      q.nondegenerate
  have hP : Matrix.det P ≠ 0 := by
    intro hzero
    apply hc
    rw [hdet, hzero]
    simp
  let p : Kˣ := Units.mk0 (Matrix.det P) hP
  have hv : c.valueProduct = b.valueProduct * p ^ 2 := by
    apply Units.ext
    change (c.valueProduct : K) = (b.valueProduct : K) * Matrix.det P ^ 2
    rw [← gramDeterminant_eq_valueProduct c,
      ← gramDeterminant_eq_valueProduct b]
    exact hdet
  exact ⟨p, hv⟩

/--
The ordinary field square class of the value product is independent of the
BONG, even when the two BONGs belong to different lattices in the same
quadratic space.
-/
theorem valueProduct_squareClass_eq {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    (b : BONG V q L n) (c : BONG V q M n) :
    squareClass K b.valueProduct = squareClass K c.valueProduct := by
  rcases exists_valueProduct_eq_mul_square b c with ⟨p, hv⟩
  rw [hv]
  exact (squareClass_mul_square K b.valueProduct p).symm

end BONG

end Bong
