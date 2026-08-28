/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Good
import Bong.Bong.Basis
import Bong.Lattice.Dual
import Mathlib.Data.Fin.Rev

/-!
# Reversed dual vectors of a BONG

Beli (2003), Lemma 4.8 reverses a good BONG and replaces each vector `x` by
`Q(x)⁻¹ x`.  This file proves the scalar and order-theoretic part of that
construction independently of the integral dual-lattice realization.
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

/-- The bilinear dual of the `i`th ambient BONG vector. -/
noncomputable def dualVector (b : BONG V q L n) (i : Fin n) : V :=
  ((b.valueUnit i)⁻¹ : K) • b.ambientVector i

/-- Dual BONG vectors pair with the ambient BONG basis by Kronecker delta. -/
theorem bilin_dualVector_ambientVector (b : BONG V q L n)
    (i j : Fin n) :
    q.bilin (b.dualVector i) (b.ambientVector j) =
      if j = i then 1 else 0 := by
  rw [dualVector, LinearMap.BilinForm.smul_left]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    change (b.value i)⁻¹ * q.quadratic (b.ambientVector i) = 1
    rw [b.quadratic_ambientVector]
    change (b.value i)⁻¹ * b.value i = 1
    exact inv_mul_cancel₀ (b.value_ne_zero i)
  · rw [if_neg hji]
    have hij : i ≠ j := fun hij => hji hij.symm
    rw [(LinearMap.BilinForm.iIsOrtho_def.mp
      b.ambientVector_iIsOrtho) i j hij]
    simp

/-- The bilinear dual basis is given by the normalized BONG vectors. -/
theorem dualBasis_eq_dualVector (b : BONG V q L n) :
    ⇑(q.bilin.dualBasis q.nondegenerate b.basis) = b.dualVector := by
  apply (LinearMap.BilinForm.dualBasis_eq_iff
    q.nondegenerate b.basis b.dualVector).2
  exact b.bilin_dualVector_ambientVector

/-- The normalized dual vectors remain pairwise orthogonal. -/
theorem dualVector_iIsOrtho (b : BONG V q L n) :
    q.bilin.iIsOrtho b.dualVector := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  rw [dualVector, dualVector, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [(LinearMap.BilinForm.iIsOrtho_def.mp
    b.ambientVector_iIsOrtho) i j hij]
  simp

/-- The reversed dual vector `x_{n-1-i} / Q(x_{n-1-i})`. -/
noncomputable def reverseDualVector (b : BONG V q L n) (i : Fin n) : V :=
  b.dualVector (Fin.rev i)

/-- The reversed dual vectors form an ambient basis. -/
noncomputable def reverseDualBasis (b : BONG V q L n) : Basis (Fin n) K V :=
  (q.bilin.dualBasis q.nondegenerate b.basis).reindex Fin.revPerm

@[simp]
theorem reverseDualBasis_apply (b : BONG V q L n) (i : Fin n) :
    b.reverseDualBasis i = b.reverseDualVector i := by
  rw [reverseDualBasis, Module.Basis.reindex_apply, Fin.revPerm_symm]
  exact congrFun b.dualBasis_eq_dualVector (Fin.rev i)

/-- The reversed dual basis is orthogonal. -/
theorem reverseDualBasis_iIsOrtho (b : BONG V q L n) :
    q.bilin.iIsOrtho b.reverseDualBasis := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i j hij
  rw [b.reverseDualBasis_apply, b.reverseDualBasis_apply]
  apply (LinearMap.BilinForm.iIsOrtho_def.mp b.dualVector_iIsOrtho)
  exact fun h => hij (Fin.rev_injective h)

/-- For the basis lattice, the reverse-dual basis integrally generates its dual. -/
theorem basisLattice_reverseDualBasis (b : BONG V q L n) :
    Lattice.basisLattice b.reverseDualBasis =
      Lattice.dualLattice q (Lattice.basisLattice b.basis) := by
  rw [reverseDualBasis, Lattice.basisLattice_reindex]
  exact (Lattice.dualLattice_basisLattice q b.basis).symm

/-- The reverse-dual vector has the reciprocal quadratic value. -/
@[simp]
theorem quadratic_reverseDualVector (b : BONG V q L n) (i : Fin n) :
    q.quadratic (b.reverseDualVector i) =
      ((b.valueUnit (Fin.rev i))⁻¹ : K) := by
  rw [reverseDualVector, dualVector, q.quadratic_smul,
    quadratic_ambientVector]
  change ((b.valueUnit (Fin.rev i) : K) ⁻¹) ^ 2 *
      (b.valueUnit (Fin.rev i) : K) =
    (b.valueUnit (Fin.rev i) : K) ⁻¹
  field_simp

/-- The reverse-dual quadratic value is nonzero. -/
theorem quadratic_reverseDualVector_ne_zero (b : BONG V q L n)
    (i : Fin n) : q.quadratic (b.reverseDualVector i) ≠ 0 := by
  rw [quadratic_reverseDualVector]
  exact inv_ne_zero (b.value_ne_zero (Fin.rev i))

/-- Every vector of the reverse-dual basis is anisotropic. -/
theorem reverseDualBasis_isAnisotropic (b : BONG V q L n) (i : Fin n) :
    q.IsAnisotropic (b.reverseDualBasis i) := by
  rw [b.reverseDualBasis_apply]
  exact b.quadratic_reverseDualVector_ne_zero i

/-- Reversing and normalizing a second time recovers the original vector. -/
theorem normalize_reverseDualVector_rev (b : BONG V q L n) (i : Fin n) :
    (q.quadratic (b.reverseDualVector (Fin.rev i)))⁻¹ •
        b.reverseDualVector (Fin.rev i) =
      b.ambientVector i := by
  rw [quadratic_reverseDualVector, reverseDualVector, Fin.rev_rev,
    dualVector, smul_smul]
  change
    ((((b.valueUnit i)⁻¹ : K)⁻¹) * ((b.valueUnit i)⁻¹ : K)) •
        b.ambientVector i = b.ambientVector i
  rw [inv_inv, mul_inv_cancel₀ (Units.ne_zero (b.valueUnit i)), one_smul]

/-- The order of a reverse-dual value is the negative reversed BONG order. -/
theorem ord_quadratic_reverseDualVector (b : BONG V q L n) (i : Fin n) :
    ord K (q.quadratic (b.reverseDualVector i)) =
      ((-b.order (Fin.rev i) : Int) : WithTop Int) := by
  rw [quadratic_reverseDualVector]
  change ord K (((b.valueUnit (Fin.rev i))⁻¹ : Kˣ) : K) = _
  rw [← coe_ordUnit, ordUnit_inv, ← b.order_eq_ordUnit]

/-- Reversing and negating a good order sequence preserves goodness. -/
theorem reverseDual_orders_good (b : BONG V q L n) (hb : b.IsGood) :
    ∀ (i : Fin n) (hi : i.1 + 2 < n),
      -b.order (Fin.rev i) ≤
        -b.order (Fin.rev ⟨i.1 + 2, hi⟩) := by
  intro i hi
  let j : Fin n := Fin.rev ⟨i.1 + 2, hi⟩
  have hj : j.1 + 2 < n := by
    simp [j]
    omega
  have hgood := hb j hj
  have hindex : (⟨j.1 + 2, hj⟩ : Fin n) = Fin.rev i := by
    apply Fin.ext
    simp [j]
    omega
  rw [hindex] at hgood
  change -b.order (Fin.rev i) ≤ -b.order j
  omega

end BONG

end Bong
