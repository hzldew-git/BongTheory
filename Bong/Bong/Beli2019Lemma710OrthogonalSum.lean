/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NormIdealOrthogonalProduct

/-!
# Beli (2019), Lemma 7.10: norm generators in an orthogonal sum

The right-end proof of Lemma 7.10 repeatedly uses the fact that a norm
generator of the left component remains a norm generator after adjoining an
orthogonal component whose norm ideal is smaller.  This file proves that
claim for the concrete product model of an orthogonal sum and derives the
order formulation used for BONG heads.
-/

namespace Bong

open Dyadic

universe u v w

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A left norm generator remains a norm generator after adjoining an
orthogonal component with a contained norm ideal. -/
theorem IsNormGenerator.orthogonalProduct_left
    {x : V} (generator : IsNormGenerator q L x)
    (hM : normIdeal r M ≤ normIdeal q L) :
    IsNormGenerator (q.orthogonalSum r) (product L M) (x, 0) := by
  constructor
  · exact inl_mem_product_iff.mpr generator.mem
  · rw [normIdeal_orthogonalProduct, sup_eq_left.mpr hM]
    simpa using generator.normIdeal_eq

/-- The symmetric right-component version. -/
theorem IsNormGenerator.orthogonalProduct_right
    {y : W} (generator : IsNormGenerator r M y)
    (hL : normIdeal q L ≤ normIdeal r M) :
    IsNormGenerator (q.orthogonalSum r) (product L M) (0, y) := by
  constructor
  · exact inr_mem_product_iff.mpr generator.mem
  · rw [normIdeal_orthogonalProduct, sup_eq_right.mpr hL]
    simpa using generator.normIdeal_eq

end Lattice

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Comparing the head orders of two nonempty BONGs compares their norm
ideals in the contravariant direction.  This is the ideal-theoretic form of
the numerical hypothesis used at each decreasing-induction step in Lemma
7.10. -/
theorem normIdeal_le_of_head_order_le
    (b : BONG V q L (n + 1)) (c : BONG W r M (m + 1))
    (horder : b.order 0 ≤ c.order 0) :
    Lattice.normIdeal r M ≤ Lattice.normIdeal q L := by
  rw [c.head_isNormGenerator.normIdeal_eq,
    b.head_isNormGenerator.normIdeal_eq]
  apply (Lattice.principalIdeal_le_iff_ord_ge
    c.head_isAnisotropic b.head_isAnisotropic).mpr
  have h := WithTop.coe_le_coe.mpr horder
  rw [b.coe_order, c.coe_order,
    b.value_zero_eq_quadratic_head,
    c.value_zero_eq_quadratic_head] at h
  exact h

/-- Conversely, containment of the two norm ideals recovers the comparison
of the head orders.  Together with `normIdeal_le_of_head_order_le`, this is
the exact ideal/order dictionary used at the stopping point of Lemma 7.10. -/
theorem head_order_le_of_normIdeal_le
    (b : BONG V q L (n + 1)) (c : BONG W r M (m + 1))
    (hideal : Lattice.normIdeal r M ≤ Lattice.normIdeal q L) :
    b.order 0 ≤ c.order 0 := by
  rw [c.head_isNormGenerator.normIdeal_eq,
    b.head_isNormGenerator.normIdeal_eq] at hideal
  have hord := (Lattice.principalIdeal_le_iff_ord_ge
    c.head_isAnisotropic b.head_isAnisotropic).mp hideal
  apply WithTop.coe_le_coe.mp
  rw [b.coe_order, c.coe_order,
    b.value_zero_eq_quadratic_head,
    c.value_zero_eq_quadratic_head]
  exact hord

/-- The order comparison used in the right-end case of Lemma 7.10 makes the
head of the left BONG a norm generator of the whole orthogonal product. -/
theorem head_isNormGenerator_orthogonalProduct_left
    (b : BONG V q L (n + 1)) (c : BONG W r M (m + 1))
    (horder : b.order 0 ≤ c.order 0) :
    Lattice.IsNormGenerator (q.orthogonalSum r)
      (Lattice.product L M) (b.head, 0) := by
  apply b.head_isNormGenerator.orthogonalProduct_left
  exact normIdeal_le_of_head_order_le b c horder

end BONG

end Bong
