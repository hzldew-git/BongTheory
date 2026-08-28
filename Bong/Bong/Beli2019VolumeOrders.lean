/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ExtremalDifference
import Bong.Bong.Structural

/-!
# Beli (2019), volume orders and BONG order sums

This file proves in every rank that the order of a lattice volume is the sum
of the orders in any BONG.  It then identifies the suffix sums used in
Section 5 with volume orders after deleting an initial block.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- In arbitrary rank, the volume order is the valuation of the product of
the BONG values. -/
theorem volumeOrder_eq_ordUnit_valueProduct_all (b : BONG V q L n) :
    Lattice.volumeOrder q L = ordUnit K b.valueProduct := by
  have hclass := b.determinantClass_eq_valueProduct
  change unitSquareClass K (Lattice.determinantUnit q L) =
    unitSquareClass K b.valueProduct at hclass
  have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  calc
    Lattice.volumeOrder q L =
        ordUnit K (Lattice.determinantUnit q L) := by
      apply WithTop.coe_injective
      rw [Lattice.coe_volumeOrder, coe_ordUnit,
        Lattice.coe_determinantUnit]
    _ = ordUnit K b.valueProduct := hord

/-- The valuation of the product of all BONG values is the finite sum of the
individual BONG orders. -/
theorem ordUnit_valueProduct_eq_sum_order (b : BONG V q L n) :
    ordUnit K b.valueProduct = ∑ i, b.order i := by
  rw [valueProduct, prefixProduct]
  have hfilter :
      Finset.univ.filter (fun j : Fin n ↦ j.1 < n) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact i.isLt
  rw [hfilter]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simp [ordUnit]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ordUnit_mul, ih]
      exact congrArg (fun z : Int ↦ z + ∑ j ∈ s, b.order j)
        (b.order_eq_ordUnit i).symm

/-- The volume order is the sum of all BONG orders. -/
theorem volumeOrder_eq_sum_order (b : BONG V q L n) :
    Lattice.volumeOrder q L = ∑ i, b.order i := by
  rw [b.volumeOrder_eq_ordUnit_valueProduct_all,
    b.ordUnit_valueProduct_eq_sum_order]

/-- Splitting off the head order leaves the sum of the projected-tail
orders. -/
theorem volumeOrder_eq_order_zero_add_sum_tail
    (b : BONG V q L (n + 1)) :
    Lattice.volumeOrder q L = b.order 0 + ∑ i, b.tail.order i := by
  rw [b.volumeOrder_eq_sum_order, Fin.sum_univ_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (b.order_tail i).symm

/-- The sum of the tail orders is the volume order minus the head order. -/
theorem sum_tail_order_eq_volumeOrder_sub_order_zero
    (b : BONG V q L (n + 1)) :
    (∑ i, b.tail.order i) =
      Lattice.volumeOrder q L - b.order 0 := by
  rw [b.volumeOrder_eq_order_zero_add_sum_tail]
  omega

end BONG

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete order-sequence suffix is the lattice volume order. -/
theorem orderSequence_suffixSum_zero_eq_volumeOrder
    (b : GoodBONG q L n) :
    b.orderSequence.suffixSum 0 = Lattice.volumeOrder q L := by
  rw [b.orderSequence.suffixSum_eq_sum_Ico 0 (by omega),
    Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range,
    b.toBONG.volumeOrder_eq_sum_order]
  apply Finset.sum_congr rfl
  intro i _
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt]
  exact b.orderSequence_at i.val i.isLt

/-- Removing the first order from the volume gives the suffix sum beginning
at index one. -/
theorem orderSequence_suffixSum_one_eq_volumeOrder_sub
    (b : GoodBONG q L (n + 1)) :
    b.orderSequence.suffixSum 1 =
      Lattice.volumeOrder q L - b.order 0 := by
  have hsplit := b.orderSequence.suffixSum_succ 0 (by omega)
  rw [b.orderSequence_suffixSum_zero_eq_volumeOrder,
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega),
    b.orderSequence_at 0 (by omega)] at hsplit
  have hindex : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hindex] at hsplit
  have hsplit' : Lattice.volumeOrder q L =
      b.order 0 + b.orderSequence.suffixSum 1 := by
    simpa only [Nat.zero_add] using hsplit
  omega

/-- The suffix beginning at one is the sum of the orders in the projected
tail. -/
theorem orderSequence_suffixSum_one_eq_sum_tail_order
    (b : GoodBONG q L (n + 1)) :
    b.orderSequence.suffixSum 1 = ∑ i, b.toBONG.tail.order i := by
  rw [b.orderSequence_suffixSum_one_eq_volumeOrder_sub,
    b.toBONG.sum_tail_order_eq_volumeOrder_sub_order_zero]
  rfl

end BONG.GoodBONG

end Bong
