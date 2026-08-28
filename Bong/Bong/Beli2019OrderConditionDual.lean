/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DefectConditionDual
import Bong.Bong.Beli2019SequenceDual
import Bong.Bong.Beli2019OrderSumRigidity
import Bong.Bong.Beli2019Lemma67Transitions

/-!
# Beli (2019): reverse-duality of the order condition

Reversing and negating an order sequence turns a prefix into the negative
of the complementary suffix.  Consequently, after swapping source and
target, condition 2.1(i), the total order gap, and every prefix gap are
transported to the complementary boundary.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The full sum changes sign under reversal and negation. -/
theorem reverseNegate_prefixSum_rank {n : Nat}
    (x : BeliOrderSequence n Gamma) :
    x.reverseNegate.prefixSum n = -x.prefixSum n := by
  unfold prefixSum
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin n, x.reverseNegate.entryOrZero i) =
        ∑ i : Fin n, -x.value (Fin.rev i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [entryOrZero_of_lt x.reverseNegate i.isLt]
      rfl
    _ = ∑ i : Fin n, -x.value i := by
      change (∑ i : Fin n,
        (fun j : Fin n ↦ -x.value j) (Fin.revPerm i)) =
          ∑ i : Fin n, -x.value i
      exact Equiv.sum_comp Fin.revPerm
        (fun j : Fin n ↦ -x.value j)
    _ = -(∑ i : Fin n, x.value i) := by
      simpa only [Finset.sum_neg_distrib]
    _ = -(∑ i : Fin n, x.entryOrZero i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [entryOrZero_of_lt x i.isLt]
      rfl

/-- A reversed-negated prefix is the negative complementary suffix. -/
theorem reverseNegate_prefixSum_eq_neg_suffixLengthSum {n : Nat}
    (x : BeliOrderSequence n Gamma) (k : Nat) (hk : k ≤ n) :
    x.reverseNegate.prefixSum k = -x.suffixLengthSum k := by
  revert hk
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _
      simp
  | one =>
      intro hk
      have hn : 0 < n := by omega
      rw [x.reverseNegate.prefixSum_one,
        x.suffixLengthSum_one hn,
        entryOrZero_of_lt x.reverseNegate hn,
        entryOrZero_of_lt x (by omega)]
      congr 2
  | more k ih _ =>
      intro hk
      have hk0 : k < n := by omega
      have hk1 : k + 1 < n := by omega
      have hleft : n - (k + 2) < n := by omega
      have hright : n - (k + 2) + 1 < n := by omega
      rw [x.reverseNegate.prefixSum_add_two,
        x.suffixLengthSum_add_two k hk, ih (by omega),
        entryOrZero_of_lt x.reverseNegate hk0,
        entryOrZero_of_lt x.reverseNegate hk1,
        entryOrZero_of_lt x hleft,
        entryOrZero_of_lt x hright]
      have hrev0 : Fin.rev (⟨k, hk0⟩ : Fin n) =
          (⟨n - (k + 2) + 1, hright⟩ : Fin n) := by
        apply Fin.ext
        simp
        omega
      have hrev1 : Fin.rev (⟨k + 1, hk1⟩ : Fin n) =
          (⟨n - (k + 2), hleft⟩ : Fin n) := by
        apply Fin.ext
        simp
      change -x.suffixLengthSum k +
          (-x.value (Fin.rev ⟨k, hk0⟩) +
            -x.value (Fin.rev ⟨k + 1, hk1⟩)) =
        -(x.value ⟨n - (k + 2), hleft⟩ +
          x.value ⟨n - (k + 2) + 1, hright⟩ +
            x.suffixLengthSum k)
      rw [hrev0, hrev1]
      abel

/-- Prefix gaps are reflected around the total gap two. -/
theorem prefixGap_reverseNegate_swap {n : Nat}
    (x y : BeliOrderSequence n Int)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (k : Nat) (hk : k ≤ n) :
    y.reverseNegate.prefixGap x.reverseNegate k =
      2 - x.prefixGap y (n - k) := by
  unfold prefixGap
  rw [x.reverseNegate_prefixSum_eq_neg_suffixLengthSum k hk,
    y.reverseNegate_prefixSum_eq_neg_suffixLengthSum k hk]
  unfold suffixLengthSum
  omega

end BeliOrderSequence

namespace BONG.GoodBONG

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Explicit reversed order identities identify the whole order sequence. -/
theorem orderSequence_eq_reverseNegate_of_orders
    (a : GoodBONG q L (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j)) :
    aDual.orderSequence = a.orderSequence.reverseNegate := by
  apply BeliOrderSequence.ext
  funext j
  exact haOrders j

/-- Condition 2.1(i) is transported to a swapped reverse-dual pair. -/
theorem representationOrderCondition_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (horder : a.RepresentationOrderCondition b le_rfl) :
    bDual.RepresentationOrderCondition aDual le_rfl := by
  have haSequence := a.orderSequence_eq_reverseNegate_of_orders
    aDual haOrders
  have hbSequence := b.orderSequence_eq_reverseNegate_of_orders
    bDual hbOrders
  rw [bDual.representationOrderCondition_iff aDual le_rfl,
    hbSequence, haSequence,
    BeliOrderLE.reverseNegate_le_reverseNegate_iff]
  exact (a.representationOrderCondition_iff b le_rfl).mp horder

/-- A total order gap two reverses to the same gap after swapping. -/
theorem totalOrderSum_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1)) :
    bDual.orderSequence.prefixSum (n + 1) + 2 =
      aDual.orderSequence.prefixSum (n + 1) := by
  rw [a.orderSequence_eq_reverseNegate_of_orders aDual haOrders,
    b.orderSequence_eq_reverseNegate_of_orders bDual hbOrders,
    a.orderSequence.reverseNegate_prefixSum_rank,
    b.orderSequence.reverseNegate_prefixSum_rank]
  omega

/-- Every prefix gap of a swapped reverse-dual pair is complementary. -/
theorem orderPrefixGap_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (htotal : a.orderSequence.prefixSum (n + 1) + 2 =
      b.orderSequence.prefixSum (n + 1))
    (k : Nat) (hk : k ≤ n + 1) :
    bDual.orderSequence.prefixGap aDual.orderSequence k =
      2 - a.orderSequence.prefixGap b.orderSequence (n + 1 - k) := by
  rw [a.orderSequence_eq_reverseNegate_of_orders aDual haOrders,
    b.orderSequence_eq_reverseNegate_of_orders bDual hbOrders]
  exact BeliOrderSequence.prefixGap_reverseNegate_swap
    a.orderSequence b.orderSequence htotal k hk

end BONG.GoodBONG

end Bong
