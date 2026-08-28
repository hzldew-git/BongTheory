/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightPivot

/-!
# Beli (2019), Lemma 6.9(i): arithmetic on the type-I right tail

On every odd position strictly after the canonical right switch, the source
order is one above the target order, while at the following even position the
target order is one above the source order.  Pair summation then shows that
the target prefix at the maximal right pivot has order exactly one above the
source prefix.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Exact alternating source-target order shifts on the odd type-I right
tail. -/
theorem lemma69_typeI_rightOdd_orders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (j : Nat) (hright : C.rightSwitch < j)
    (hlast : j < D.profile.last) (hodd : Odd j) :
    a.orderSequence.entryOrZero j =
        b.orderSequence.entryOrZero j + 1 ∧
      b.orderSequence.entryOrZero (j + 1) =
        a.orderSequence.entryOrZero (j + 1) + 1 := by
  have hlastBound := D.profile.lastDifference.bound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hjOneEven : Even (j + 1) := by
    rcases hodd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hjOneDistance : Even (j + 1 - D.anchor) := by
    rcases hjOneEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have htargetNext := C.target_from_anchor (j + 1) (by
      have hanchorRight := C.anchor_le_right
      omega)
    (by omega) hjOneDistance
  have hsourceNext := C.source_after_right (j + 1) (by omega)
    (by omega) hjOneDistance
  have hpairParity : Even (j - (D.anchor + 1)) := by
    rcases hodd with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hpair := D.profile.rightPairEq j (by
      have hanchorRight := C.anchor_le_right
      omega)
    (by omega) hpairParity
  have hanchorGap := D.anchor_gap
  constructor <;> omega

/-- At the maximal odd right pivot, the target prefix order is the source
prefix order plus one. -/
theorem lemma69_i_typeI_rightPivot_prefixSum
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma69TypeIRightPivotData a b D C) :
    b.orderSequence.prefixSum (P.pivot + 1) =
      a.orderSequence.prefixSum (P.pivot + 1) + 1 := by
  have hlastBound := D.profile.lastDifference.bound
  have hpivotLast := P.pivot_le_last_previous
  have hpivotLtLast : P.pivot < D.profile.last := by
    rcases P.pivot_odd with ⟨d, hd⟩
    omega
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hpivotOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst P.pivot (by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega)
    hpivotLtLast P.pivot_odd
  have hpivotDistance : Even (P.pivot - (D.anchor + 1)) := by
    rcases P.pivot_odd with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega⟩
  rcases hpivotDistance with ⟨pairs, hpairs⟩
  have hprefixAnchor :
      b.orderSequence.prefixSum (D.anchor + 1) =
        a.orderSequence.prefixSum (D.anchor + 1) + 2 := by
    calc
      b.orderSequence.prefixSum (D.anchor + 1) =
          b.orderSequence.prefixSum D.anchor +
            b.orderSequence.entryOrZero D.anchor := by
        simpa only using b.orderSequence.prefixSum_succ D.anchor
      _ = a.orderSequence.prefixSum D.anchor +
          (a.orderSequence.entryOrZero D.anchor + 2) := by
        rw [D.profile.prefix_eq, D.anchor_gap]
      _ = (a.orderSequence.prefixSum D.anchor +
          a.orderSequence.entryOrZero D.anchor) + 2 := by ring
      _ = a.orderSequence.prefixSum (D.anchor + 1) + 2 := by
        rw [a.orderSequence.prefixSum_succ]
  have hprefixPairs (t : Nat) (ht : t ≤ pairs) :
      b.orderSequence.prefixSum (D.anchor + 1 + 2 * t) =
        a.orderSequence.prefixSum (D.anchor + 1 + 2 * t) + 2 := by
    induction t with
    | zero => simpa using hprefixAnchor
    | succ t ih =>
        have ht' : t ≤ pairs := by omega
        have hcurrent : D.anchor + 1 + 2 * t + 2 ≤ P.pivot := by
          omega
        have hpair := D.profile.rightPairEq
          (D.anchor + 1 + 2 * t) (by omega) (by omega)
          ⟨t, by omega⟩
        rw [show D.anchor + 1 + 2 * (t + 1) =
            D.anchor + 1 + 2 * t + 2 by ring,
          a.orderSequence.prefixSum_add_two,
          b.orderSequence.prefixSum_add_two, ih ht', hpair]
        ring
  have hprefixPivot :
      b.orderSequence.prefixSum P.pivot =
        a.orderSequence.prefixSum P.pivot + 2 := by
    have hanchorPivot : D.anchor + 1 ≤ P.pivot := by
      have hanchorRight := C.anchor_le_right
      have hnextPivot := P.next_le_pivot
      omega
    have hpivotEq : D.anchor + 1 + 2 * pairs = P.pivot := by
      omega
    simpa only [hpivotEq] using hprefixPairs pairs le_rfl
  rw [a.orderSequence.prefixSum_succ,
    b.orderSequence.prefixSum_succ, hprefixPivot]
  omega

end BONG.GoodBONG

end Bong
