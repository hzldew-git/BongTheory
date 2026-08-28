/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftOrders
import Bong.Bong.Beli2019Lemma69TypeIRightArithmetic
import Bong.Bong.Beli2019Lemma79NormOrder

/-!
# Beli (2019), Lemma 7.9(i): the elementary type-I outer classes

Before the canonical left switch, the even target orders are one above the
first source order.  Strict inclusion of norm ideals therefore gives the
direct comparison with the third BONG.  At every nonexceptional odd left
coordinate, and at every odd coordinate after the right switch, the current
target order is below the source order while the following adjacent sums
agree.  The old order condition then transports formally.

The sole left coordinate not covered here is the predecessor of the left
switch; its following even entry already belongs to the gap-two block and is
the exceptional point isolated in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The direct alternative of condition 2.1(i) at every even coordinate
strictly before the canonical type-I left switch. -/
theorem beli2019Lemma79_i_typeI_leftEven
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkEven : Even k)
    (hleft : k < C.leftSwitch) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have htarget := C.target_before_left k hleft hkEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hthirdMonotone := c.orderSequence.entryOrZero_le_of_evenGap
    0 k (Nat.zero_le k) hk hkEven
  left
  rw [← b.orderSequence.entryOrZero_of_lt hk,
    ← c.orderSequence.entryOrZero_of_lt hk]
  omega

/-- The adjacent-pair alternative at every odd left coordinate whose
successor is still strictly before the canonical left switch. -/
theorem beli2019Lemma79_i_typeI_leftOdd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hk : k < n + 2) (hkOdd : Odd k)
    (hleft : k + 1 < C.leftSwitch) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have hkOneEven : Even (k + 1) := by
    rcases hkOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst (k + 1) (by
      rcases hkOdd with ⟨d, hd⟩
      omega) hleft.le hkOneEven
  have hsourceNext := C.source_to_anchor (k + 1)
    (hleft.le.trans C.left_le_anchor) hkOneEven
  have htargetNext := C.target_before_left (k + 1) hleft hkOneEven
  have hcurrent : b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero k := by
    have hcurrentEq := horders.2.2
    rw [show k + 1 - 1 = k by omega] at hcurrentEq
    omega
  have hpair : b.orderSequence.entryOrZero k +
      b.orderSequence.entryOrZero (k + 1) ≤
        a.orderSequence.entryOrZero k +
          a.orderSequence.entryOrZero (k + 1) := by
    have hcurrentEq := horders.2.2
    rw [show k + 1 - 1 = k by omega] at hcurrentEq
    omega
  exact BeliOrderLE.compare_of_source_bounds
    hacSequence k hk hcurrent hpair

/-- The adjacent-pair alternative at every odd type-I coordinate strictly
after the right switch and before the last unequal coordinate. -/
theorem beli2019Lemma79_i_typeI_rightOdd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hk : k < n + 2) (hkOdd : Odd k)
    (hright : C.rightSwitch < k) (hlast : k < D.profile.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst k hright hlast hkOdd
  have hcurrent : b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero k := by
    omega
  have hpair : b.orderSequence.entryOrZero k +
      b.orderSequence.entryOrZero (k + 1) ≤
        a.orderSequence.entryOrZero k +
          a.orderSequence.entryOrZero (k + 1) := by
    omega
  exact BeliOrderLE.compare_of_source_bounds
    hacSequence k hk hcurrent hpair

end BONG.GoodBONG

end Bong
