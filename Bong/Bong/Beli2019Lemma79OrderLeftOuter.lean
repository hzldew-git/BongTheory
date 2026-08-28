/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79NormOrder

/-!
# Beli (2019), Lemma 7.9(i): the complete left outer interval

Before the left no-gap transition, even target entries equal the first
source order plus one.  At odd entries the source is one above the target,
and the next adjacent source and target sums agree.  These two alternatives
transport condition 2.1(i) throughout the left outer interval.
-/

namespace Bong

namespace BeliOrderLE.NoGapTwoOuterConsequences

variable {n : Nat}
  {x y : BeliOrderSequence n Int}

/-- Every even source entry through the left transition equals the first
source entry. -/
theorem source_leftEven_eq_first
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (k : Nat) (hk : k ≤ O.transition.lastZero) (heven : Even k) :
    x.entryOrZero k = x.entryOrZero 0 := by
  by_cases heq : O.first = O.transition.lastZero
  · have hkZero : k = 0 := by omega
    subst k
    rfl
  · have hlt : O.first < O.transition.lastZero :=
      lt_of_le_of_ne O.first_le_left heq
    have hp := O.leftProfile hlt
    have hvalue := hp.2.2 k (by omega) hk (by
      simpa only [hfirst, Nat.sub_zero] using heven)
    simpa only [hfirst] using hvalue

/-- At the first differing coordinate the target is exactly one above the
source in the no-gap-two branch. -/
theorem target_first_eq_source_add_one
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2) :
    y.entryOrZero 0 = x.entryOrZero 0 + 1 := by
  by_cases heq : O.first = O.transition.lastZero
  · have hleftZero : O.transition.lastZero = 0 := by omega
    simpa only [hleftZero] using O.transition.leftBoundary
  · have hlt : O.first < O.transition.lastZero :=
      lt_of_le_of_ne O.first_le_left heq
    have hlower : x.entryOrZero 0 < y.entryOrZero 0 := by
      simpa only [hfirst] using (O.leftProfile hlt).2.1
    have hbound : 0 < n := by
      simpa only [hfirst] using O.firstDifference.bound
    have hupper := hnoTwo 0 hbound
    omega

/-- Every even target entry through the left transition is exactly one
above the first source order. -/
theorem target_leftEven_eq_first_add_one
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hk : k ≤ O.transition.lastZero) (heven : Even k) :
    y.entryOrZero k = x.entryOrZero 0 + 1 := by
  have hkBound : k < n := by
    have hfirstTwoBound := O.transition.firstTwo_le_rank
    have hseparated := O.transition.separated
    omega
  have hsource := O.source_leftEven_eq_first hfirst k hk heven
  have hfirstValue := O.target_first_eq_source_add_one hfirst hnoTwo
  have hmono := y.entryOrZero_le_of_evenGap 0 k
    (Nat.zero_le k) hkBound heven
  have hupper := hnoTwo k hkBound
  omega

/-- At every odd entry strictly before the left transition, the source is
one above the target. -/
theorem source_leftOdd_eq_target_add_one
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hk : k < O.transition.lastZero) (hodd : Odd k) :
    x.entryOrZero k = y.entryOrZero k + 1 := by
  rcases hodd with ⟨d, hd⟩
  have hpreviousEven : Even (k - 1) := ⟨d, by omega⟩
  have hleftEven := O.left_even_of_first_eq_zero hfirst
  rcases hleftEven with ⟨e, he⟩
  have hpairParity : Even (O.transition.lastZero - (k - 1)) :=
    ⟨e - d, by omega⟩
  have hpair := O.leftPairEq (k - 1) (by omega) hpairParity
  have hsourcePrevious := O.source_leftEven_eq_first
    hfirst (k - 1) (by omega) hpreviousEven
  have htargetPrevious := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (k - 1) (by omega) hpreviousEven
  rw [show k - 1 + 1 = k by omega] at hpair
  omega

/-- Source and target adjacent sums agree at every odd entry strictly before
the left transition. -/
theorem leftOdd_pair_eq
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hk : k < O.transition.lastZero) (hodd : Odd k) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) := by
  rcases hodd with ⟨d, hd⟩
  have hnextEven : Even (k + 1) := ⟨d + 1, by omega⟩
  have hcurrent := O.source_leftOdd_eq_target_add_one
    hfirst hnoTwo k hk ⟨d, hd⟩
  have hsourceNext := O.source_leftEven_eq_first
    hfirst (k + 1) (by omega) hnextEven
  have htargetNext := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (k + 1) (by omega) hnextEven
  omega

end BeliOrderLE.NoGapTwoOuterConsequences

namespace BeliOrderLE

/-- Condition 2.1(i) transports through the complete left outer interval
of a no-gap-two profile. -/
theorem compare_leftOuter {n : Nat}
    {x y z : BeliOrderSequence n Int} (hxz : BeliOrderLE x z)
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (hfirstLower : x.entryOrZero 0 + 1 ≤ z.entryOrZero 0)
    (k : Nat) (hk : k < n) (hleft : k ≤ O.transition.lastZero) :
    y.entry k hk ≤ z.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n),
        y.entry k hk + y.entry (k + 1) hkNext ≤
          z.entry (k - 1) (by omega) + z.entry k hk := by
  rcases Nat.even_or_odd k with heven | hodd
  · left
    have hy := O.target_leftEven_eq_first_add_one
      hfirst hnoTwo k hleft heven
    have hz := z.entryOrZero_le_of_evenGap 0 k
      (Nat.zero_le k) hk heven
    rw [← y.entryOrZero_of_lt hk, ← z.entryOrZero_of_lt hk]
    omega
  · have hleftStrict : k < O.transition.lastZero := by
      rcases hodd with ⟨d, hd⟩
      rcases O.left_even_of_first_eq_zero hfirst with ⟨e, he⟩
      omega
    have hcurrentEq := O.source_leftOdd_eq_target_add_one
      hfirst hnoTwo k hleftStrict hodd
    have hpairEq := O.leftOdd_pair_eq
      hfirst hnoTwo k hleftStrict hodd
    apply compare_of_source_bounds hxz k hk
    · omega
    · exact le_of_eq hpairEq.symm

end BeliOrderLE

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Parts 1 and 5 of Lemma 7.9(i) on the complete type-II left outer
interval, directly from the paper's strict norm-ideal hypothesis. -/
theorem beli2019Lemma79_i_typeII_leftOuter
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2)
    (hleft : k ≤ D.outer.transition.lastZero) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
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
  exact BeliOrderLE.compare_leftOuter hacSequence D.outer hfirst
    D.no_gap_two hfirstLower k hk hleft

/-- Parts 1 and 6 of Lemma 7.9(i) on the complete type-III left outer
interval, directly from the paper's strict norm-ideal hypothesis. -/
theorem beli2019Lemma79_i_typeIII_leftOuter
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2)
    (hleft : k ≤ D.outer.transition.lastZero) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
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
  exact BeliOrderLE.compare_leftOuter hacSequence D.outer hfirst
    D.no_gap_two hfirstLower k hk hleft

end BONG.GoodBONG

end Bong
