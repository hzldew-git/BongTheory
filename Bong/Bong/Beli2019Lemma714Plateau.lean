/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019), Lemma 7.14(i)

The minimal even endpoint in Lemma 7.14 forces an alternating plateau.  This
file isolates the exact minimality predicate and proves the two constant
parity chains using only good-BONG two-step monotonicity and the universal
adjacent-gap lower bound.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The part of the minimality of the paper's even integer `s` used in
Lemma 7.14(i).  For every earlier even `t`, the order at `t+2` has not yet
crossed the defining threshold. -/
structure Lemma714MinimalityData
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat) : Prop where
  even : Even s
  two_le : 2 ≤ s
  le_rank : s ≤ n + 3
  before (t : Nat) (htTwo : 2 ≤ t) (hts : t < s) (htEven : Even t)
      (htBound : t + 2 ≤ n + 3) :
    b.order ⟨t + 1, by omega⟩ ≤
      R - 2 * (ramificationIndex K : Int) + 1

/-- The alternating order plateau asserted in Lemma 7.14(i).  Odd
zero-based positions are the paper's even positions and conversely. -/
structure Lemma714PlateauConsequences
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsBound : s ≤ n + 3) : Prop where
  low_positions (k : Nat) (hkThree : 3 ≤ k) (hks : k ≤ s - 1)
      (hkOdd : Odd k) :
    b.order ⟨k, by omega⟩ =
      R - 2 * (ramificationIndex K : Int) + 1
  high_positions (k : Nat) (hkTwo : 2 ≤ k) (hks : k ≤ s - 2)
      (hkEven : Even k) :
    b.order ⟨k, by omega⟩ = R + 1

/-- Beli (2019), Lemma 7.14(i), in zero-based indexing. -/
theorem beli2019Lemma714_i
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714MinimalityData b R s) (hsFour : 4 ≤ s)
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩) :
    Lemma714PlateauConsequences b R s D.le_rank := by
  have hsBound : s ≤ n + 3 := D.le_rank
  have htwoBound : 2 < n + 3 := by omega
  have hthreeBound : 3 < n + 3 := by omega
  have hmono (x y : Nat) (hx : x < n + 3) (hy : y < n + 3)
      (hxy : x ≤ y) (heven : Even (y - x)) :
      b.order ⟨x, hx⟩ ≤ b.order ⟨y, hy⟩ := by
    have h := b.orderSequence.entryOrZero_le_of_evenGap
      x y hxy hy heven
    rw [b.orderSequence_entryOrZero_eq_order ⟨x, hx⟩,
      b.orderSequence_entryOrZero_eq_order ⟨y, hy⟩] at h
    exact h
  have hterminal : b.order ⟨s - 1, by omega⟩ ≤
      R - 2 * (ramificationIndex K : Int) + 1 := by
    have h := D.before (s - 2) (by omega) (by omega) (by
      rcases D.even with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩) (by omega)
    simpa only [show s - 2 + 1 = s - 1 by omega] using h
  have hthirdGap := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    ⟨2, htwoBound⟩ hthreeBound
  have hfourthLower :
      R - 2 * (ramificationIndex K : Int) + 1 ≤
        b.order ⟨3, by omega⟩ := by
    change -(2 * (ramificationIndex K : Int)) ≤
      b.order ⟨3, by omega⟩ - b.order ⟨2, by omega⟩ at hthirdGap
    omega
  have hlow (k : Nat) (hkThree : 3 ≤ k) (hks : k ≤ s - 1)
      (hkOdd : Odd k) :
      b.order ⟨k, by omega⟩ =
        R - 2 * (ramificationIndex K : Int) + 1 := by
    have hthreeK : Even (k - 3) := by
      rcases hkOdd with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hkTerminal : Even ((s - 1) - k) := by
      rcases D.even with ⟨d, hd⟩
      rcases hkOdd with ⟨e, he⟩
      exact ⟨d - e - 1, by omega⟩
    have hleft := hmono 3 k (by omega) (by omega)
      hkThree hthreeK
    have hright := hmono k (s - 1) (by omega) (by omega)
      hks hkTerminal
    omega
  refine {
    low_positions := hlow
    high_positions := ?_ }
  intro k hkTwo hks hkEven
  have htwoK : Even (k - 2) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hleft := hmono 2 k (by omega) (by omega) hkTwo htwoK
  have hnextOdd : Odd (k + 1) := by
    rcases hkEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnext := hlow (k + 1) (by omega) (by omega) hnextOdd
  have hkBound : k < n + 3 := by omega
  have hnextBound : k + 1 < n + 3 := by omega
  have hgap := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    ⟨k, hkBound⟩ hnextBound
  change -(2 * (ramificationIndex K : Int)) ≤
    b.order ⟨k + 1, by omega⟩ - b.order ⟨k, by omega⟩ at hgap
  omega

end BONG.GoodBONG

end Bong
