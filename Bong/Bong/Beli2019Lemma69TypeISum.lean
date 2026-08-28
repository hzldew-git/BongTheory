/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019WeightSegmentSum

/-!
# Beli (2019), Lemma 6.9(v): the type-I block sum

Inside the canonical type-I interval, target orders are two larger at even
positions and two smaller at odd positions.  Hence every adjacent order sum,
and therefore the corresponding segment of the `W`-sequence, is unchanged.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type v} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- At every even position in the canonical type-I interval, the target
order is exactly two larger than the source order. -/
theorem lemma69_v_typeI_even_entry_gap_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) (hright : k ≤ C.rightSwitch) :
    b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero k + 2 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  by_cases hkAnchor : k ≤ D.anchor
  · have ha := C.source_to_anchor k hkAnchor hkEven
    have hb := C.target_from_left k hleft hkAnchor hkEven
    omega
  · have hanchorK : D.anchor ≤ k :=
      Nat.le_of_lt (lt_of_not_ge hkAnchor)
    have hdistance : Even (k - D.anchor) := by
      rcases hkEven with ⟨d, hd⟩
      rcases hanchorEven with ⟨e, he⟩
      exact ⟨d - e, by omega⟩
    have ha := C.source_to_right k hanchorK hright hdistance
    have hb := C.target_from_anchor k hanchorK
      (hright.trans C.right_le_last) hdistance
    have hgapAnchor := D.anchor_gap
    omega

/-- At every odd position in the canonical type-I interval, the source
order is exactly two larger than the target order. -/
theorem lemma69_v_typeI_odd_entry_gap_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat) (hkOdd : Odd k)
    (hleft : C.leftSwitch ≤ k) (hright : k ≤ C.rightSwitch) :
    a.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero k + 2 := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  rcases hkOdd with ⟨d, hd⟩
  by_cases hkAnchor : k < D.anchor
  · have hleftEven := C.left_even
    rcases hleftEven with ⟨e, he⟩
    have hkPos : 0 < k := by omega
    have hleftPrevious : C.leftSwitch ≤ k - 1 := by omega
    have hpreviousEven : Even (k - 1) := ⟨d, by omega⟩
    have hpreviousGap := lemma69_v_typeI_even_entry_gap_two
      a b D C hfirst (k - 1) hpreviousEven hleftPrevious (by omega)
    have hpairParity : Even (D.anchor - (k - 1)) := by
      rcases hanchorEven with ⟨f, hf⟩
      exact ⟨f - d, by omega⟩
    have hpair := D.profile.leftPairEq (k - 1) (by omega) hpairParity
    have hone : k - 1 + 1 = k := by omega
    rw [hone] at hpair
    omega
  · have hrightEven := C.right_even
    rcases hrightEven with ⟨e, he⟩
    have hanchorK : D.anchor < k := by
      rcases hanchorEven with ⟨f, hf⟩
      omega
    have hnextEven : Even (k + 1) := ⟨d + 1, by omega⟩
    have hnextRight : k + 1 ≤ C.rightSwitch := by omega
    have hnextGap := lemma69_v_typeI_even_entry_gap_two
      a b D C hfirst (k + 1) hnextEven (by omega) hnextRight
    have hpairParity : Even (k - (D.anchor + 1)) := by
      rcases hanchorEven with ⟨f, hf⟩
      exact ⟨d - f, by omega⟩
    have hpair := D.profile.rightPairEq k (by omega) (by
      have hrightLast := C.right_le_last
      have hlastBound := D.profile.lastDifference.bound
      omega) hpairParity
    omega

/-- Adjacent source and target order sums agree throughout the canonical
type-I interval. -/
theorem lemma69_v_typeI_adjacent_entry_sum_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (k : Nat)
    (hleft : C.leftSwitch ≤ k) (hright : k < C.rightSwitch) :
    a.orderSequence.entryOrZero k +
        a.orderSequence.entryOrZero (k + 1) =
      b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) := by
  rcases Nat.even_or_odd k with hkEven | hkOdd
  · have hkOneOdd : Odd (k + 1) := by
      rcases hkEven with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hkGap := lemma69_v_typeI_even_entry_gap_two
      a b D C hfirst k hkEven hleft hright.le
    have hkOneGap := lemma69_v_typeI_odd_entry_gap_two
      a b D C hfirst (k + 1) hkOneOdd (by omega) (by omega)
    omega
  · have hkOneEven : Even (k + 1) := by
      rcases hkOdd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hkGap := lemma69_v_typeI_odd_entry_gap_two
      a b D C hfirst k hkOdd hleft hright.le
    have hkOneGap := lemma69_v_typeI_even_entry_gap_two
      a b D C hfirst (k + 1) hkOneEven (by omega) (by omega)
    omega

/-- The paired `W`-segment over the canonical type-I interval has the same
sum for source and target. -/
theorem lemma69_v_typeI_weightSegmentSum_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) :
    a.weightSequence.segmentSum (2 * C.leftSwitch)
        (2 * C.rightSwitch) =
      b.weightSequence.segmentSum (2 * C.leftSwitch)
        (2 * C.rightSwitch) := by
  have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
    C.left_le_anchor.trans C.anchor_le_right
  have hrightBound : C.rightSwitch ≤ n + 1 := by
    have hrightLast := C.right_le_last
    have hlastBound := D.profile.lastDifference.bound
    omega
  apply a.weightSegmentSum_eq_of_adjacentOrderSums b
    C.leftSwitch C.rightSwitch hleftRight hrightBound
  intro k hkLeft hkRight
  have hsum := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst k hkLeft hkRight
  have hkBound : k < n + 2 := by omega
  have hkOneBound : k + 1 < n + 2 := by omega
  rw [a.orderSequence_entryOrZero_eq_order ⟨k, hkBound⟩,
    a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkOneBound⟩,
    b.orderSequence_entryOrZero_eq_order ⟨k, hkBound⟩,
    b.orderSequence_entryOrZero_eq_order ⟨k + 1, hkOneBound⟩] at hsum
  exact_mod_cast hsum

/-- Lemma 7.7's type-I middle branch after eliminating the block-sum
hypothesis from the interval-rigidity argument. -/
theorem beli2019Lemma77_typeI_of_weightBoundaries
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hW : BeliOrderLE a.weightSequence b.weightSequence)
    (hleftBoundary :
      a.weightSequence.entryOrZero (2 * C.leftSwitch) ≤
        b.weightSequence.entryOrZero (2 * C.leftSwitch))
    (hrightBoundary :
      a.weightSequence.entryOrZero (2 * C.rightSwitch - 1) ≤
        b.weightSequence.entryOrZero (2 * C.rightSwitch - 1))
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hiEven : Even i) (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 < C.rightSwitch) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  apply a.beli2019Lemma77_typeI_of_weightInterval b D C hfirst hW
    hleftBoundary hrightBoundary
  · exact lemma69_v_typeI_weightSegmentSum_eq a b D C hfirst
  · exact hiTwo
  · exact hiBound
  · exact hiEven
  · exact hleft
  · exact hright

end BONG.GoodBONG

end Bong
