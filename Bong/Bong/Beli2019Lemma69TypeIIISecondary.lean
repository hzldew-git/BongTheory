/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIII

/-!
# Beli (2019), Lemma 6.9(i): positivity of the type-III secondary shift

The proof of Lemma 6.9(i) shows that the optional secondary candidate at
the type-III transition has a strictly positive integral order coefficient.
This file exports that previously local calculation for use in Lemma 7.8.
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

/-- The integral coefficient of the optional secondary type-III candidate
is strictly positive under the normalization `s = 1`. -/
theorem lemma69_typeIII_secondaryCoefficient_pos
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hi : 1 < D.outer.transition.lastZero + 1 ∧
      D.outer.transition.lastZero + 1 + 1 < n + 1) :
    0 <
      a.order ⟨D.outer.transition.lastZero + 1, by omega⟩ +
        a.order ⟨D.outer.transition.lastZero + 1 + 1, hi.2⟩ -
        b.order ⟨D.outer.transition.lastZero + 1 - 2, by omega⟩ -
        b.order ⟨D.outer.transition.lastZero + 1 - 1, by omega⟩ := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hrightBound : right < n + 1 := by omega
  let idx : RepresentationIndex (n + 1) (n + 1) := {
    val := left + 1
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  have hidxVal : idx.val = left + 1 := rfl
  have hidxPred : idx.val - 1 = left := by
    rw [hidxVal]
    omega
  have hidxRight : idx.val = right := by
    rw [hidxVal, hrightEq]
  have hiIdx : 1 < idx.val ∧ idx.val + 1 < n + 1 := by
    simpa only [idx, left] using hi
  have hleftEven : Even left := by
    by_cases heq : D.outer.first = left
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < left :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, left, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hsourceEven (k : Nat) (hk : k ≤ left) (heven : Even k) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero left := by
    by_cases hzero : left = 0
    · have hkZero : k = 0 := by omega
      rw [hkZero, hzero]
    · have hlt : D.outer.first < left := by
        rw [hfirst]
        omega
      have hp := D.outer.leftProfile hlt
      have hkEq := hp.2.2 k (by rw [hfirst]; omega) hk (by
        simpa only [hfirst, Nat.sub_zero] using heven)
      have hleftEq := hp.2.2 left D.outer.first_le_left
        le_rfl hp.1
      exact hkEq.trans hleftEq.symm
  have hsourceZero : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left :=
    hsourceEven 0 (Nat.zero_le left) ⟨0, by omega⟩
  have htargetZero : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero left := by
    by_cases hzero : left = 0
    · rw [hzero]
    · have hlt : D.outer.first < left := by
        rw [hfirst]
        omega
      have hp := D.outer.leftProfile hlt
      have hupper := D.no_gap_two D.outer.first
        D.outer.firstDifference.bound
      rw [hfirst] at hupper
      have hfirstGap : b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero 0 + 1 := by
        have hstrict := hp.2.1
        rw [hfirst] at hstrict
        omega
      have hleftGap := D.outer.transition.leftBoundary
      have hleftGap' : b.orderSequence.entryOrZero left =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [left] using hleftGap
      omega
  have htargetEven (k : Nat) (hk : k ≤ left) (heven : Even k) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero left := by
    have hkBound : k < n + 1 :=
      hk.trans_lt hleftBound |>.trans (by omega)
    have hleftRank : left < n + 1 := hleftBound.trans (by omega)
    have hleftK : Even (left - k) := by
      rcases hleftEven with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hzeroK := b.orderSequence.entryOrZero_le_of_evenGap
      0 k (Nat.zero_le k) hkBound heven
    have hkLeft := b.orderSequence.entryOrZero_le_of_evenGap
      k left hk hleftRank hleftK
    omega
  have htargetNext_le_source :
      b.orderSequence.entryOrZero (left + 2) ≤
        a.orderSequence.entryOrZero (left + 2) := by
    have hnext : left + 2 < n + 1 := by
      simpa only [left] using hi.2
    by_cases hafter : D.outer.last < left + 2
    · exact (D.outer.lastDifference.after
        (left + 2) hafter hnext).symm.le
    · have hnextLast : left + 2 ≤ D.outer.last := by omega
      have hrightLast : right < D.outer.last := by omega
      have hp := D.outer.rightProfile hrightLast
      have hnextOneLast : left + 3 ≤ D.outer.last := by
        rcases hp.1 with ⟨d, hd⟩
        omega
      have hlastParity : Even (D.outer.last - (left + 3)) := by
        rcases hp.1 with ⟨d, hd⟩
        refine ⟨d - 1, ?_⟩
        omega
      have htargetSame :
          b.orderSequence.entryOrZero (left + 3) =
            b.orderSequence.entryOrZero D.outer.last := by
        exact hp.2.2 (left + 3) (by omega)
          hnextOneLast hlastParity
      have hsourceLe := a.orderSequence.entryOrZero_le_of_evenGap
        (left + 3) D.outer.last hnextOneLast
        D.outer.lastDifference.bound hlastParity
      have hpair := D.outer.rightPairEq (left + 2) (by
        have hadjacent := D.adjacent
        change D.outer.transition.firstTwo ≤
          D.outer.transition.lastZero + 2
        omega) (by
          have hlastBound := D.outer.lastDifference.bound
          omega) ⟨0, by omega⟩
      have hone : left + 2 + 1 = left + 3 := by omega
      rw [hone] at hpair
      have hlastStrict := hp.2.1
      omega
  have hleftTwo : 2 ≤ left := by
    rcases hleftEven with ⟨d, hd⟩
    simp only [idx] at hiIdx
    omega
  have hpairParity : Even (left - (left - 2)) := ⟨1, by omega⟩
  have hpair := D.outer.leftPairEq (left - 2) (by omega) hpairParity
  have hsourcePrev := hsourceEven (left - 2) (by omega) (by
    rcases hleftEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩)
  have htargetPrev := htargetEven (left - 2) (by omega) (by
    rcases hleftEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩)
  have htargetOdd :
      b.orderSequence.entryOrZero (left - 1) =
        a.orderSequence.entryOrZero (left - 1) - 1 := by
    have hone : left - 2 + 1 = left - 1 := by omega
    rw [hone] at hpair
    have hleftBoundary := D.outer.transition.leftBoundary
    have hleftBoundary' : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using hleftBoundary
    omega
  have hsourceOddLe := a.orderSequence.entryOrZero_le_of_evenGap
    (left - 1) right (by omega) hrightBound ⟨1, by omega⟩
  have htargetMonotone := b.orderSequence.entryOrZero_le_of_evenGap
    left (left + 2) (by omega) (by
      simpa only [idx] using hiIdx.2) ⟨1, by omega⟩
  have hcoefficient : 0 <
      a.orderSequence.entryOrZero right +
        a.orderSequence.entryOrZero (left + 2) -
        b.orderSequence.entryOrZero (left - 1) -
        b.orderSequence.entryOrZero left := by
    omega
  have hcoefficientOrder : 0 <
      a.order ⟨idx.val, idx.lt_large⟩ +
        a.order ⟨idx.val + 1, hiIdx.2⟩ -
        b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
    have haCurrent : a.order ⟨idx.val, idx.lt_large⟩ =
        a.orderSequence.entryOrZero idx.val :=
      (BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        idx.lt_large).symm
    have haNext : a.order ⟨idx.val + 1, hiIdx.2⟩ =
        a.orderSequence.entryOrZero (idx.val + 1) :=
      (BeliOrderSequence.entryOrZero_of_lt a.orderSequence hiIdx.2).symm
    have hbPrevious :
        b.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ =
          b.orderSequence.entryOrZero (idx.val - 2) :=
      (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (show idx.val - 2 < n + 1 by omega)).symm
    have hbCurrent :
        b.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ =
          b.orderSequence.entryOrZero (idx.val - 1) :=
      (BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (show idx.val - 1 < n + 1 by omega)).symm
    rw [haCurrent, haNext, hbPrevious, hbCurrent]
    have hidxNext : idx.val + 1 = left + 2 := by
      rw [hidxVal]
    have hidxPrevious : idx.val - 2 = left - 1 := by
      rw [hidxVal]
      omega
    rw [hidxNext, hidxPrevious, hidxPred, hidxRight]
    exact hcoefficient
  simpa only [idx, left] using hcoefficientOrder

end BONG.GoodBONG

end Bong
