/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716OrderCondition

/-!
# Beli (2019), Lemma 7.16: exceptional order-failure profiles

This module formalizes the arithmetic claim in the proof of condition
2.1(i).  Failure at any remaining exceptional coordinate forces the rigid
alternating comparison profile printed in the paper.  The later geometric
argument rules out precisely these profiles.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Two-step monotonicity in a form using actual finite indices. -/
theorem lemma716_order_le_of_evenGap
    (c : GoodBONG q N (n + 3)) (i j : Fin (n + 3))
    (hij : i.val ≤ j.val) (heven : Even (j.val - i.val)) :
    c.order i ≤ c.order j := by
  have h := c.orderSequence.entryOrZero_le_of_evenGap
    i.val j.val hij j.isLt heven
  rw [c.orderSequence_entryOrZero_eq_order i,
    c.orderSequence_entryOrZero_eq_order j] at h
  exact h

/-- The rigid comparison prefix forced by a type-I exceptional failure. -/
structure Beli2019Lemma716TypeIFailureProfile
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsRank : s ≤ n + 3) : Prop where
  first : c.order 0 = R + 1
  high : c.order ⟨s - 2, by omega⟩ = R + 1
  low (hs : 2 < s) :
    c.order ⟨s - 3, by omega⟩ =
      R - 2 * (ramificationIndex K : Int) + 1

/-- The rigid comparison prefix forced by the type-II exceptional failure. -/
structure Beli2019Lemma716TypeIIFailureProfile
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsInterior : s < n + 3) : Prop where
  first : c.order 0 = R + 1
  high : c.order ⟨s - 2, by omega⟩ = R + 1
  low : c.order ⟨s - 1, by omega⟩ =
    R - 2 * (ramificationIndex K : Int) + 1

/-- Failure of type-I condition 2.1(i) at paper index `s - 1` forces the
claimed comparison order profile. -/
theorem lemma716_typeI_left_failureProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hfail : ¬Beli2019Lemma716OrderClause b c
      ⟨s - 2, by
        have := D.le_rank
        omega⟩) :
    Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank := by
  let left : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  have hfailLeft : ¬Beli2019Lemma716OrderClause b c left := by
    simpa only [left] using hfail
  have hleftEven : Even left.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [left]; omega⟩
  have hleftTarget : b.order left = R + 2 := by
    simpa only [left] using
      lemma716_typeI_leftBoundary_order_eq a b R s D hfirst hvalues
  have hleftLt : c.order left < b.order left := by
    apply lt_of_not_ge
    intro h
    exact hfailLeft (Or.inl h)
  have hzeroLower := lemma716_comparison_order_zero_ge
    a c R hfirst hnorm
  have hzeroLeft := lemma716_order_le_of_evenGap c
    (0 : Fin (n + 3)) left (Nat.zero_le _) hleftEven
  have hleftEq : c.order left = R + 1 := by omega
  have hzeroEq : c.order 0 = R + 1 := by omega
  refine {
    first := hzeroEq
    high := by simpa only [left] using hleftEq
    low := ?_ }
  intro hs
  have hsFour : 4 ≤ s := by
    rcases D.even with ⟨d, hd⟩
    omega
  let highPrevious : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  let right : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  have hhighPreviousEven : Even highPrevious.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by simp only [highPrevious]; omega⟩
  have hzeroHighPrevious := lemma716_order_le_of_evenGap c
    (0 : Fin (n + 3)) highPrevious (Nat.zero_le _) hhighPreviousEven
  have hhighPreviousLeftEven : Even (left.val - highPrevious.val) := by
    exact ⟨1, by simp only [left, highPrevious]; omega⟩
  have hhighPreviousLeft := lemma716_order_le_of_evenGap c
    highPrevious left (by simp only [left, highPrevious]; omega)
      hhighPreviousLeftEven
  have hhighPreviousEq : c.order highPrevious = R + 1 := by omega
  have hrightTarget : b.order right =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [right] using
      lemma716_typeI_rightBoundary_order_eq a b R s D hsecond hvalues
  have hpairLt : c.order low + c.order left <
      b.order left + b.order right := by
    apply lt_of_not_ge
    intro hpair
    apply hfailLeft
    right
    have hi0 : 0 < left.val := by simp only [left]; omega
    have hiLarge : left.val + 1 < n + 3 := by
      simp only [left]
      have := D.le_rank
      omega
    refine ⟨hi0, hiLarge, ?_⟩
    have hnext : (⟨left.val + 1, hiLarge⟩ : Fin (n + 3)) = right := by
      apply Fin.ext
      simp only [left, right]
      omega
    have hprevious : (⟨left.val - 1, by omega⟩ : Fin (n + 3)) = low := by
      apply Fin.ext
      simp only [left, low]
      omega
    simpa only [hnext, hprevious] using hpair
  let gap : Fin (n + 2) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap =
      c.order low - c.order highPrevious := by
    unfold orderGap
    have hsucc : gap.succ = low := by
      apply Fin.ext
      simp [gap, low]
      omega
    have hcastSucc : gap.castSucc = highPrevious := by
      apply Fin.ext
      simp [gap, highPrevious]
    rw [hsucc, hcastSucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  have hgapNegative : c.orderGap gap < 0 := by
    rw [hgapDef]
    rw [hhighPreviousEq]
    rw [hleftEq, hleftTarget, hrightTarget] at hpairLt
    have he := ramificationIndex_pos (K := K)
    omega
  have hgapEven := c.orderGap_even_of_negative gap hgapNegative
  rw [hgapDef] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  rw [hleftEq, hleftTarget, hrightTarget] at hpairLt
  have he := ramificationIndex_pos (K := K)
  have hlowEq : c.order low =
      R - 2 * (ramificationIndex K : Int) + 1 := by omega
  simpa only [low] using hlowEq

/-- Failure of type-I condition 2.1(i) at paper index `s` forces the same
claimed comparison order profile. -/
theorem lemma716_typeI_right_failureProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hfail : ¬Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩) :
    Beli2019Lemma716TypeIFailureProfile c R s D.two_le D.le_rank := by
  let left : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let right : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  have hfailRight : ¬Beli2019Lemma716OrderClause b c right := by
    simpa only [right] using hfail
  have hrightOdd : Odd right.val := by
    have hsTwo := D.two_le
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [right]; omega⟩
  have hleftEven : Even left.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [left]; omega⟩
  have hrightTarget : b.order right =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [right] using
      lemma716_typeI_rightBoundary_order_eq a b R s D hsecond hvalues
  have hrightLt : c.order right < b.order right := by
    apply lt_of_not_ge
    intro h
    exact hfailRight (Or.inl h)
  have hrightLower := lemma716_comparison_odd_order_ge
    a c R hfirst hnorm right hrightOdd
  have hrightEq : c.order right =
      R - 2 * (ramificationIndex K : Int) + 1 := by omega
  let gap : Fin (n + 2) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  have hgapDef : c.orderGap gap = c.order right - c.order left := by
    unfold orderGap
    have hsucc : gap.succ = right := by
      apply Fin.ext
      change s - 2 + 1 = s - 1
      have := D.two_le
      omega
    have hcastSucc : gap.castSucc = left := by
      apply Fin.ext
      simp [gap, left]
    rw [hsucc, hcastSucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  have hleftLower := lemma716_comparison_even_order_ge
    a c R hfirst hnorm left hleftEven
  have hleftEq : c.order left = R + 1 := by omega
  have hzeroLower := lemma716_comparison_order_zero_ge
    a c R hfirst hnorm
  have hzeroLeft := lemma716_order_le_of_evenGap c
    (0 : Fin (n + 3)) left (Nat.zero_le _) hleftEven
  have hzeroEq : c.order 0 = R + 1 := by omega
  refine {
    first := hzeroEq
    high := by simpa only [left] using hleftEq
    low := ?_ }
  intro hs
  let low : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  have hlowOdd : Odd low.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 2, by simp only [low]; omega⟩
  have hlowRightEven : Even (right.val - low.val) := by
    exact ⟨1, by simp only [right, low]; omega⟩
  have hlowRight := lemma716_order_le_of_evenGap c low right
    (by simp only [right, low]; omega) hlowRightEven
  have hlowLower := lemma716_comparison_odd_order_ge
    a c R hfirst hnorm low hlowOdd
  have hlowEq : c.order low =
      R - 2 * (ramificationIndex K : Int) + 1 := by omega
  simpa only [low] using hlowEq

variable [DyadicDiscriminantClassLaws K]

/-- Failure of the unique type-II exceptional clause forces the alternating
profile stated in the paper. -/
theorem lemma716_typeII_failureProfile
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η j)
    (hfail : ¬Beli2019Lemma716OrderClause b c
      ⟨s - 1, by
        have := D.le_rank
        omega⟩) :
    Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII) := by
  let left : Fin (n + 3) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  let right : Fin (n + 3) := ⟨s - 1, by
    have := D.le_rank
    omega⟩
  let tail : Fin (n + 3) := ⟨s, Classical.choose hII⟩
  have hsInterior : s < n + 3 := Classical.choose hII
  have hfailRight : ¬Beli2019Lemma716OrderClause b c right := by
    simpa only [right] using hfail
  have hleftEven : Even left.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by simp only [left]; omega⟩
  have hrightTarget : b.order right =
      R - 2 * (ramificationIndex K : Int) + 3 := by
    simpa only [right] using lemma716_typeII_rightBoundary_order_eq
      a b R s D hII ε η hεUnit hηUnit hvalues
  have htailTarget : b.order tail = R + 1 := by
    simpa only [tail] using lemma716_typeII_tailBoundary_order_eq
      a b R s D hII ε η hεUnit hηUnit hvalues
  have hrightLt : c.order right < b.order right := by
    apply lt_of_not_ge
    intro h
    exact hfailRight (Or.inl h)
  have hpairLt : c.order left + c.order right <
      b.order right + b.order tail := by
    apply lt_of_not_ge
    intro hpair
    apply hfailRight
    right
    have hi0 : 0 < right.val := by
      change 0 < s - 1
      have := D.two_le
      omega
    have hiLarge : right.val + 1 < n + 3 := by
      change s - 1 + 1 < n + 3
      omega
    refine ⟨hi0, hiLarge, ?_⟩
    have hnext : (⟨right.val + 1, hiLarge⟩ : Fin (n + 3)) = tail := by
      apply Fin.ext
      change s - 1 + 1 = s
      have := D.two_le
      omega
    have hprevious : (⟨right.val - 1, by omega⟩ : Fin (n + 3)) = left := by
      apply Fin.ext
      simp only [right, left]
      omega
    simpa only [hnext, hprevious] using hpair
  have hleftLower := lemma716_comparison_even_order_ge
    a c R hfirst hnorm left hleftEven
  let gap : Fin (n + 2) := ⟨s - 2, by
    omega⟩
  have hgapDef : c.orderGap gap = c.order right - c.order left := by
    unfold orderGap
    have hsucc : gap.succ = right := by
      apply Fin.ext
      change s - 2 + 1 = s - 1
      have := D.two_le
      omega
    have hcastSucc : gap.castSucc = left := by
      apply Fin.ext
      simp [gap, left]
    rw [hsucc, hcastSucc]
  have hgapLower := c.orderGap_ge_neg_two_mul_e gap
  rw [hgapDef] at hgapLower
  have hleftEq : c.order left = R + 1 := by
    rw [hrightTarget, htailTarget] at hpairLt
    omega
  have hzeroLower := lemma716_comparison_order_zero_ge
    a c R hfirst hnorm
  have hzeroLeft := lemma716_order_le_of_evenGap c
    (0 : Fin (n + 3)) left (Nat.zero_le _) hleftEven
  have hzeroEq : c.order 0 = R + 1 := by omega
  have hgapNegative : c.orderGap gap < 0 := by
    rw [hgapDef]
    rw [hleftEq]
    rw [hrightTarget] at hrightLt
    have he := ramificationIndex_pos (K := K)
    omega
  have hgapEven := c.orderGap_even_of_negative gap hgapNegative
  rw [hgapDef] at hgapEven
  rcases hgapEven with ⟨z, hz⟩
  rw [hleftEq] at hgapLower hz
  rw [hrightTarget] at hrightLt
  have hrightEq : c.order right =
      R - 2 * (ramificationIndex K : Int) + 1 := by omega
  exact {
    first := hzeroEq
    high := by simpa only [left] using hleftEq
    low := by simpa only [right] using hrightEq }

end BONG.GoodBONG

end Bong
