/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIITypes

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the overlapping type-II/III branch

When type III also has central source gap one, the paper treats it as type
II.  The `Lemma67Classification` representation keeps adjacent transitions
in the type-III constructor, so this file proves the required type-II prefix
class directly from the adjacent profile.  It does not coerce the data to the
strictly-long `Lemma67TypeII` structure.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the overlapping type-II/III branch, the target prefix through the
last unequal coordinate has the type-II congruence class. -/
theorem beli2019Lemma72_typeIII_overlap_target_last_succ
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    Int.ModEq 2
      (b.orderSequence.prefixSum (D.outer.last + 1))
      (((D.outer.last + 1 : Nat) : Int) *
          b.orderSequence.entryOrZero D.outer.transition.lastZero + 1) := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero left
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n + 2 := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hrightBound : right < n + 2 := by omega
  have hlastBound := D.outer.lastDifference.bound
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hrightEven := D.outer.right_even_distance
  have htargetZero : b.orderSequence.entryOrZero 0 = T := by
    have hzero := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
    have hleft := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
    simpa only [T, left] using hzero.trans hleft.symm
  have htargetBefore (k : Nat) (hk : k < right) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) T := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := left) (k := k) (by omega) hleftBound
      (Nat.zero_le _) (by omega) (by omega) hleftEven htargetZero
    simpa only [T, htargetZero] using hmod
  let center : Fin (n + 1) := ⟨left, by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega⟩
  have hgapFormula : a.orderGap center =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    congr 1
    · apply congrArg a.order
      apply Fin.ext
      simp only [center, Fin.val_succ]
      exact hrightEq.symm
  have hoverlap' : a.orderGap center = 1 := by
    simpa only [center, left] using hoverlap
  have hsourceStep : a.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero left + 1 := by
    rw [hgapFormula] at hoverlap'
    omega
  have htargetRight : b.orderSequence.entryOrZero right = T + 1 := by
    have hleftBoundary : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using D.outer.transition.leftBoundary
    have hrightBoundary : b.orderSequence.entryOrZero right =
        a.orderSequence.entryOrZero right + 1 := by
      simpa only [right] using D.outer.transition.rightBoundary
    simp only [T]
    omega
  have htargetLast : b.orderSequence.entryOrZero D.outer.last =
      b.orderSequence.entryOrZero right := by
    have h := D.outer.target_rightEven_eq_boundary
      D.outer.last D.outer.right_le_last le_rfl hrightEven
    simpa only [right] using h
  have htargetAfter (k : Nat) (hrightK : right ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) (T + 1) := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := right) (j := D.outer.last) (k := k)
      hrightBound hlastBound hrightK hk (hk.trans_lt hlastBound)
      hrightEven htargetLast.symm
    simpa only [htargetRight, T] using hmod
  have hbase : Int.ModEq 2 (b.orderSequence.prefixSum right)
      ((right : Int) * T) := by
    apply b.orderSequence.prefixSum_modEq_mul T right
    intro k hk
    exact htargetBefore k hk
  have hrightLastSucc : right ≤ D.outer.last + 1 := by
    have hrightLast := D.outer.right_le_last
    omega
  have hsum := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    ((right : Int) * T) (T + 1) hrightLastSucc hbase (by
      intro k hkRight hkLast
      exact htargetAfter k hkRight (by omega))
  have hformula :
      (right : Int) * T +
          ((D.outer.last + 1 - right : Nat) : Int) * (T + 1) =
        ((D.outer.last + 1 : Nat) : Int) * T +
          ((D.outer.last + 1 - right : Nat) : Int) := by
    rw [Nat.cast_sub hrightLastSucc]
    ring
  have hdistanceOdd : Odd
      (((D.outer.last + 1 - right : Nat) : Int)) := by
    rcases hrightEven with ⟨d, hd⟩
    refine ⟨(d : Int), ?_⟩
    have hrightLast : right ≤ D.outer.last := by
      simpa only [right] using D.outer.right_le_last
    have hdistance : D.outer.last + 1 - right = 2 * d + 1 := by
      simp only [right] at hd hrightLast ⊢
      omega
    exact_mod_cast hdistance
  have hdistanceMod : Int.ModEq 2
      (((D.outer.last + 1 - right : Nat) : Int)) 1 :=
    modEq_two_one_of_odd hdistanceOdd
  rw [hformula] at hsum
  have hfinal := hsum.trans (Int.ModEq.rfl.add hdistanceMod)
  simpa only [T, right] using hfinal

/-- The type-II reference in an overlapping type-III profile is no larger
than the first order of the comparison BONG. -/
theorem beli2019Lemma79_typeIII_overlap_reference_le_thirdFirst
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.orderSequence.entryOrZero D.outer.transition.lastZero ≤
      c.orderSequence.entryOrZero 0 := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hleftValue := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
  omega

/-- In the overlapping branch, the target value at the final unequal
coordinate is one above the target value at the left transition. -/
theorem beli2019Lemma79_typeIII_overlap_lastTarget_eq_left_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    b.orderSequence.entryOrZero D.outer.last =
      b.orderSequence.entryOrZero D.outer.transition.lastZero + 1 := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let center : Fin (n + 1) := ⟨left, by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega⟩
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega
  have hrightBound : right < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    omega
  have hgapFormula : a.orderGap center =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [center, Fin.val_succ]
    exact hrightEq.symm
  have hoverlap' : a.orderGap center = 1 := by
    simpa only [center, left] using hoverlap
  have hsourceStep : a.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero left + 1 := by
    rw [hgapFormula] at hoverlap'
    omega
  have hleftBoundary : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hrightBoundary : b.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [right] using D.outer.transition.rightBoundary
  have htargetRight : b.orderSequence.entryOrZero right =
      b.orderSequence.entryOrZero left + 1 := by omega
  have htargetLast := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl D.outer.right_even_distance
  simpa only [right, left] using htargetLast.trans htargetRight

end BONG.GoodBONG

end Bong
