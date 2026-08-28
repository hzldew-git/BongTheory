/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeII
import Bong.Bong.Beli2019Lemma79OrderLeftOuter
import Bong.Bong.Beli2019Lemma79OrderRightAlternating

/-!
# Beli (2019), Lemma 7.2(ii): overlapping type-II/III profiles

A type-III profile whose central source gap is one has exactly the four
cumulative-order congruences of type II.  The classification datatype retains
the adjacent profile in its type-III constructor, so these consequences are
proved directly rather than by constructing an impossible strictly-long
`Lemma67TypeII` witness.
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

/-- The four type-II prefix congruences carried by a central-gap-one
type-III profile. -/
structure Lemma72TypeIIIOverlapConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) : Prop where
  target_before (i : Nat) (hi : i < D.outer.transition.firstTwo) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) *
        b.orderSequence.entryOrZero D.outer.transition.lastZero)
  target_after (i : Nat)
      (hfirst : D.outer.transition.firstTwo ≤ i)
      (hi : i ≤ D.outer.last + 1) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) *
          (b.orderSequence.entryOrZero D.outer.transition.lastZero + 1) +
        ((D.outer.transition.firstTwo - 1 : Nat) : Int))
  source_before (i : Nat)
      (hi : i ≤ D.outer.transition.lastZero + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) *
        (b.orderSequence.entryOrZero D.outer.transition.lastZero - 1))
  source_after (i : Nat)
      (hlast : D.outer.transition.lastZero + 1 ≤ i)
      (hi : i ≤ D.outer.last + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) *
        b.orderSequence.entryOrZero D.outer.transition.lastZero - 1)

/-- The overlapping branch of Lemma 7.2(ii). -/
theorem beli2019Lemma72_ii_typeIII_overlap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1) :
    Lemma72TypeIIIOverlapConsequences a b D := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero left
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
  have hleftBound : left < n + 1 := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hleftGapBound : left < n := by
    simp only [left]
    rw [D.adjacent] at hfirstTwoBound
    omega
  have hrightBound : right < n + 1 := by omega
  have hlastBound := D.outer.lastDifference.bound
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hrightEven := D.outer.right_even_distance
  have hsourceZero : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left := by
    have hzero := D.outer.source_leftEven_eq_first
      hfirst 0 (Nat.zero_le _) ⟨0, by omega⟩
    have hleft := D.outer.source_leftEven_eq_first
      hfirst D.outer.transition.lastZero le_rfl hleftEven
    simpa only [left] using hzero.trans hleft.symm
  have htargetZero : b.orderSequence.entryOrZero 0 = T := by
    have hzero := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
    have hleft := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
    simpa only [T, left] using hzero.trans hleft.symm
  have hleftBoundary : T = a.orderSequence.entryOrZero left + 1 := by
    simpa only [T, left] using D.outer.transition.leftBoundary
  let center : Fin n := ⟨left, hleftGapBound⟩
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
  have hsourceRight : a.orderSequence.entryOrZero right = T := by
    rw [hgapFormula] at hoverlap'
    omega
  have htargetRight : b.orderSequence.entryOrZero right = T + 1 := by
    have hrightBoundary : b.orderSequence.entryOrZero right =
        a.orderSequence.entryOrZero right + 1 := by
      simpa only [right] using D.outer.transition.rightBoundary
    omega
  have hsourceLast : a.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero right := by
    have h := D.outer.source_rightEven_eq_boundary D.no_gap_two
      D.outer.last D.outer.right_le_last le_rfl hrightEven
    simpa only [right] using h
  have htargetLast : b.orderSequence.entryOrZero D.outer.last =
      b.orderSequence.entryOrZero right := by
    have h := D.outer.target_rightEven_eq_boundary
      D.outer.last D.outer.right_le_last le_rfl hrightEven
    simpa only [right] using h
  have hsourceBeforeEntry (k : Nat) (hk : k ≤ left) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k) (T - 1) := by
    have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := left) (k := k) (by omega) hleftBound
      (Nat.zero_le _) hk (hk.trans_lt hleftBound) hleftEven hsourceZero
    have hleftValue : a.orderSequence.entryOrZero left = T - 1 := by
      omega
    simpa only [hsourceZero, hleftValue] using hmod
  have htargetBeforeEntry (k : Nat) (hk : k ≤ left) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) T := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := left) (k := k) (by omega) hleftBound
      (Nat.zero_le _) hk (hk.trans_lt hleftBound) hleftEven htargetZero
    simpa only [T, htargetZero] using hmod
  have hsourceAfterEntry (k : Nat) (hrightK : right ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k) T := by
    have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
      (i := right) (j := D.outer.last) (k := k)
      hrightBound hlastBound hrightK hk (hk.trans_lt hlastBound)
      hrightEven hsourceLast.symm
    simpa only [hsourceRight, T] using hmod
  have htargetAfterEntry (k : Nat) (hrightK : right ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) (T + 1) := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := right) (j := D.outer.last) (k := k)
      hrightBound hlastBound hrightK hk (hk.trans_lt hlastBound)
      hrightEven htargetLast.symm
    simpa only [htargetRight, T] using hmod
  have hleftOne : Int.ModEq 2 ((left + 1 : Nat) : Int) 1 := by
    rcases hleftEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have hnegRight : Int.ModEq 2 (-((right : Nat) : Int))
      ((right : Nat) : Int) := by
    rw [Int.modEq_iff_dvd]
    exact ⟨(right : Int), by ring⟩
  have htargetBefore (i : Nat)
      (hi : i < D.outer.transition.firstTwo) :
      Int.ModEq 2 (b.orderSequence.prefixSum i) ((i : Int) * T) := by
    apply b.orderSequence.prefixSum_modEq_mul T i
    intro k hk
    exact htargetBeforeEntry k (by
      simp only [left]
      rw [D.adjacent] at hi
      omega)
  have hsourceBefore (i : Nat) (hi : i ≤ left + 1) :
      Int.ModEq 2 (a.orderSequence.prefixSum i)
        ((i : Int) * (T - 1)) := by
    apply a.orderSequence.prefixSum_modEq_mul (T - 1) i
    intro k hk
    exact hsourceBeforeEntry k (by omega)
  refine {
    target_before := ?_
    target_after := ?_
    source_before := ?_
    source_after := ?_ }
  · intro i hi
    simpa only [T, left] using htargetBefore i hi
  · intro i hfirstI hi
    have hrightI : right ≤ i := by
      simp only [right]
      omega
    have hbase : Int.ModEq 2 (b.orderSequence.prefixSum right)
        ((right : Int) * T) := by
      apply htargetBefore right
      simp only [right]
      omega
    have hsum := b.orderSequence.prefixSum_modEq_add_mul_of_tail
      ((right : Int) * T) (T + 1) hrightI hbase (by
        intro k hkRight hkI
        exact htargetAfterEntry k hkRight (by omega))
    have hformula :
        (right : Int) * T + ((i - right : Nat) : Int) * (T + 1) =
          (i : Int) * (T + 1) - (right : Int) := by
      rw [Nat.cast_sub hrightI]
      ring
    have hcorrection : Int.ModEq 2
        ((i : Int) * (T + 1) - (right : Int))
        ((i : Int) * (T + 1) + (right : Int)) := by
      simpa only [sub_eq_add_neg] using
        (Int.ModEq.rfl.add hnegRight)
    have hbridge : Int.ModEq 2
        ((right : Int) * T + ((i - right : Nat) : Int) * (T + 1))
        ((i : Int) * (T + 1) + (right : Int)) := by
      rw [hformula]
      exact hcorrection
    have hfinal := hsum.trans hbridge
    simpa only [T, left, right] using hfinal
  · intro i hi
    simpa only [T, left] using hsourceBefore i (by
      simpa only [left] using hi)
  · intro i hleftI hi
    have hbase := hsourceBefore (left + 1) le_rfl
    have hsum := a.orderSequence.prefixSum_modEq_add_mul_of_tail
      (((left + 1 : Nat) : Int) * (T - 1)) T hleftI hbase (by
        intro k hkLeft hkI
        exact hsourceAfterEntry k (by simpa only [hrightEq] using hkLeft)
          (by omega))
    have hformula :
        ((left + 1 : Nat) : Int) * (T - 1) +
            ((i - (left + 1) : Nat) : Int) * T =
          (i : Int) * T - ((left + 1 : Nat) : Int) := by
      rw [Nat.cast_sub hleftI]
      ring
    have hcorrection : Int.ModEq 2
        ((i : Int) * T - ((left + 1 : Nat) : Int))
        ((i : Int) * T - 1) :=
      Int.ModEq.rfl.sub hleftOne
    have hbridge : Int.ModEq 2
        (((left + 1 : Nat) : Int) * (T - 1) +
          ((i - (left + 1) : Nat) : Int) * T)
        ((i : Int) * T - 1) := by
      rw [hformula]
      exact hcorrection
    have hfinal := hsum.trans hbridge
    simpa only [T, left] using hfinal

end BONG.GoodBONG

end Bong
