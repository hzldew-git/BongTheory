/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72Arithmetic

/-!
# Beli (2019), Lemma 6.11: the type-II parity profile

In the application of Section 7 the first unequal index is zero.  The left
outer plateau therefore has even endpoint, while the right outer plateau has
the parity fixed by Lemma 6.7.  Lemma 6.6 turns equality of the relevant
endpoints into congruence of every intervening order.  The constant middle
interval from the type-II branch then joins the two outer profiles.
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

/-- A convenient zero-extended form of Lemma 6.6(i). -/
theorem entryOrZero_modEq_of_equal_even_endpoints
    (b : GoodBONG q L (n + 1)) {i j k : Nat}
    (hi : i < n + 1) (hj : j < n + 1)
    (hik : i ≤ k) (hkj : k ≤ j) (hk : k < n + 1)
    (hparity : Even (j - i))
    (heq : b.orderSequence.entryOrZero i =
      b.orderSequence.entryOrZero j) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero i) := by
  let iFin : Fin (n + 1) := ⟨i, hi⟩
  let jFin : Fin (n + 1) := ⟨j, hj⟩
  let kFin : Fin (n + 1) := ⟨k, hk⟩
  have heqOrder : b.order iFin = b.order jFin := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence hj] at heq
    change b.order iFin = b.order jFin
    exact heq
  have hdata := b.beli2019Lemma66_i iFin jFin
    (by change i ≤ j; omega) hparity heqOrder
  have hmod := hdata.order_modEq kFin
    (by change i ≤ k; exact hik) (by change k ≤ j; exact hkj)
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hk,
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi]
  change Int.ModEq 2 (b.order kFin) (b.order iFin)
  exact hmod

/-- The entrywise parity data from Lemma 6.11(ii), in the zero-based
coordinates of `Lemma67TypeII`. -/
structure Lemma611TypeIIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeII a b) : Prop where
  left_even : Even D.outer.transition.lastZero
  right_parity : Even
    (D.outer.last - (D.outer.transition.firstTwo - 1))
  source_before (k : Nat)
      (hk : k ≤ D.outer.transition.lastZero) :
    Int.ModEq 2 (a.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero D.outer.transition.lastZero - 1)
  source_after (k : Nat)
      (hlast : D.outer.transition.lastZero < k)
      (hk : k ≤ D.outer.last) :
    Int.ModEq 2 (a.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero D.outer.transition.lastZero)
  target_before (k : Nat)
      (hk : k < D.outer.transition.firstTwo - 1) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero D.outer.transition.lastZero)
  target_after (k : Nat)
      (hfirst : D.outer.transition.firstTwo - 1 ≤ k)
      (hk : k ≤ D.outer.last) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (b.orderSequence.entryOrZero D.outer.transition.lastZero + 1)

/-- Beli (2019), Lemma 6.11(ii), for the type-II data produced by Lemma
6.7 and with `s = 1` as in Section 7. -/
theorem lemma611TypeII
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0) :
    Lemma611TypeIIConsequences a b D := by
  have hfirstBound := D.outer.firstDifference.bound
  have hleftBound : D.outer.transition.lastZero < n + 1 := by
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    have hseparated := D.outer.transition.separated
    omega
  have hrightBound : D.outer.transition.firstTwo - 1 < n + 1 := by
    have hfirstTwoBound := D.outer.transition.firstTwo_le_rank
    omega
  have hlastBound := D.outer.lastDifference.bound
  have hleftEven : Even D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := (D.outer.leftProfile hlt).1
      simpa only [hfirst, Nat.sub_zero] using hp
  have hsourceLeft :
      a.orderSequence.entryOrZero D.outer.first =
        a.orderSequence.entryOrZero D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [heq]
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := D.outer.leftProfile hlt
      exact (hp.2.2 D.outer.transition.lastZero
        D.outer.first_le_left le_rfl hp.1).symm
  have htargetLeft :
      b.orderSequence.entryOrZero D.outer.first =
        b.orderSequence.entryOrZero D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [heq]
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      have hp := D.outer.leftProfile hlt
      have hupper := D.no_gap_two D.outer.first hfirstBound
      have hboundary := D.outer.transition.leftBoundary
      omega
  have hrightEven : Even
      (D.outer.last - (D.outer.transition.firstTwo - 1)) := by
    by_cases heq : D.outer.transition.firstTwo - 1 = D.outer.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.transition.firstTwo - 1 < D.outer.last :=
        lt_of_le_of_ne D.outer.right_le_last heq
      exact (D.outer.rightProfile hlt).1
  have htargetRight :
      b.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) =
        b.orderSequence.entryOrZero D.outer.last := by
    by_cases heq : D.outer.transition.firstTwo - 1 = D.outer.last
    · rw [heq]
    · have hlt : D.outer.transition.firstTwo - 1 < D.outer.last :=
        lt_of_le_of_ne D.outer.right_le_last heq
      have hp := D.outer.rightProfile hlt
      exact hp.2.2 (D.outer.transition.firstTwo - 1)
        le_rfl D.outer.right_le_last hp.1
  have hsourceRight :
      a.orderSequence.entryOrZero (D.outer.transition.firstTwo - 1) =
        a.orderSequence.entryOrZero D.outer.last := by
    by_cases heq : D.outer.transition.firstTwo - 1 = D.outer.last
    · rw [heq]
    · have hlt : D.outer.transition.firstTwo - 1 < D.outer.last :=
        lt_of_le_of_ne D.outer.right_le_last heq
      have hp := D.outer.rightProfile hlt
      have hupper := D.no_gap_two D.outer.last hlastBound
      have hboundary := D.outer.transition.rightBoundary
      omega
  have hsourceLeftZero :
      a.orderSequence.entryOrZero 0 =
        a.orderSequence.entryOrZero D.outer.transition.lastZero := by
    simpa only [hfirst] using hsourceLeft
  have htargetLeftZero :
      b.orderSequence.entryOrZero 0 =
        b.orderSequence.entryOrZero D.outer.transition.lastZero := by
    simpa only [hfirst] using htargetLeft
  have hsourceLeftMod (k : Nat)
      (hk : k ≤ D.outer.transition.lastZero) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k)
        (a.orderSequence.entryOrZero D.outer.transition.lastZero) := by
    have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := D.outer.transition.lastZero) (k := k)
      (by omega) hleftBound (Nat.zero_le k) hk (by omega)
      hleftEven hsourceLeftZero
    simpa only [hsourceLeftZero] using hmod
  have htargetLeftMod (k : Nat)
      (hk : k ≤ D.outer.transition.lastZero) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.orderSequence.entryOrZero D.outer.transition.lastZero) := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := D.outer.transition.lastZero) (k := k)
      (by omega) hleftBound (Nat.zero_le k) hk (by omega)
      hleftEven htargetLeftZero
    simpa only [htargetLeftZero] using hmod
  have hsourceRightMod (k : Nat)
      (hfirstK : D.outer.transition.firstTwo - 1 ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k)
        (a.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1)) := by
    exact a.entryOrZero_modEq_of_equal_even_endpoints
      (i := D.outer.transition.firstTwo - 1) (j := D.outer.last)
      (k := k) hrightBound hlastBound hfirstK hk
      (hk.trans_lt hlastBound) hrightEven hsourceRight
  have htargetRightMod (k : Nat)
      (hfirstK : D.outer.transition.firstTwo - 1 ≤ k)
      (hk : k ≤ D.outer.last) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k)
        (b.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1)) := by
    exact b.entryOrZero_modEq_of_equal_even_endpoints
      (i := D.outer.transition.firstTwo - 1) (j := D.outer.last)
      (k := k) hrightBound hlastBound hfirstK hk
      (hk.trans_lt hlastBound) hrightEven htargetRight
  refine {
    left_even := hleftEven
    right_parity := hrightEven
    source_before := ?_
    source_after := ?_
    target_before := ?_
    target_after := ?_ }
  · intro k hk
    have hmod := hsourceLeftMod k hk
    have hboundary := D.outer.transition.leftBoundary
    have heq :
        a.orderSequence.entryOrZero D.outer.transition.lastZero =
          b.orderSequence.entryOrZero D.outer.transition.lastZero - 1 := by
      omega
    simpa only [heq] using hmod
  · intro k hleftK hk
    by_cases hmiddle : k + 1 < D.outer.transition.firstTwo
    · rw [D.middle k hleftK hmiddle]
    · have hrightK : D.outer.transition.firstTwo - 1 ≤ k := by
        omega
      have hmod := hsourceRightMod k hrightK hk
      simpa only [D.right_source] using hmod
  · intro k hk
    by_cases hkLeft : k ≤ D.outer.transition.lastZero
    · exact htargetLeftMod k hkLeft
    · have hmiddle : k + 1 < D.outer.transition.firstTwo := by
        omega
      have hcommon := D.outer.transition.middle k (by omega) hmiddle
      have hvalue := D.middle k (by omega) hmiddle
      rw [← hcommon, hvalue]
  · intro k hrightK hk
    have hmod := htargetRightMod k hrightK hk
    simpa only [D.right_target] using hmod

end BONG.GoodBONG

end Bong
