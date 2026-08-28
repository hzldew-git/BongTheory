/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeII

/-!
# Beli (2019), Lemma 7.2(ii)

The type-II entrywise parity profile is summed on the two sides of each
transition.  The even zero-based left endpoint says that its one-based index
is odd, producing the paper's correction term `-1`.  At the right transition
the two occurrences of its zero-based index cancel modulo two.
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

/-- The four cumulative-order congruences in Lemma 7.2(ii), with paper
indices represented by prefix lengths. -/
structure Lemma72TypeIIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeII a b) : Prop where
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

/-- Beli (2019), Lemma 7.2(ii). -/
theorem beli2019Lemma72_ii
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0) :
    Lemma72TypeIIConsequences a b D := by
  let C := a.lemma611TypeII b D hfirst
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero left
  have hfirstTwoPos : 0 < D.outer.transition.firstTwo := by
    have hseparated := D.outer.transition.separated
    omega
  have hleftEven : Even left := by
    simpa only [left] using C.left_even
  have hleftOne : Int.ModEq 2 ((left + 1 : Nat) : Int) 1 := by
    rcases hleftEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have hnegRight : Int.ModEq 2 (-((right : Nat) : Int))
      ((right : Nat) : Int) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(right : Int), by ring⟩
  have htargetBefore (i : Nat)
      (hi : i < D.outer.transition.firstTwo) :
      Int.ModEq 2 (b.orderSequence.prefixSum i) ((i : Int) * T) := by
    apply b.orderSequence.prefixSum_modEq_mul T i
    intro k hk
    exact C.target_before k (by omega)
  have hsourceBefore (i : Nat) (hi : i ≤ left + 1) :
      Int.ModEq 2 (a.orderSequence.prefixSum i)
        ((i : Int) * (T - 1)) := by
    apply a.orderSequence.prefixSum_modEq_mul (T - 1) i
    intro k hk
    exact C.source_before k (by
      simp only [left] at hi ⊢
      omega)
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
        exact C.target_after k (by simpa only [right] using hkRight)
          (by omega))
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
        exact C.source_after k (by omega) (by omega))
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
