/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma611TypeI

/-!
# Beli (2019), Lemma 7.2(i)

Summing the four parity blocks of Lemma 6.11(i) gives the cumulative-order
formulas.  The left switch is even, so its correction vanishes modulo two;
the right switch is even, so the one-based right switch contributes `-1`.
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

/-- The four cumulative-order congruences in Lemma 7.2(i). -/
structure Lemma72TypeIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) where
  leftSwitch : Nat
  rightSwitch : Nat
  left_even : Even leftSwitch
  right_even : Even rightSwitch
  right_le_last : rightSwitch ≤ D.profile.last
  target_before (i : Nat) (hi : i < leftSwitch + 1) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) * (a.orderSequence.entryOrZero D.anchor + 1))
  target_after (i : Nat) (hleft : leftSwitch + 1 ≤ i)
      (hi : i ≤ D.profile.last + 1) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) * (a.orderSequence.entryOrZero D.anchor + 2))
  source_before (i : Nat) (hi : i ≤ rightSwitch + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) * a.orderSequence.entryOrZero D.anchor)
  source_after (i : Nat) (hright : rightSwitch + 1 ≤ i)
      (hi : i ≤ D.profile.last + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) * (a.orderSequence.entryOrZero D.anchor + 1) - 1)

/-- Beli (2019), Lemma 7.2(i), with paper indices represented by prefix
lengths. -/
theorem beli2019Lemma72_i
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0) :
    Nonempty (Lemma72TypeIConsequences a b D) := by
  rcases a.lemma611TypeI b D hfirst with ⟨C⟩
  let left := C.leftSwitch
  let right := C.rightSwitch
  let R := a.orderSequence.entryOrZero D.anchor
  have hleftZero : Int.ModEq 2 (left : Int) 0 := by
    rcases C.left_even with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have hrightOne : Int.ModEq 2 ((right + 1 : Nat) : Int) 1 := by
    rcases C.right_even with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have htargetBefore (i : Nat) (hi : i < left + 1) :
      Int.ModEq 2 (b.orderSequence.prefixSum i)
        ((i : Int) * (R + 1)) := by
    apply b.orderSequence.prefixSum_modEq_mul (R + 1) i
    intro k hk
    exact C.target_before k (by omega)
  have hsourceBefore (i : Nat) (hi : i ≤ right + 1) :
      Int.ModEq 2 (a.orderSequence.prefixSum i)
        ((i : Int) * R) := by
    apply a.orderSequence.prefixSum_modEq_mul R i
    intro k hk
    exact C.source_before k (by omega)
  refine ⟨{
    leftSwitch := left
    rightSwitch := right
    left_even := C.left_even
    right_even := C.right_even
    right_le_last := C.right_le_last
    target_before := ?_
    target_after := ?_
    source_before := ?_
    source_after := ?_ }⟩
  · intro i hi
    simpa only [R, left] using htargetBefore i (by
      simpa only [left] using hi)
  · intro i hleftI hi
    have hleftI' : left ≤ i := by omega
    have hbase := htargetBefore left (by omega)
    have hsum := b.orderSequence.prefixSum_modEq_add_mul_of_tail
      ((left : Int) * (R + 1)) (R + 2) hleftI' hbase (by
        intro k hkLeft hkI
        exact C.target_after k hkLeft (by omega))
    have hformula :
        (left : Int) * (R + 1) +
            ((i - left : Nat) : Int) * (R + 2) =
          (i : Int) * (R + 2) - (left : Int) := by
      rw [Nat.cast_sub hleftI']
      ring
    have hcorrection : Int.ModEq 2
        ((i : Int) * (R + 2) - (left : Int))
        ((i : Int) * (R + 2)) := by
      simpa only [sub_zero] using (Int.ModEq.rfl.sub hleftZero)
    have hbridge : Int.ModEq 2
        ((left : Int) * (R + 1) +
          ((i - left : Nat) : Int) * (R + 2))
        ((i : Int) * (R + 2)) := by
      rw [hformula]
      exact hcorrection
    have hfinal := hsum.trans hbridge
    simpa only [R, left] using hfinal
  · intro i hi
    simpa only [R, right] using hsourceBefore i (by
      simpa only [right] using hi)
  · intro i hrightI hi
    have hbase := hsourceBefore (right + 1) le_rfl
    have hsum := a.orderSequence.prefixSum_modEq_add_mul_of_tail
      (((right + 1 : Nat) : Int) * R) (R + 1) hrightI hbase (by
        intro k hkRight hkI
        exact C.source_after k (by omega) (by omega))
    have hformula :
        ((right + 1 : Nat) : Int) * R +
            ((i - (right + 1) : Nat) : Int) * (R + 1) =
          (i : Int) * (R + 1) - ((right + 1 : Nat) : Int) := by
      rw [Nat.cast_sub hrightI]
      ring
    have hcorrection : Int.ModEq 2
        ((i : Int) * (R + 1) - ((right + 1 : Nat) : Int))
        ((i : Int) * (R + 1) - 1) :=
      Int.ModEq.rfl.sub hrightOne
    have hbridge : Int.ModEq 2
        (((right + 1 : Nat) : Int) * R +
          ((i - (right + 1) : Nat) : Int) * (R + 1))
        ((i : Int) * (R + 1) - 1) := by
      rw [hformula]
      exact hcorrection
    have hfinal := hsum.trans hbridge
    simpa only [R, right] using hfinal

end BONG.GoodBONG

end Bong
