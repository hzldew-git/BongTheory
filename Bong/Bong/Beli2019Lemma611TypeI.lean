/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67TypeICanonical
import Bong.Bong.Beli2019Lemma611TypeII

/-!
# Beli (2019), Lemma 6.11: the type-I parity profile

The canonical type-I switches divide both order sequences into two parity
blocks.  Lemma 6.6 controls the long blocks.  The pair identities from
Lemma 6.7 control the single entry crossing each switch.
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

/-- The four entrywise congruence blocks in Lemma 6.11(i). -/
structure Lemma611TypeIConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) where
  leftSwitch : Nat
  rightSwitch : Nat
  left_even : Even leftSwitch
  right_even : Even rightSwitch
  left_le_right : leftSwitch ≤ rightSwitch
  right_le_last : rightSwitch ≤ D.profile.last
  target_before (k : Nat) (hk : k < leftSwitch) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (a.orderSequence.entryOrZero D.anchor + 1)
  target_after (k : Nat) (hleft : leftSwitch ≤ k)
      (hk : k ≤ D.profile.last) :
    Int.ModEq 2 (b.orderSequence.entryOrZero k)
      (a.orderSequence.entryOrZero D.anchor + 2)
  source_before (k : Nat) (hk : k ≤ rightSwitch) :
    Int.ModEq 2 (a.orderSequence.entryOrZero k)
      (a.orderSequence.entryOrZero D.anchor)
  source_after (k : Nat) (hright : rightSwitch < k)
      (hk : k ≤ D.profile.last) :
    Int.ModEq 2 (a.orderSequence.entryOrZero k)
      (a.orderSequence.entryOrZero D.anchor + 1)

/-- Beli (2019), Lemma 6.11(i), with the first unequal index equal to zero
as in Section 7. -/
theorem lemma611TypeI
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0) :
    Nonempty (Lemma611TypeIConsequences a b D) := by
  rcases a.lemma67TypeICanonicalData b D hfirst with ⟨C⟩
  let left := C.leftSwitch
  let right := C.rightSwitch
  let R := a.orderSequence.entryOrZero D.anchor
  have hlastBound := D.profile.lastDifference.bound
  have hleftBound : left < n + 1 := by
    exact C.left_le_anchor.trans_lt D.anchor_bound
  have hrightBound : right < n + 1 := by
    exact C.right_le_last.trans_lt hlastBound
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hrightDistance : Even (right - D.anchor) := by
    rcases C.right_even with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    refine ⟨d - e, ?_⟩
    have hanchorRight := C.anchor_le_right
    simp only [right] at hd hanchorRight ⊢
    omega
  have hlastDistance : Even (D.profile.last - D.anchor) := by
    by_cases heq : D.anchor = D.profile.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      exact (D.profile.rightProfile hlt).1
  have hlastEven : Even D.profile.last := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hlastDistance with ⟨e, he⟩
    refine ⟨d + e, ?_⟩
    have hanchorLast := D.profile.anchor_le_last
    omega
  have hleftLastEven : Even (D.profile.last - left) := by
    rcases hlastEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    refine ⟨d - e, ?_⟩
    have hleftLast := C.left_le_anchor.trans D.profile.anchor_le_last
    simp only [left] at he hleftLast ⊢
    omega
  have hsourceZero : a.orderSequence.entryOrZero 0 = R := by
    exact C.source_to_anchor 0 (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hsourceRight : a.orderSequence.entryOrZero right = R := by
    exact C.source_to_right right C.anchor_le_right le_rfl hrightDistance
  have hsourceBeforeMod (k : Nat) (hk : k ≤ right) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k) R := by
    have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
      (i := 0) (j := right) (k := k) (by omega) hrightBound
      (Nat.zero_le k) hk (hk.trans_lt hrightBound) (by
        simpa only [Nat.sub_zero] using C.right_even) (by
          rw [hsourceZero, hsourceRight])
    simpa only [hsourceZero] using hmod
  have htargetLeft : b.orderSequence.entryOrZero left = R + 2 := by
    exact C.target_from_left left le_rfl C.left_le_anchor C.left_even
  have htargetLast :
      b.orderSequence.entryOrZero D.profile.last = R + 2 := by
    calc
      b.orderSequence.entryOrZero D.profile.last =
          b.orderSequence.entryOrZero D.anchor :=
        C.target_from_anchor D.profile.last D.profile.anchor_le_last
          le_rfl hlastDistance
      _ = R + 2 := D.anchor_gap
  have htargetAfterMod (k : Nat) (hleft : left ≤ k)
      (hk : k ≤ D.profile.last) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) (R + 2) := by
    have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
      (i := left) (j := D.profile.last) (k := k) hleftBound
      hlastBound hleft hk (hk.trans_lt hlastBound) hleftLastEven (by
        rw [htargetLeft, htargetLast])
    simpa only [htargetLeft] using hmod
  have htargetBeforeMod (k : Nat) (hk : k < left) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) (R + 1) := by
    have hleftPos : 0 < left := by omega
    rcases C.left_even with ⟨d, hd⟩
    have hleftTwo : 2 ≤ left := by
      simp only [left] at hd hleftPos ⊢
      omega
    have hleftMinusEven : Even (left - 2) := by
      refine ⟨d - 1, ?_⟩
      simp only [left] at hd ⊢
      omega
    have htargetZero : b.orderSequence.entryOrZero 0 = R + 1 := by
      exact C.target_before_left 0 hleftPos ⟨0, by omega⟩
    have htargetEnd :
        b.orderSequence.entryOrZero (left - 2) = R + 1 := by
      exact C.target_before_left (left - 2) (by omega) hleftMinusEven
    by_cases hinterval : k ≤ left - 2
    · have hendBound : left - 2 < n + 1 := by omega
      have hmod := b.entryOrZero_modEq_of_equal_even_endpoints
        (i := 0) (j := left - 2) (k := k) (by omega) hendBound
        (Nat.zero_le k) hinterval (hinterval.trans_lt hendBound)
        (by simpa only [Nat.sub_zero] using hleftMinusEven) (by
          rw [htargetZero, htargetEnd])
      simpa only [htargetZero] using hmod
    · have hkEq : k = left - 1 := by omega
      subst k
      have hpairParity : Even (D.anchor - (left - 2)) := by
        rcases hanchorEven with ⟨e, he⟩
        refine ⟨e - d + 1, ?_⟩
        have hleftAnchor := C.left_le_anchor
        simp only [left] at hd hleftAnchor ⊢
        omega
      have hpair := D.profile.leftPairEq (left - 2) (by
        have hleftAnchor := C.left_le_anchor
        omega) hpairParity
      have hone : left - 2 + 1 = left - 1 := by omega
      rw [hone] at hpair
      have hsourceSum : Int.ModEq 2
          (a.orderSequence.entryOrZero (left - 2) +
            a.orderSequence.entryOrZero (left - 1)) (R + R) :=
        (hsourceBeforeMod (left - 2) (by
            have hleftRight := C.left_le_anchor.trans C.anchor_le_right
            omega)).add
          (hsourceBeforeMod (left - 1) (by
            have hleftRight := C.left_le_anchor.trans C.anchor_le_right
            omega))
      rw [hpair] at hsourceSum
      have hleftCong : Int.ModEq 2
          (b.orderSequence.entryOrZero (left - 2)) (R + 1) := by
        rw [htargetEnd]
      have hcross := hsourceSum.sub hleftCong
      have hnormalized : Int.ModEq 2
          (b.orderSequence.entryOrZero (left - 1)) (R - 1) := by
        convert hcross using 1 <;> ring
      have hshift : Int.ModEq 2 (R - 1) (R + 1) := by
        rw [Int.modEq_iff_dvd]
        exact ⟨1, by ring⟩
      exact hnormalized.trans hshift
  have hsourceAfterMod (k : Nat) (hright : right < k)
      (hk : k ≤ D.profile.last) :
      Int.ModEq 2 (a.orderSequence.entryOrZero k) (R + 1) := by
    have hrightLast : right < D.profile.last := hright.trans_le hk
    have hlastRightEven : Even (D.profile.last - right) := by
      rcases hlastEven with ⟨d, hd⟩
      rcases C.right_even with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      simp only [right] at he hrightLast ⊢
      omega
    rcases hlastRightEven with ⟨d, hd⟩
    have hrightTwo : right + 2 ≤ D.profile.last := by
      simp only [right] at hrightLast hd ⊢
      omega
    have hnextDistance : Even (right + 2 - D.anchor) := by
      rcases hrightDistance with ⟨e, he⟩
      refine ⟨e + 1, ?_⟩
      have hanchorRight := C.anchor_le_right
      omega
    have hsourceNext :
        a.orderSequence.entryOrZero (right + 2) = R + 1 := by
      exact C.source_after_right (right + 2) (by omega)
        hrightTwo hnextDistance
    have hsourceLast :
        a.orderSequence.entryOrZero D.profile.last = R + 1 := by
      exact C.source_after_right D.profile.last hrightLast le_rfl
        hlastDistance
    by_cases hinterval : right + 2 ≤ k
    · have hnextBound : right + 2 < n + 1 := by omega
      have hmod := a.entryOrZero_modEq_of_equal_even_endpoints
        (i := right + 2) (j := D.profile.last) (k := k)
        hnextBound hlastBound hinterval hk (hk.trans_lt hlastBound)
        (by
          refine ⟨d - 1, ?_⟩
          simp only [right] at hd ⊢
          omega) (by rw [hsourceNext, hsourceLast])
      simpa only [hsourceNext] using hmod
    · have hkEq : k = right + 1 := by omega
      subst k
      have hpairParity : Even ((right + 1) - (D.anchor + 1)) := by
        simpa only [Nat.add_sub_add_right] using hrightDistance
      have hpair := D.profile.rightPairEq (right + 1) (by
        have hanchorRight := C.anchor_le_right
        omega) (by omega) hpairParity
      have htargetSum : Int.ModEq 2
          (b.orderSequence.entryOrZero (right + 1) +
            b.orderSequence.entryOrZero (right + 2))
          ((R + 2) + (R + 2)) :=
        (htargetAfterMod (right + 1) (by
            have hleftRight := C.left_le_anchor.trans C.anchor_le_right
            omega) (by omega)).add
          (htargetAfterMod (right + 2) (by
            have hleftRight := C.left_le_anchor.trans C.anchor_le_right
            omega) hrightTwo)
      rw [← hpair] at htargetSum
      have hnextCong : Int.ModEq 2
          (a.orderSequence.entryOrZero (right + 2)) (R + 1) := by
        rw [hsourceNext]
      have hcross := htargetSum.sub hnextCong
      have hnormalized : Int.ModEq 2
          (a.orderSequence.entryOrZero (right + 1)) (R + 3) := by
        convert hcross using 1 <;> ring
      have hshift : Int.ModEq 2 (R + 3) (R + 1) := by
        rw [Int.modEq_iff_dvd]
        exact ⟨-1, by ring⟩
      exact hnormalized.trans hshift
  exact ⟨{
    leftSwitch := left
    rightSwitch := right
    left_even := C.left_even
    right_even := C.right_even
    left_le_right := C.left_le_anchor.trans C.anchor_le_right
    right_le_last := C.right_le_last
    target_before := htargetBeforeMod
    target_after := htargetAfterMod
    source_before := hsourceBeforeMod
    source_after := hsourceAfterMod }⟩

end BONG.GoodBONG

end Bong
