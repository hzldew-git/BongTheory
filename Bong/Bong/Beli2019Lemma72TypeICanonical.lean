/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72TypeI

/-!
# Beli (2019), Lemma 7.2(i) for fixed canonical switches

The original packaging of Lemma 7.2(i) chooses canonical type-I switches
internally.  Later arguments already carry such switches.  This file proves
that the left switch is unique and exposes the target-prefix congruence for
the supplied canonical data.
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

/-- The left switch occurring in the parity profile is the switch in any
fixed canonical type-I data. -/
theorem lemma611_typeI_leftSwitch_eq_canonical
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (P : Lemma611TypeIConsequences a b D) :
    P.leftSwitch = C.leftSwitch := by
  let R := a.orderSequence.entryOrZero D.anchor
  have hnotConsecutive : ¬ Int.ModEq 2 (R + 1) (R + 2) := by
    intro h
    rw [Int.modEq_iff_dvd] at h
    rcases h with ⟨z, hz⟩
    omega
  apply le_antisymm
  · by_contra hnot
    have hstrict : C.leftSwitch < P.leftSwitch :=
      lt_of_not_ge hnot
    have htarget := P.target_before C.leftSwitch hstrict
    have hcanonical := C.target_from_left C.leftSwitch le_rfl
      C.left_le_anchor C.left_even
    rw [hcanonical] at htarget
    exact hnotConsecutive htarget.symm
  · by_contra hnot
    have hstrict : P.leftSwitch < C.leftSwitch :=
      lt_of_not_ge hnot
    have hleftLast : P.leftSwitch ≤ D.profile.last :=
      P.left_le_right.trans P.right_le_last
    have htarget := P.target_after P.leftSwitch le_rfl hleftLast
    have hcanonical := C.target_before_left P.leftSwitch hstrict
      P.left_even
    rw [hcanonical] at htarget
    exact hnotConsecutive htarget

/-- The right switch occurring in the parity profile is the switch in any
fixed canonical type-I data. -/
theorem lemma611_typeI_rightSwitch_eq_canonical
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (P : Lemma611TypeIConsequences a b D) :
    P.rightSwitch = C.rightSwitch := by
  let R := a.orderSequence.entryOrZero D.anchor
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hcanonicalBefore (k : Nat) (hkEven : Even k)
      (hkRight : k ≤ C.rightSwitch) :
      a.orderSequence.entryOrZero k = R := by
    by_cases hkAnchor : k ≤ D.anchor
    · exact C.source_to_anchor k hkAnchor hkEven
    · have hanchorK : D.anchor ≤ k := (Nat.lt_of_not_ge hkAnchor).le
      have hdistance : Even (k - D.anchor) := by
        rcases hkEven with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨d - e, by omega⟩
      exact C.source_to_right k hanchorK hkRight hdistance
  have hnotConsecutive : ¬ Int.ModEq 2 (R + 1) R := by
    intro h
    rw [Int.modEq_iff_dvd] at h
    rcases h with ⟨z, hz⟩
    omega
  apply le_antisymm
  · by_contra hnot
    have hstrict : C.rightSwitch < P.rightSwitch := lt_of_not_ge hnot
    rcases C.right_even with ⟨d, hd⟩
    rcases P.right_even with ⟨e, he⟩
    have htwo : C.rightSwitch + 2 ≤ P.rightSwitch := by omega
    let k := C.rightSwitch + 2
    have hkEven : Even k := ⟨d + 1, by simp only [k]; omega⟩
    have hdistance : Even (k - D.anchor) := by
      rcases hanchorEven with ⟨f, hf⟩
      exact ⟨d + 1 - f, by simp only [k]; omega⟩
    have hcanonical := C.source_after_right k (by
      simp only [k]
      omega) (by
        simp only [k]
        exact htwo.trans P.right_le_last) hdistance
    have hprofile := P.source_before k (by
      simp only [k]
      exact htwo)
    rw [hcanonical] at hprofile
    exact hnotConsecutive hprofile
  · by_contra hnot
    have hstrict : P.rightSwitch < C.rightSwitch := lt_of_not_ge hnot
    rcases P.right_even with ⟨d, hd⟩
    rcases C.right_even with ⟨e, he⟩
    have htwo : P.rightSwitch + 2 ≤ C.rightSwitch := by omega
    let k := P.rightSwitch + 2
    have hkEven : Even k := ⟨d + 1, by simp only [k]; omega⟩
    have hcanonical := hcanonicalBefore k hkEven (by
      simp only [k]
      exact htwo)
    have hprofile := P.source_after k (by
      simp only [k]
      omega) (by
        simp only [k]
        exact htwo.trans C.right_le_last)
    rw [hcanonical] at hprofile
    exact hnotConsecutive hprofile.symm

/-- Lemma 7.2(i)'s target-prefix congruence, using the canonical switches
already present in the surrounding proof. -/
theorem lemma72_typeI_target_after_of_canonical
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hleft : C.leftSwitch + 1 ≤ i)
    (hi : i ≤ D.profile.last + 1) :
    Int.ModEq 2 (b.orderSequence.prefixSum i)
      ((i : Int) * (a.orderSequence.entryOrZero D.anchor + 2)) := by
  rcases a.lemma611TypeI b D hfirst with ⟨P⟩
  have hswitch := a.lemma611_typeI_leftSwitch_eq_canonical b D C P
  let left := P.leftSwitch
  let R := a.orderSequence.entryOrZero D.anchor
  have hleftZero : Int.ModEq 2 (left : Int) 0 := by
    rcases P.left_even with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    omega
  have hbase : Int.ModEq 2 (b.orderSequence.prefixSum left)
      ((left : Int) * (R + 1)) := by
    apply b.orderSequence.prefixSum_modEq_mul (R + 1) left
    intro k hk
    exact P.target_before k hk
  have hleftI : left ≤ i := by
    dsimp only [left]
    omega
  have hsum := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    ((left : Int) * (R + 1)) (R + 2) hleftI hbase (by
      intro k hkLeft hkI
      exact P.target_after k hkLeft (by omega))
  have hformula :
      (left : Int) * (R + 1) +
          ((i - left : Nat) : Int) * (R + 2) =
        (i : Int) * (R + 2) - (left : Int) := by
    rw [Nat.cast_sub hleftI]
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
  simpa only [R] using hfinal

/-- Lemma 7.2(i)'s source-prefix congruence before the supplied canonical
right switch. -/
theorem lemma72_typeI_source_before_of_canonical
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hi : i ≤ C.rightSwitch + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) * a.orderSequence.entryOrZero D.anchor) := by
  rcases a.lemma611TypeI b D hfirst with ⟨P⟩
  have hswitch := a.lemma611_typeI_rightSwitch_eq_canonical
    b D C hfirst P
  apply a.orderSequence.prefixSum_modEq_mul
    (a.orderSequence.entryOrZero D.anchor) i
  intro k hk
  exact P.source_before k (by omega)

/-- Lemma 7.2(i)'s source-prefix congruence after the supplied canonical
right switch. -/
theorem lemma72_typeI_source_after_of_canonical
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hright : C.rightSwitch + 1 ≤ i)
    (hi : i ≤ D.profile.last + 1) :
    Int.ModEq 2 (a.orderSequence.prefixSum i)
      ((i : Int) *
        (a.orderSequence.entryOrZero D.anchor + 1) - 1) := by
  rcases a.lemma611TypeI b D hfirst with ⟨P⟩
  have hswitch := a.lemma611_typeI_rightSwitch_eq_canonical
    b D C hfirst P
  let right := P.rightSwitch
  let R := a.orderSequence.entryOrZero D.anchor
  have hrightOne : Int.ModEq 2 ((right + 1 : Nat) : Int) 1 := by
    rcases P.right_even with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    push_cast
    omega
  have hbase : Int.ModEq 2
      (a.orderSequence.prefixSum (right + 1))
      (((right + 1 : Nat) : Int) * R) := by
    apply a.orderSequence.prefixSum_modEq_mul R (right + 1)
    intro k hk
    exact P.source_before k (by omega)
  have hrightI : right + 1 ≤ i := by
    dsimp only [right]
    omega
  have hsum := a.orderSequence.prefixSum_modEq_add_mul_of_tail
    (((right + 1 : Nat) : Int) * R) (R + 1) hrightI hbase (by
      intro k hkRight hkI
      exact P.source_after k (by omega) (by omega))
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
  simpa only [R] using hfinal

end BONG.GoodBONG

end Bong
