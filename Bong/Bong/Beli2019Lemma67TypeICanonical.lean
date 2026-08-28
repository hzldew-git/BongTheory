/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma72Arithmetic

/-!
# Beli (2019), Lemma 6.7: canonical type-I transition indices

The gap-two proof initially chooses an arbitrary anchor.  This file recovers
the paper's canonical indices `t` and `t'`: the first source-parity position
where the target reaches the upper value, and the last such position where
the source retains the lower value.  Finite minima and maxima make the two
thresholds independent of the original anchor.
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

/-- Exact same-parity data at the two canonical type-I thresholds. -/
structure Lemma67TypeICanonicalData
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) where
  leftSwitch : Nat
  rightSwitch : Nat
  left_le_anchor : leftSwitch ≤ D.anchor
  anchor_le_right : D.anchor ≤ rightSwitch
  right_le_last : rightSwitch ≤ D.profile.last
  left_even : Even leftSwitch
  right_even : Even rightSwitch
  source_to_anchor (k : Nat) (hk : k ≤ D.anchor)
      (heven : Even k) :
    a.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor
  target_before_left (k : Nat) (hk : k < leftSwitch)
      (heven : Even k) :
    b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor + 1
  target_from_left (k : Nat) (hleft : leftSwitch ≤ k)
      (hk : k ≤ D.anchor) (heven : Even k) :
    b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor + 2
  target_from_anchor (k : Nat) (hanchor : D.anchor ≤ k)
      (hk : k ≤ D.profile.last)
      (heven : Even (k - D.anchor)) :
    b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero D.anchor
  source_to_right (k : Nat) (hanchor : D.anchor ≤ k)
      (hk : k ≤ rightSwitch)
      (heven : Even (k - D.anchor)) :
    a.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor
  source_after_right (k : Nat) (hright : rightSwitch < k)
      (hk : k ≤ D.profile.last)
      (heven : Even (k - D.anchor)) :
    a.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor + 1

/-- Construct the canonical type-I thresholds when the first unequal index
is zero, as in Section 7. -/
theorem lemma67TypeICanonicalData
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0) :
    Nonempty (Lemma67TypeICanonicalData a b D) := by
  classical
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hsourceSame (k : Nat) (hk : k ≤ D.anchor)
      (heven : Even k) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor := by
    by_cases hzero : D.anchor = 0
    · have hkZero : k = 0 := by omega
      rw [hkZero, hzero]
    · have hlt : D.profile.first < D.anchor := by
        rw [hfirst]
        omega
      have hp := D.profile.leftProfile hlt
      have hkEq := hp.2.2 k (by rw [hfirst]; omega) hk (by
        simpa only [hfirst, Nat.sub_zero] using heven)
      have hanchorEq := hp.2.2 D.anchor D.profile.first_le_anchor
        le_rfl hp.1
      exact hkEq.trans hanchorEq.symm
  have hfirstLt :
      a.orderSequence.entryOrZero 0 <
        b.orderSequence.entryOrZero 0 := by
    by_cases hzero : D.anchor = 0
    · have hgap := D.anchor_gap
      rw [hzero] at hgap
      omega
    · have hlt : D.profile.first < D.anchor := by
        rw [hfirst]
        omega
      simpa only [hfirst] using (D.profile.leftProfile hlt).2.1
  let leftSet := (Finset.range (D.anchor + 1)).filter fun k ↦
    Even k ∧ b.orderSequence.entryOrZero k =
      a.orderSequence.entryOrZero D.anchor + 2
  have hanchorMem : D.anchor ∈ leftSet := by
    simp only [leftSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hanchorEven, D.anchor_gap⟩
  have hleftSet : leftSet.Nonempty := ⟨D.anchor, hanchorMem⟩
  let leftSwitch := leftSet.min' hleftSet
  have hleftMem : leftSwitch ∈ leftSet := leftSet.min'_mem hleftSet
  have hleftData := Finset.mem_filter.mp hleftMem
  have hleftBound : leftSwitch ≤ D.anchor := by
    have := Finset.mem_range.mp hleftData.1
    omega
  have hleftEven := hleftData.2.1
  have hleftValue := hleftData.2.2
  have htargetBefore (k : Nat) (hk : k < leftSwitch)
      (heven : Even k) :
      b.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor + 1 := by
    have hkAnchor : k ≤ D.anchor := hk.le.trans hleftBound
    have hxk := hsourceSame k hkAnchor heven
    have hyLower :
        a.orderSequence.entryOrZero D.anchor + 1 ≤
          b.orderSequence.entryOrZero k := by
      have hyMono := b.orderSequence.entryOrZero_le_of_evenGap
        0 k (Nat.zero_le k) (hkAnchor.trans_lt D.anchor_bound)
        heven
      have hxZero := hsourceSame 0 (Nat.zero_le D.anchor)
        ⟨0, by omega⟩
      omega
    have hyUpper := D.target_le_source_add_two k
      (hkAnchor.trans_lt D.anchor_bound)
    have hne : b.orderSequence.entryOrZero k ≠
        a.orderSequence.entryOrZero D.anchor + 2 := by
      intro heq
      have hkMem : k ∈ leftSet := by
        simp only [leftSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, heven, heq⟩
      exact (not_le_of_gt hk) (leftSet.min'_le k hkMem)
    omega
  have htargetAfter (k : Nat) (hleft : leftSwitch ≤ k)
      (hk : k ≤ D.anchor) (heven : Even k) :
      b.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor + 2 := by
    have hdistance : Even (k - leftSwitch) := by
      rcases heven with ⟨d, hd⟩
      rcases hleftEven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hyLower := b.orderSequence.entryOrZero_le_of_evenGap
      leftSwitch k hleft (hk.trans_lt D.anchor_bound) hdistance
    have hxk := hsourceSame k hk heven
    have hyUpper := D.target_le_source_add_two k
      (hk.trans_lt D.anchor_bound)
    omega
  have hlastEvenFromAnchor : Even (D.profile.last - D.anchor) := by
    by_cases heq : D.anchor = D.profile.last
    · rw [← heq]
      exact ⟨0, by omega⟩
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      exact (D.profile.rightProfile hlt).1
  have htargetAnchorLast :
      b.orderSequence.entryOrZero D.anchor =
        b.orderSequence.entryOrZero D.profile.last := by
    by_cases heq : D.anchor = D.profile.last
    · exact congrArg (fun k ↦ b.orderSequence.entryOrZero k) heq
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      have hp := D.profile.rightProfile hlt
      exact hp.2.2 D.anchor le_rfl
        D.profile.anchor_le_last hp.1
  have htargetRightSame (k : Nat) (hanchor : D.anchor ≤ k)
      (hk : k ≤ D.profile.last)
      (heven : Even (k - D.anchor)) :
      b.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero D.anchor := by
    by_cases heq : D.anchor = D.profile.last
    · have hkEq : k = D.anchor := by omega
      rw [hkEq]
    · have hlt : D.anchor < D.profile.last :=
        lt_of_le_of_ne D.profile.anchor_le_last heq
      have hp := D.profile.rightProfile hlt
      have hlastK : Even (D.profile.last - k) := by
        rcases hlastEvenFromAnchor with ⟨d, hd⟩
        rcases heven with ⟨e, he⟩
        refine ⟨d - e, ?_⟩
        omega
      exact (hp.2.2 k hanchor hk hlastK).trans
        htargetAnchorLast.symm
  let rightSet := (Finset.range (D.profile.last + 1)).filter fun k ↦
    D.anchor ≤ k ∧ Even (k - D.anchor) ∧
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor
  have hanchorRightMem : D.anchor ∈ rightSet := by
    simp only [rightSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le D.profile.anchor_le_last, le_rfl, ?_, trivial⟩
    exact ⟨0, by omega⟩
  have hrightSet : rightSet.Nonempty :=
    ⟨D.anchor, hanchorRightMem⟩
  let rightSwitch := rightSet.max' hrightSet
  have hrightMem : rightSwitch ∈ rightSet :=
    rightSet.max'_mem hrightSet
  have hrightData := Finset.mem_filter.mp hrightMem
  have hrightAnchor := hrightData.2.1
  have hrightEvenAnchor := hrightData.2.2.1
  have hrightValue := hrightData.2.2.2
  have hrightLast : rightSwitch ≤ D.profile.last := by
    have := Finset.mem_range.mp hrightData.1
    omega
  have hrightEven : Even rightSwitch := by
    rcases hanchorEven with ⟨d, hd⟩
    rcases hrightEvenAnchor with ⟨e, he⟩
    refine ⟨d + e, ?_⟩
    omega
  have hsourceRightBefore (k : Nat) (hanchor : D.anchor ≤ k)
      (hk : k ≤ rightSwitch)
      (heven : Even (k - D.anchor)) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor := by
    have hdistance : Even (rightSwitch - k) := by
      rcases hrightEvenAnchor with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      refine ⟨d - e, ?_⟩
      omega
    have hmono := a.orderSequence.entryOrZero_le_of_evenGap
      D.anchor k hanchor (hk.trans hrightLast |>.trans_lt
        D.profile.lastDifference.bound) heven
    have hupper := a.orderSequence.entryOrZero_le_of_evenGap
      k rightSwitch hk (hrightLast.trans_lt
        D.profile.lastDifference.bound) hdistance
    omega
  have hsourceRightAfter (k : Nat) (hright : rightSwitch < k)
      (hk : k ≤ D.profile.last)
      (heven : Even (k - D.anchor)) :
      a.orderSequence.entryOrZero k =
        a.orderSequence.entryOrZero D.anchor + 1 := by
    have hmono := a.orderSequence.entryOrZero_le_of_evenGap
      D.anchor k (hrightAnchor.trans hright.le) (hk.trans_lt
        D.profile.lastDifference.bound) heven
    have hySame := htargetRightSame k
      (hrightAnchor.trans hright.le) hk heven
    have htargetAnchor := D.anchor_gap
    have hstrictLast :
        a.orderSequence.entryOrZero D.profile.last <
          b.orderSequence.entryOrZero D.profile.last := by
      by_cases heq : D.anchor = D.profile.last
      · omega
      · have hlt : D.anchor < D.profile.last :=
          lt_of_le_of_ne D.profile.anchor_le_last heq
        exact (D.profile.rightProfile hlt).2.1
    have hupperLast := D.target_le_source_add_two
      D.profile.last D.profile.lastDifference.bound
    have hxUpper : a.orderSequence.entryOrZero k ≤
        a.orderSequence.entryOrZero D.anchor + 1 := by
      have hkLastParity : Even (D.profile.last - k) := by
        rcases hlastEvenFromAnchor with ⟨d, hd⟩
        rcases heven with ⟨e, he⟩
        refine ⟨d - e, ?_⟩
        omega
      have hkLast := a.orderSequence.entryOrZero_le_of_evenGap
        k D.profile.last hk D.profile.lastDifference.bound
        hkLastParity
      omega
    have hne : a.orderSequence.entryOrZero k ≠
        a.orderSequence.entryOrZero D.anchor := by
      intro heq
      have hkMem : k ∈ rightSet := by
        simp only [rightSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hrightAnchor.trans hright.le, heven, heq⟩
      exact (not_le_of_gt hright) (rightSet.le_max' k hkMem)
    omega
  exact ⟨{
    leftSwitch := leftSwitch
    rightSwitch := rightSwitch
    left_le_anchor := hleftBound
    anchor_le_right := hrightAnchor
    right_le_last := hrightLast
    left_even := hleftEven
    right_even := hrightEven
    source_to_anchor := hsourceSame
    target_before_left := htargetBefore
    target_from_left := htargetAfter
    target_from_anchor := htargetRightSame
    source_to_right := hsourceRightBefore
    source_after_right := hsourceRightAfter }⟩

end BONG.GoodBONG

end Bong
