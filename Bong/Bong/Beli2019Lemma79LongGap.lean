/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79LongCommonSuffix
import Bong.Bong.Beli2019Lemma716LongExceptional

/-!
# Beli (2019), the large target-gap remark after Lemma 6.11

The proof of Lemma 7.9(iv) uses the remark following Lemma 6.11: before
the common suffix every target gap is at most `2e`, except for the single
type-I gap immediately preceding the first canonical switch.  That gap is
at most `2e + 1`.  This file records the corresponding zero-based statement.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- In the active type-I difference interval, a target gap strictly larger
than `2e` is the unique gap immediately before the first canonical switch,
and is exactly `2e + 1`. -/
theorem lemma79_typeI_largeTargetGap_forces_leftSwitch
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hactive : i.val < D.profile.last)
    (hlarge : 2 * (ramificationIndex K : Int) <
      b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩) :
    i.val + 1 = C.leftSwitch ∧
      b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩ =
        2 * (ramificationIndex K : Int) + 1 := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hlastBound : D.profile.last < n + 2 :=
    D.profile.lastDifference.bound
  have hleftEven := C.left_even
  have hrightEven := C.right_even
  have hanchorEven : Even D.anchor := by
    by_cases hanchor : D.profile.first = D.anchor
    · rw [← hanchor, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor hanchor
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastFromAnchor : Even (D.profile.last - D.anchor) := by
    by_cases hanchor : D.anchor = D.profile.last
    · rw [← hanchor]
      exact ⟨0, by omega⟩
    · exact (D.profile.rightProfile
        (lt_of_le_of_ne D.profile.anchor_le_last hanchor)).1
  by_cases hbefore : i.val < C.leftSwitch - 1
  · have hleftPos : 0 < C.leftSwitch := by omega
    have hleftTwo : 2 ≤ C.leftSwitch := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    by_cases hboundary : i.val = C.leftSwitch - 2
    · have hiEven : Even i.val := by
        rw [hboundary]
        rcases C.left_even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have halpha := a.beli2019Lemma69_i_typeI_targetLeftTail
        b D C hfirst hleftPos i.val (by omega) hiEven
      have hgapLeOne := b.orderGap_le_one_of_alphaValue_le_one
        ⟨i.val, by have := i.succ_lt_large; omega⟩ halpha
      have he := ramificationIndex_pos (K := K)
      omega
    · let leftEnd : Fin (n + 2) := ⟨C.leftSwitch - 2, by omega⟩
      have hzeroOrder : b.order (0 : Fin (n + 2)) = b.order leftEnd := by
        rw [← b.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
          ← b.orderSequence_entryOrZero_eq_order leftEnd]
        have hzero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
        have hend := C.target_before_left (C.leftSwitch - 2)
          (by omega) (by
            rcases C.left_even with ⟨d, hd⟩
            exact ⟨d - 1, by omega⟩)
        exact hzero.trans hend.symm
      have hinterval := b.beli2019Lemma66_i (0 : Fin (n + 2)) leftEnd
        (Fin.zero_le _) (by
          simpa only [leftEnd, Fin.val_zero, Nat.sub_zero] using
            (show Even (C.leftSwitch - 2) by
              rcases C.left_even with ⟨d, hd⟩
              exact ⟨d - 1, by omega⟩)) hzeroOrder
      have hiEnd : i.val < C.leftSwitch - 2 := by omega
      have hgapLe := hinterval.gap_le
        ⟨i.val, by have := i.succ_lt_large; omega⟩
        (Nat.zero_le i.val) (by
          change i.val < C.leftSwitch - 2
          exact hiEnd)
      omega
  · by_cases hswitch : i.val + 1 = C.leftSwitch
    · constructor
      · exact hswitch
      · have hleftPos : 0 < C.leftSwitch := by omega
        have hupperRaw := lemma79_typeI_leftSwitch_gap_le_twoE_add_one
          a b D C hleftPos
        have hindex : (⟨i.val, by have := i.succ_lt_large; omega⟩ :
            Fin (n + 1)) =
            ⟨C.leftSwitch - 1, by omega⟩ := by
          apply Fin.ext
          change i.val = C.leftSwitch - 1
          omega
        rw [hindex]
        have hlarge' : 2 * (ramificationIndex K : Int) <
            b.orderGap ⟨C.leftSwitch - 1, by omega⟩ := by
          simpa only [hindex] using hlarge
        omega
    · have hleft : C.leftSwitch ≤ i.val := by omega
      by_cases hcentral : i.val < C.rightSwitch
      · let left : Fin (n + 2) := ⟨C.leftSwitch, hleftBound⟩
        let right : Fin (n + 2) := ⟨C.rightSwitch, hrightBound⟩
        have heqEntry := lemma76_typeI_target_even_order_eq_left
          a b D C hfirst C.rightSwitch
            (C.left_le_anchor.trans C.anchor_le_right) le_rfl C.right_even
        have heq : b.order left = b.order right := by
          rw [← b.orderSequence_entryOrZero_eq_order left,
            ← b.orderSequence_entryOrZero_eq_order right]
          simpa only [left, right] using heqEntry
        have hparity : Even (right.val - left.val) := by
          rcases C.right_even with ⟨d, hd⟩
          rcases C.left_even with ⟨e, he⟩
          exact ⟨d - e, by simp only [left, right]; omega⟩
        have hinterval := b.beli2019Lemma66_i left right
          (by change C.leftSwitch ≤ C.rightSwitch
              exact C.left_le_anchor.trans C.anchor_le_right)
          hparity heq
        have hgapLe := hinterval.gap_le
          ⟨i.val, by have := i.succ_lt_large; omega⟩
          (by simp only [left]; exact hleft)
          (by simp only [right]; exact hcentral)
        omega
      · have hright : C.rightSwitch ≤ i.val := by omega
        let right : Fin (n + 2) := ⟨C.rightSwitch, hrightBound⟩
        let last : Fin (n + 2) := ⟨D.profile.last, hlastBound⟩
        have hrightDistance : Even (C.rightSwitch - D.anchor) := by
          rcases C.right_even with ⟨d, hd⟩
          rcases hanchorEven with ⟨e, he⟩
          exact ⟨d - e, by omega⟩
        have hrightEntry := C.target_from_anchor C.rightSwitch
          C.anchor_le_right C.right_le_last hrightDistance
        have hlastEntry := C.target_from_anchor D.profile.last
          D.profile.anchor_le_last le_rfl hlastFromAnchor
        have heq : b.order right = b.order last := by
          rw [← b.orderSequence_entryOrZero_eq_order right,
            ← b.orderSequence_entryOrZero_eq_order last]
          exact hrightEntry.trans hlastEntry.symm
        have hparity : Even (last.val - right.val) := by
          rcases hlastFromAnchor with ⟨d, hd⟩
          rcases hrightDistance with ⟨e, he⟩
          have hanchorLeLast : D.anchor ≤ D.profile.last :=
            D.profile.anchor_le_last
          have hanchorLeRight : D.anchor ≤ C.rightSwitch :=
            C.anchor_le_right
          have hlastEq : D.profile.last = D.anchor + 2 * d := by omega
          have hrightEq : C.rightSwitch = D.anchor + 2 * e := by omega
          have hed : e ≤ d := by omega
          refine ⟨d - e, ?_⟩
          simp only [right, last]
          omega
        have hinterval := b.beli2019Lemma66_i right last
          (by change C.rightSwitch ≤ D.profile.last
              exact C.right_le_last) hparity heq
        have hgapLe := hinterval.gap_le
          ⟨i.val, by have := i.succ_lt_large; omega⟩
          (by simp only [right]; exact hright)
          (by simp only [last]; exact hactive)
        omega

/-- Every active target gap in a type-II profile is at most `2e`.

The left and right outer intervals have equal-order endpoints of even
distance, so Lemma 6.6 applies.  Between the two transitions the target
orders form a plateau followed by one final jump of size one. -/
theorem lemma79_typeII_targetGap_le_twoE
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hactive : i.val < D.outer.last) :
    b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩ ≤
      2 * (ramificationIndex K : Int) := by
  let gapIndex : Fin (n + 1) :=
    ⟨i.val, by have := i.succ_lt_large; omega⟩
  have hleftBound : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hseparated := D.outer.transition.separated
    omega
  have hrightBound : D.outer.transition.firstTwo - 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hseparated := D.outer.transition.separated
    omega
  have hlastBound : D.outer.last < n + 2 :=
    D.outer.lastDifference.bound
  by_cases hleftRegion : i.val < D.outer.transition.lastZero
  · let left : Fin (n + 2) :=
      ⟨D.outer.transition.lastZero, hleftBound⟩
    have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
    have hzeroEntry := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
    have hleftEntry := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
    have heq : b.order (0 : Fin (n + 2)) = b.order left := by
      rw [← b.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
        ← b.orderSequence_entryOrZero_eq_order left]
      exact hzeroEntry.trans hleftEntry.symm
    have hinterval := b.beli2019Lemma66_i (0 : Fin (n + 2)) left
      (Fin.zero_le _) (by
        simpa only [left, Fin.val_zero, Nat.sub_zero] using hleftEven) heq
    exact hinterval.gap_le gapIndex (Nat.zero_le _)
      (by simp only [left, gapIndex]; exact hleftRegion)
  · have hleft : D.outer.transition.lastZero ≤ i.val := by omega
    by_cases hmiddle : i.val < D.outer.transition.firstTwo - 1
    · have hplateau (k : Nat)
          (hleftK : D.outer.transition.lastZero ≤ k)
          (hrightK : k < D.outer.transition.firstTwo - 1) :
          b.orderSequence.entryOrZero k =
            b.orderSequence.entryOrZero D.outer.transition.lastZero := by
        by_cases heq : k = D.outer.transition.lastZero
        · rw [heq]
        · have hstrict : D.outer.transition.lastZero < k := by omega
          have htransition := D.outer.transition.middle k hstrict (by omega)
          exact htransition.symm.trans (D.middle k hstrict (by omega))
      by_cases hbeforeBoundary : i.val + 1 <
          D.outer.transition.firstTwo - 1
      · have hcurrent := hplateau i.val hleft hmiddle
        have hnext := hplateau (i.val + 1) (by omega) hbeforeBoundary
        change b.order gapIndex.succ - b.order gapIndex.castSucc ≤
          2 * (ramificationIndex K : Int)
        rw [← b.orderSequence_entryOrZero_eq_order gapIndex.succ,
          ← b.orderSequence_entryOrZero_eq_order gapIndex.castSucc]
        have he := ramificationIndex_pos (K := K)
        simp only [gapIndex, Fin.val_succ, Fin.val_castSucc]
        omega
      · have hindex : i.val = D.outer.transition.firstTwo - 2 := by
          have hseparated := D.long
          omega
        have hnextIndex : i.val + 1 =
            D.outer.transition.firstTwo - 1 := by omega
        have hcurrent := hplateau i.val hleft hmiddle
        have hright := D.right_target
        change b.order gapIndex.succ - b.order gapIndex.castSucc ≤
          2 * (ramificationIndex K : Int)
        rw [← b.orderSequence_entryOrZero_eq_order gapIndex.succ,
          ← b.orderSequence_entryOrZero_eq_order gapIndex.castSucc]
        have he := ramificationIndex_pos (K := K)
        simp only [gapIndex, Fin.val_succ, Fin.val_castSucc]
        rw [hnextIndex]
        omega
    · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
      let right : Fin (n + 2) :=
        ⟨D.outer.transition.firstTwo - 1, hrightBound⟩
      let last : Fin (n + 2) := ⟨D.outer.last, hlastBound⟩
      have hrightEntry := D.outer.target_rightEven_eq_boundary
        (D.outer.transition.firstTwo - 1) le_rfl D.outer.right_le_last
          ⟨0, by omega⟩
      have hlastEntry := D.outer.target_rightEven_eq_boundary
        D.outer.last D.outer.right_le_last le_rfl D.outer.right_even_distance
      have heq : b.order right = b.order last := by
        rw [← b.orderSequence_entryOrZero_eq_order right,
          ← b.orderSequence_entryOrZero_eq_order last]
        exact hrightEntry.trans hlastEntry.symm
      have hinterval := b.beli2019Lemma66_i right last
        (by simp only [right, last]; exact D.outer.right_le_last)
        (by simpa only [right, last] using D.outer.right_even_distance) heq
      exact hinterval.gap_le gapIndex
        (by simp only [right, gapIndex]; exact hright)
        (by simp only [last, gapIndex]; exact hactive)

/-- Every active target gap in a type-III profile is at most `2e`.

The two outer intervals are again controlled by Lemma 6.6.  Since the
transitions are adjacent, the only remaining gap is their common centre;
Lemma 6.9 gives target `alpha ≤ 1`, hence that gap is at most one. -/
theorem lemma79_typeIII_targetGap_le_twoE
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hactive : i.val < D.outer.last) :
    b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩ ≤
      2 * (ramificationIndex K : Int) := by
  let gapIndex : Fin (n + 1) :=
    ⟨i.val, by have := i.succ_lt_large; omega⟩
  change b.orderGap gapIndex ≤ 2 * (ramificationIndex K : Int)
  have hleftBound : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hrightBound : D.outer.transition.firstTwo - 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hadjacent := D.adjacent
    omega
  have hlastBound : D.outer.last < n + 2 :=
    D.outer.lastDifference.bound
  by_cases hleftRegion : i.val < D.outer.transition.lastZero
  · let left : Fin (n + 2) :=
      ⟨D.outer.transition.lastZero, hleftBound⟩
    have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
    have hzeroEntry := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two 0 (Nat.zero_le _) ⟨0, by omega⟩
    have hleftEntry := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
    have heq : b.order (0 : Fin (n + 2)) = b.order left := by
      rw [← b.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
        ← b.orderSequence_entryOrZero_eq_order left]
      exact hzeroEntry.trans hleftEntry.symm
    have hinterval := b.beli2019Lemma66_i (0 : Fin (n + 2)) left
      (Fin.zero_le _) (by
        simpa only [left, Fin.val_zero, Nat.sub_zero] using hleftEven) heq
    exact hinterval.gap_le gapIndex (Nat.zero_le _)
      (by simp only [left, gapIndex]; exact hleftRegion)
  · have hleft : D.outer.transition.lastZero ≤ i.val := by omega
    by_cases hcenter : i.val < D.outer.transition.firstTwo - 1
    · have hindex : i.val = D.outer.transition.lastZero := by
        rw [D.adjacent] at hcenter
        omega
      have halpha := a.beli2019Lemma69_i_typeIII_target_local
        b D horder hdefect htotal
      have hgapLeOne := b.orderGap_le_one_of_alphaValue_le_one
        gapIndex (by simpa only [gapIndex, hindex] using halpha)
      have he := ramificationIndex_pos (K := K)
      omega
    · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
      let right : Fin (n + 2) :=
        ⟨D.outer.transition.firstTwo - 1, hrightBound⟩
      let last : Fin (n + 2) := ⟨D.outer.last, hlastBound⟩
      have hrightEntry := D.outer.target_rightEven_eq_boundary
        (D.outer.transition.firstTwo - 1) le_rfl D.outer.right_le_last
          ⟨0, by omega⟩
      have hlastEntry := D.outer.target_rightEven_eq_boundary
        D.outer.last D.outer.right_le_last le_rfl D.outer.right_even_distance
      have heq : b.order right = b.order last := by
        rw [← b.orderSequence_entryOrZero_eq_order right,
          ← b.orderSequence_entryOrZero_eq_order last]
        exact hrightEntry.trans hlastEntry.symm
      have hinterval := b.beli2019Lemma66_i right last
        (by simp only [right, last]; exact D.outer.right_le_last)
        (by simpa only [right, last] using D.outer.right_even_distance) heq
      exact hinterval.gap_le gapIndex
        (by simp only [right, gapIndex]; exact hright)
        (by simp only [last, gapIndex]; exact hactive)

/-- The large-gap dichotomy used in Lemma 7.9(iv): either the long index is
already in the common suffix, or the normalized classification is type I and
the index is precisely the unique exceptional switch gap. -/
theorem Lemma79NormalizedClassification.longGap_alternative
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : LongRepresentationIndex (n + 2) (n + 2))
    (hlarge : 2 * (ramificationIndex K : Int) <
      b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩) :
    D.IsCommonSuffixForLongAt i ∨
      ∃ (E : Lemma67TypeI a b)
          (C : Lemma67TypeICanonicalData a b E),
        E.profile.first = 0 ∧
          i.val + 1 = C.leftSwitch ∧
          b.orderGap ⟨i.val, by have := i.succ_lt_large; omega⟩ =
            2 * (ramificationIndex K : Int) + 1 := by
  cases D with
  | typeI E hfirst =>
      by_cases hactive : i.val < E.profile.last
      · right
        rcases a.lemma67TypeICanonicalData b E hfirst with ⟨C⟩
        have hgap := lemma79_typeI_largeTargetGap_forces_leftSwitch
          a b E C hfirst i hactive hlarge
        exact ⟨E, C, hfirst, hgap.1, hgap.2⟩
      · left
        exact ⟨E.profile.last, E.profile.lastDifference, by omega⟩
  | typeII E hfirst =>
      by_cases hactive : i.val < E.outer.last
      · have hgap := lemma79_typeII_targetGap_le_twoE
          a b E hfirst i hactive
        omega
      · left
        exact ⟨E.outer.last, E.outer.lastDifference, by omega⟩
  | typeIII E hfirst _ =>
      by_cases hactive : i.val < E.outer.last
      · have hgap := lemma79_typeIII_targetGap_le_twoE
          a b E hfirst horder hdefect htotal i hactive
        omega
      · left
        exact ⟨E.outer.last, E.outer.lastDifference, by omega⟩

end BONG.GoodBONG

end Bong
