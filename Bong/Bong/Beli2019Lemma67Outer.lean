/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Transitions
import Bong.Bong.Beli2019Lemma67Extrema

/-!
# Beli (2019), Lemma 6.7: outer profiles in the no-gap-two branch

The zero prefix gap at the left transition gives prefix equality, while the
prefix gap two at the right transition and the total gap two give suffix
equality.  The first and last differences therefore carry the two extremal
profiles of Lemma 5.6.  This is the common outer part of types II and III.
-/

namespace Bong

namespace BeliOrderLE

/-- The complete outer-profile package attached to a prefix-gap transition.
-/
structure NoGapTwoOuterConsequences {n : Nat}
    (x y : BeliOrderSequence n Int) where
  transition : PrefixGapTransitionConsequences x y
  first : Nat
  last : Nat
  firstDifference : BeliOrderSequence.IsFirstDifferenceAt x y first
  lastDifference : BeliOrderSequence.IsLastDifferenceAt x y last
  first_le_left : first ≤ transition.lastZero
  right_le_last : transition.firstTwo - 1 ≤ last
  prefix_eq :
    x.prefixSum transition.lastZero = y.prefixSum transition.lastZero
  suffix_eq :
    x.suffixSum transition.firstTwo = y.suffixSum transition.firstTwo
  leftProfile : first < transition.lastZero →
    Even (transition.lastZero - first) ∧
      x.entryOrZero first < y.entryOrZero first ∧
      ∀ k, first ≤ k → k ≤ transition.lastZero → Even (k - first) →
        x.entryOrZero k = x.entryOrZero first
  rightProfile : transition.firstTwo - 1 < last →
    Even (last - (transition.firstTwo - 1)) ∧
      x.entryOrZero last < y.entryOrZero last ∧
      ∀ k, transition.firstTwo - 1 ≤ k → k ≤ last →
        Even (last - k) → y.entryOrZero k = y.entryOrZero last
  leftPairEq (k : Nat) (hk : k + 2 ≤ transition.lastZero)
      (heven : Even (transition.lastZero - k)) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)
  rightPairEq (k : Nat) (hfirst : transition.firstTwo ≤ k)
      (hk : k + 2 ≤ n) (heven : Even (k - transition.firstTwo)) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)

/-- Complete the outer profile from any explicitly supplied transition.
This form is useful under duality, where the complementary transition
indices are known before running the canonical finite-set construction. -/
theorem exists_noGapTwoOuterConsequences_of_transition {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (T : PrefixGapTransitionConsequences x y) :
    ∃ O : NoGapTwoOuterConsequences x y, O.transition = T := by
  have htransitionSeparated := T.separated
  have htransitionBound := T.firstTwo_le_rank
  have hleftBound : T.lastZero < n := by
    exact T.lastZero_lt_firstTwo.trans_le T.firstTwo_le_rank
  have hleftNe :
      x.entryOrZero T.lastZero ≠ y.entryOrZero T.lastZero := by
    rw [T.leftBoundary]
    omega
  obtain ⟨first, hfirst, hfirstLeft⟩ :=
    x.exists_firstDifferenceAt_le y T.lastZero hleftBound hleftNe
  have hrightBound : T.firstTwo - 1 < n := by omega
  have hrightNe : x.entryOrZero (T.firstTwo - 1) ≠
      y.entryOrZero (T.firstTwo - 1) := by
    rw [T.rightBoundary]
    omega
  obtain ⟨last, hlast, hrightLast⟩ :=
    x.exists_le_lastDifferenceAt y (T.firstTwo - 1)
      hrightBound hrightNe
  have hprefix :
      x.prefixSum T.lastZero = y.prefixSum T.lastZero := by
    have hgapLast := T.gap_lastZero
    unfold BeliOrderSequence.prefixGap at hgapLast
    omega
  have hsuffix :
      x.suffixSum T.firstTwo = y.suffixSum T.firstTwo := by
    rw [x.suffixSum_eq_total_sub_prefix T.firstTwo T.firstTwo_le_rank,
      y.suffixSum_eq_total_sub_prefix T.firstTwo T.firstTwo_le_rank]
    have hgapFirst := T.gap_firstTwo
    unfold BeliOrderSequence.prefixGap at hgapFirst
    omega
  refine ⟨{
    transition := T
    first := first
    last := last
    firstDifference := hfirst
    lastDifference := hlast
    first_le_left := hfirstLeft
    right_le_last := hrightLast
    prefix_eq := hprefix
    suffix_eq := hsuffix
    leftProfile := ?_
    rightProfile := ?_
    leftPairEq := ?_
    rightPairEq := ?_ }, rfl⟩
  · intro hfirstLt
    exact h.firstDifference_profile T.lastZero first hleftBound.le
      hleftBound hfirstLt hfirst hprefix
  · intro hlastGt
    exact h.lastDifference_profile T.firstTwo last
      (by omega) (by omega) hlast hsuffix
  · intro k hk heven
    exact h.entryPair_eq_of_prefixSum_eq_of_evenGap
      T.lastZero k hleftBound.le hk heven hprefix
  · intro k hfirstK hk heven
    exact h.entryPair_eq_of_suffixSum_eq_of_evenGap
      T.firstTwo k hfirstK hk heven hsuffix

/-- The common type-II/type-III outer profile in Lemma 6.7. -/
theorem noGapTwoOuterConsequences {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (hnoTwo : ∀ k, k < n →
      y.entryOrZero k ≠ x.entryOrZero k + 2) :
    Nonempty (NoGapTwoOuterConsequences x y) := by
  rcases h.prefixGapTransitionConsequences htotal hnoTwo with ⟨T⟩
  have htransitionSeparated := T.separated
  have htransitionBound := T.firstTwo_le_rank
  have hleftBound : T.lastZero < n := by
    omega
  have hleftNe :
      x.entryOrZero T.lastZero ≠ y.entryOrZero T.lastZero := by
    rw [T.leftBoundary]
    omega
  obtain ⟨first, hfirst, hfirstLeft⟩ :=
    x.exists_firstDifferenceAt_le y T.lastZero hleftBound hleftNe
  have hrightBound : T.firstTwo - 1 < n := by omega
  have hrightNe : x.entryOrZero (T.firstTwo - 1) ≠
      y.entryOrZero (T.firstTwo - 1) := by
    rw [T.rightBoundary]
    omega
  obtain ⟨last, hlast, hrightLast⟩ :=
    x.exists_le_lastDifferenceAt y (T.firstTwo - 1)
      hrightBound hrightNe
  have hprefix :
      x.prefixSum T.lastZero = y.prefixSum T.lastZero := by
    have hgapLast := T.gap_lastZero
    unfold BeliOrderSequence.prefixGap at hgapLast
    omega
  have hsuffix :
      x.suffixSum T.firstTwo = y.suffixSum T.firstTwo := by
    rw [x.suffixSum_eq_total_sub_prefix T.firstTwo T.firstTwo_le_rank,
      y.suffixSum_eq_total_sub_prefix T.firstTwo T.firstTwo_le_rank]
    have hgapFirst := T.gap_firstTwo
    unfold BeliOrderSequence.prefixGap at hgapFirst
    omega
  refine ⟨{
    transition := T
    first := first
    last := last
    firstDifference := hfirst
    lastDifference := hlast
    first_le_left := hfirstLeft
    right_le_last := hrightLast
    prefix_eq := hprefix
    suffix_eq := hsuffix
    leftProfile := ?_
    rightProfile := ?_
    leftPairEq := ?_
    rightPairEq := ?_ }⟩
  · intro hfirstLt
    exact h.firstDifference_profile T.lastZero first hleftBound.le
      hleftBound hfirstLt hfirst hprefix
  · intro hlastGt
    have hprofile := h.lastDifference_profile T.firstTwo last
      (by omega) (by omega) hlast hsuffix
    exact hprofile
  · intro k hk heven
    exact h.entryPair_eq_of_prefixSum_eq_of_evenGap
      T.lastZero k hleftBound.le hk heven hprefix
  · intro k hfirstK hk heven
    exact h.entryPair_eq_of_suffixSum_eq_of_evenGap
      T.firstTwo k hfirstK hk heven hsuffix

end BeliOrderLE

end Bong
