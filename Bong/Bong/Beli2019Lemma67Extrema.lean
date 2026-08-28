/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Bounds
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 6.7: extremal profiles around a gap-two entry

When one entry attains the maximal difference two, the complementary prefix
and suffix sums agree.  This file constructs the first and last differing
indices and applies Lemma 5.6 on both sides of the anchor.  The result is the
constant parity-chain and adjacent-pair package used in the type-I branch of
Lemma 6.7.
-/

namespace Bong

namespace BeliOrderSequence

/-- A finite pair of unequal integer sequences has a first differing index,
bounded by any specified differing index. -/
theorem exists_firstDifferenceAt_le {n : Nat}
    (x y : BeliOrderSequence n Int) (anchor : Nat)
    (hanchor : anchor < n)
    (hne : x.entryOrZero anchor ≠ y.entryOrZero anchor) :
    ∃ first, IsFirstDifferenceAt x y first ∧ first ≤ anchor := by
  classical
  let support := (Finset.range n).filter fun k ↦
    x.entryOrZero k ≠ y.entryOrZero k
  have hanchorMem : anchor ∈ support := by
    simp only [support, Finset.mem_filter, Finset.mem_range]
    exact ⟨hanchor, hne⟩
  have hsupport : support.Nonempty := ⟨anchor, hanchorMem⟩
  let first := support.min' hsupport
  have hfirstMem : first ∈ support := support.min'_mem hsupport
  have hfirstData := Finset.mem_filter.mp hfirstMem
  refine ⟨first, ?_, support.min'_le anchor hanchorMem⟩
  refine {
    bound := Finset.mem_range.mp hfirstData.1
    ne := hfirstData.2
    before := ?_ }
  intro k hk
  by_contra hkNe
  have hkBound : k < n := hk.trans (Finset.mem_range.mp hfirstData.1)
  have hkMem : k ∈ support := by
    simp only [support, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkBound, hkNe⟩
  exact (not_le_of_gt hk) (support.min'_le k hkMem)

/-- A finite pair of unequal integer sequences has a last differing index,
above any specified differing index. -/
theorem exists_le_lastDifferenceAt {n : Nat}
    (x y : BeliOrderSequence n Int) (anchor : Nat)
    (hanchor : anchor < n)
    (hne : x.entryOrZero anchor ≠ y.entryOrZero anchor) :
    ∃ last, IsLastDifferenceAt x y last ∧ anchor ≤ last := by
  classical
  let support := (Finset.range n).filter fun k ↦
    x.entryOrZero k ≠ y.entryOrZero k
  have hanchorMem : anchor ∈ support := by
    simp only [support, Finset.mem_filter, Finset.mem_range]
    exact ⟨hanchor, hne⟩
  have hsupport : support.Nonempty := ⟨anchor, hanchorMem⟩
  let last := support.max' hsupport
  have hlastMem : last ∈ support := support.max'_mem hsupport
  have hlastData := Finset.mem_filter.mp hlastMem
  refine ⟨last, ?_, support.le_max' anchor hanchorMem⟩
  refine {
    bound := Finset.mem_range.mp hlastData.1
    ne := hlastData.2
    after := ?_ }
  intro k hlk hkn
  by_contra hkNe
  have hkMem : k ∈ support := by
    simp only [support, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkn, hkNe⟩
  exact (not_le_of_gt hlk) (support.le_max' k hkMem)

end BeliOrderSequence

namespace BeliOrderLE

/-- The complete extremal package around a point where `y_i = x_i + 2`. -/
structure GapTwoAnchorConsequences {n : Nat}
    (x y : BeliOrderSequence n Int) (anchor : Nat) where
  first : Nat
  last : Nat
  firstDifference : BeliOrderSequence.IsFirstDifferenceAt x y first
  lastDifference : BeliOrderSequence.IsLastDifferenceAt x y last
  first_le_anchor : first ≤ anchor
  anchor_le_last : anchor ≤ last
  prefix_eq : x.prefixSum anchor = y.prefixSum anchor
  suffix_eq : x.suffixSum (anchor + 1) = y.suffixSum (anchor + 1)
  leftProfile : first < anchor →
    Even (anchor - first) ∧
      x.entryOrZero first < y.entryOrZero first ∧
      ∀ k, first ≤ k → k ≤ anchor → Even (k - first) →
        x.entryOrZero k = x.entryOrZero first
  rightProfile : anchor < last →
    Even (last - anchor) ∧
      x.entryOrZero last < y.entryOrZero last ∧
      ∀ k, anchor ≤ k → k ≤ last → Even (last - k) →
        y.entryOrZero k = y.entryOrZero last
  leftPairEq (k : Nat) (hk : k + 2 ≤ anchor)
      (heven : Even (anchor - k)) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)
  rightPairEq (k : Nat) (hanchor : anchor + 1 ≤ k)
      (hk : k + 2 ≤ n) (heven : Even (k - (anchor + 1))) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)

/-- The gap-two branch of Lemma 6.7, through the two applications of
Lemma 5.6. -/
theorem gapTwoAnchorConsequences {n : Nat}
    {x y : BeliOrderSequence n Int} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n + 2 = y.prefixSum n)
    (anchor : Nat) (hanchor : anchor < n)
    (hentry : y.entryOrZero anchor = x.entryOrZero anchor + 2) :
    Nonempty (GapTwoAnchorConsequences x y anchor) := by
  have hne : x.entryOrZero anchor ≠ y.entryOrZero anchor := by omega
  obtain ⟨first, hfirst, hfirstAnchor⟩ :=
    x.exists_firstDifferenceAt_le y anchor hanchor hne
  obtain ⟨last, hlast, hanchorLast⟩ :=
    x.exists_le_lastDifferenceAt y anchor hanchor hne
  have hcomplement := h.prefix_suffix_eq_of_entryOrZero_eq_add_two
    htotal anchor hanchor hentry
  refine ⟨{
    first := first
    last := last
    firstDifference := hfirst
    lastDifference := hlast
    first_le_anchor := hfirstAnchor
    anchor_le_last := hanchorLast
    prefix_eq := hcomplement.1
    suffix_eq := hcomplement.2
    leftProfile := ?_
    rightProfile := ?_
    leftPairEq := ?_
    rightPairEq := ?_ }⟩
  · intro hfirstLt
    exact h.firstDifference_profile anchor first hanchor.le hanchor
      hfirstLt hfirst hcomplement.1
  · intro hlastGt
    have hprofile := h.lastDifference_profile (anchor + 1) last
      (by omega) (by omega) hlast hcomplement.2
    have hone : anchor + 1 - 1 = anchor := by omega
    rw [hone] at hprofile
    exact hprofile
  · intro k hk heven
    exact h.entryPair_eq_of_prefixSum_eq_of_evenGap
      anchor k hanchor.le hk heven hcomplement.1
  · intro k hak hk heven
    exact h.entryPair_eq_of_suffixSum_eq_of_evenGap
      (anchor + 1) k hak hk heven hcomplement.2

end BeliOrderLE

end Bong
