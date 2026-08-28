/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 5.7: orders after choosing a norm generator

This file isolates the order-theoretic core of Lemma 5.7.  The paper starts
with a norm generator, adjoins a sufficiently divided copy of it, and then
applies Lemma 5.6(ii).  The resulting two order sequences have equal suffix
sums from the second coordinate onward.  The theorem below proves all of the
remaining conclusions directly from that relation.

Indices are zero based.  Thus the paper's initial odd chain
`S₁ = S₃ = ... = S_{2k+1}` occurs here at indices `0, 2, ..., 2k`.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The index `k` is maximal for the initial chain at even zero-based
indices.  These are the odd one-based indices in Beli's statement. -/
structure IsMaximalInitialOddPlateau {n : Nat}
    (y : BeliOrderSequence n Gamma) (k : Nat) : Prop where
  bound : 2 * k < n
  eq_zero (r : Nat) (hr : r ≤ k) :
    y.entryOrZero (2 * r) = y.entryOrZero 0
  maximal (r : Nat) (hr : 2 * r < n)
      (heq : y.entryOrZero (2 * r) = y.entryOrZero 0) :
    r ≤ k

omit [IsOrderedAddMonoid Gamma] in
/-- Past a maximal initial odd plateau, the corresponding entries are
strictly larger than its first entry. -/
theorem IsMaximalInitialOddPlateau.lt_of_lt {n : Nat}
    {y : BeliOrderSequence n Gamma} {k r : Nat}
    (h : y.IsMaximalInitialOddPlateau k) (hkr : k < r)
    (hr : 2 * r < n) :
    y.entryOrZero 0 < y.entryOrZero (2 * r) := by
  have hle := y.entryOrZero_le_of_evenGap 0 (2 * r)
    (by omega) hr ⟨r, by omega⟩
  apply lt_of_le_of_ne hle
  intro heq
  exact (not_le_of_gt hkr) (h.maximal r hr heq.symm)

omit [IsOrderedAddMonoid Gamma] in
/-- On a finite interval, two sequences either agree from `b` onward or
have a last difference there. -/
theorem eq_after_or_exists_lastDifferenceFrom {n : Nat}
    (x y : BeliOrderSequence n Gamma) (b : Nat) :
    (∀ i : Nat, b ≤ i → i < n →
      x.entryOrZero i = y.entryOrZero i) ∨
      ∃ d : Nat, b ≤ d ∧ IsLastDifferenceAt x y d := by
  classical
  by_cases hall : ∀ i : Nat, b ≤ i → i < n →
      x.entryOrZero i = y.entryOrZero i
  · exact Or.inl hall
  · right
    let differences : Finset Nat :=
      (Finset.range n).filter fun i =>
        b ≤ i ∧ x.entryOrZero i ≠ y.entryOrZero i
    have hdifferences : differences.Nonempty := by
      push Not at hall
      obtain ⟨i, hbi, hin, hne⟩ := hall
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, ?_⟩⟩
      exact ⟨hbi, hne⟩
    let d := differences.max' hdifferences
    have hdmem : d ∈ differences := differences.max'_mem hdifferences
    have hddata := Finset.mem_filter.mp hdmem
    refine ⟨d, hddata.2.1, ?_⟩
    refine
      { bound := Finset.mem_range.mp hddata.1
        ne := hddata.2.2
        after := ?_ }
    intro i hdi hin
    by_contra hne
    have himem : i ∈ differences := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hin, ⟨by omega, hne⟩⟩
    exact (not_le_of_gt hdi) (differences.le_max' i himem)

/-- The complete zero-based order conclusion of Beli's Lemma 5.7. -/
structure NormGeneratorOrderProfile {n : Nat}
    (x y : BeliOrderSequence n Gamma) (k : Nat) : Prop where
  stable_after (j : Nat) (hkj : 2 * k < j) (hjn : j < n) :
    x.entryOrZero j = y.entryOrZero j
  pair_sum (j : Nat) (hj0 : 0 < j) (hjk : j < 2 * k)
      (hjodd : Odd j) :
    x.entryOrZero j + x.entryOrZero (j + 1) =
      y.entryOrZero j + y.entryOrZero (j + 1)
  target_pair (j : Nat) (hj0 : 0 < j) (hjk : j < 2 * k)
      (hjodd : Odd j) :
    y.entryOrZero j + y.entryOrZero (j + 1) =
      y.entryOrZero j + y.entryOrZero 0
  target_le_source (j : Nat) (hj0 : 0 < j) (hjk : j < 2 * k)
      (hjodd : Odd j) :
    y.entryOrZero j ≤ x.entryOrZero j
  stable_from_eq (j : Nat) (hj0 : 0 < j) (hjk : j < 2 * k)
      (hjodd : Odd j) (heq : x.entryOrZero j = y.entryOrZero j) :
    ∀ q : Nat, j ≤ q → q < n →
      x.entryOrZero q = y.entryOrZero q

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Beli (2019), Lemma 5.7, after the lattice construction has supplied
the order relation and the equal tail-volume identity. -/
theorem normGeneratorOrderProfile {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hplateau : y.IsMaximalInitialOddPlateau k)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.NormGeneratorOrderProfile x y k := by
  have hkBound := hplateau.bound
  rcases x.eq_after_or_exists_lastDifferenceFrom y 1 with hall | hlast
  · refine
      { stable_after := ?_
        pair_sum := ?_
        target_pair := ?_
        target_le_source := ?_
        stable_from_eq := ?_ }
    · intro j hkj hjn
      exact hall j (by omega) hjn
    · intro j hj0 hjk hjodd
      rw [hall j (Nat.succ_le_iff.mpr hj0) (by omega),
        hall (j + 1) (by omega) (by omega)]
    · intro j _ hjk hjodd
      rcases hjodd with ⟨r, hr⟩
      have hnext := hplateau.eq_zero (r + 1) (by omega)
      have hjnext : j + 1 = 2 * (r + 1) := by omega
      rw [hjnext, hnext]
    · intro j hj0 _ _
      exact (hall j (Nat.succ_le_iff.mpr hj0) (by omega)).ge
    · intro _ hj0 _ _ _ q hjq hqn
      exact hall q (by omega) hqn
  · obtain ⟨d, hd1, hd⟩ := hlast
    have hprofile := h.lastDifference_profile 1 d (by omega) hd1 hd htail
    have hdEven := hprofile.1
    have hdLT := hprofile.2.1
    have hyProfile := hprofile.2.2
    have hyZeroD : y.entryOrZero 0 = y.entryOrZero d :=
      hyProfile 0 (by omega) (by omega) hdEven
    rcases hdEven with ⟨r, hr⟩
    have hdr : d = 2 * r := by omega
    have hyr : y.entryOrZero (2 * r) = y.entryOrZero 0 := by
      rw [← hdr]
      exact hyZeroD.symm
    have hrBound : 2 * r < n := by
      rw [← hdr]
      exact hd.bound
    have hrk : r ≤ k := hplateau.maximal r hrBound hyr
    have hdk : d ≤ 2 * k := by omega
    have pair_eq (j : Nat) (hj0 : 0 < j) (hjk : j < 2 * k)
        (hjodd : Odd j) :
        x.entryOrZero j + x.entryOrZero (j + 1) =
          y.entryOrZero j + y.entryOrZero (j + 1) := by
      rcases hjodd with ⟨s, hs⟩
      apply h.entryPair_eq_of_suffixSum_eq_of_evenGap 1 j
        (Nat.succ_le_iff.mpr hj0)
        (by omega) ⟨s, by omega⟩ htail
    have y_next_eq_zero (j : Nat) (hjk : j < 2 * k)
        (hjodd : Odd j) :
        y.entryOrZero (j + 1) = y.entryOrZero 0 := by
      rcases hjodd with ⟨s, hs⟩
      simpa only [show j + 1 = 2 * (s + 1) by omega] using
        hplateau.eq_zero (s + 1) (by omega)
    have target_lt_source_of_le_d (j : Nat) (hj0 : 0 < j)
        (hjk : j < 2 * k) (hjodd : Odd j) (hjd : j ≤ d) :
        y.entryOrZero j < x.entryOrZero j := by
      have hpair := pair_eq j hj0 hjk hjodd
      have hynext := y_next_eq_zero j hjk hjodd
      rcases hjodd with ⟨s, hs⟩
      have hnextd : j + 1 ≤ d := by omega
      have heven : Even (d - (j + 1)) := by
        refine ⟨r - (s + 1), ?_⟩
        omega
      have hxnext := x.entryOrZero_le_of_evenGap
        (j + 1) d hnextd hd.bound heven
      have hynextd : y.entryOrZero (j + 1) = y.entryOrZero d := by
        rw [hynext, ← hyZeroD]
      have hxnextLT : x.entryOrZero (j + 1) <
          y.entryOrZero (j + 1) :=
        hxnext.trans_lt (hdLT.trans_eq hynextd.symm)
      apply lt_of_add_lt_add_right
      calc
        y.entryOrZero j + x.entryOrZero (j + 1) <
            y.entryOrZero j + y.entryOrZero (j + 1) :=
          by
            simpa only [add_comm] using
              add_lt_add_right hxnextLT (y.entryOrZero j)
        _ = x.entryOrZero j + x.entryOrZero (j + 1) := hpair.symm
    refine
      { stable_after := ?_
        pair_sum := pair_eq
        target_pair := ?_
        target_le_source := ?_
        stable_from_eq := ?_ }
    · intro j hkj hjn
      exact hd.after j (hdk.trans_lt hkj) hjn
    · intro j _ hjk hjodd
      rw [y_next_eq_zero j hjk hjodd]
    · intro j hj0 hjk hjodd
      by_cases hjd : j ≤ d
      · exact (target_lt_source_of_le_d j hj0 hjk hjodd hjd).le
      · exact (hd.after j (lt_of_not_ge hjd) (by omega)).ge
    · intro j hj0 hjk hjodd heq q hjq hqn
      have hdj : d < j := by
        by_contra hnot
        have hjd : j ≤ d := Nat.le_of_not_gt hnot
        exact (ne_of_gt (target_lt_source_of_le_d j hj0 hjk hjodd hjd))
          heq
      exact hd.after q (hdj.trans_le hjq) hqn

end BeliOrderLE

end Bong
