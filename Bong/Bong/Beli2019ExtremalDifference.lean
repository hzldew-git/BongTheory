/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SuffixMaximum

/-!
# Beli (2019), Lemma 5.6: extremal difference profiles

This file completes the combinatorial content of Lemma 5.6.  A first
difference before an equal prefix, or a last difference after an equal
suffix, lies in the forced parity class, is a strict increase from `x` to
`y`, and generates the constant chain described in the paper.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

omit [IsOrderedAddMonoid Gamma] in
/-- Equality of all entries before `k` implies equality of the prefix sums. -/
theorem prefixSum_eq_of_entryOrZero_eq_before {m n : Nat}
    (x : BeliOrderSequence m Gamma) (y : BeliOrderSequence n Gamma)
    (k : Nat)
    (hentry : ∀ i : Nat, i < k → x.entryOrZero i = y.entryOrZero i) :
    x.prefixSum k = y.prefixSum k := by
  unfold prefixSum
  apply Finset.sum_congr rfl
  intro i hi
  exact hentry i (Finset.mem_range.mp hi)

omit [IsOrderedAddMonoid Gamma] in
/-- The suffix sum is the ordinary finite sum over `[k, n)`. -/
theorem suffixSum_eq_sum_Ico {n : Nat} (x : BeliOrderSequence n Gamma)
    (k : Nat) (hk : k ≤ n) :
    x.suffixSum k = ∑ i ∈ Finset.Ico k n, x.entryOrZero i := by
  rw [x.suffixSum_eq_total_sub_prefix k hk]
  unfold prefixSum
  exact (Finset.sum_Ico_eq_sub _ hk).symm

omit [IsOrderedAddMonoid Gamma] in
/-- Equality of all entries from `k` onward implies equality of suffix sums. -/
theorem suffixSum_eq_of_entryOrZero_eq_after {n : Nat}
    (x y : BeliOrderSequence n Gamma) (k : Nat) (hk : k ≤ n)
    (hentry : ∀ i : Nat, k ≤ i → i < n →
      x.entryOrZero i = y.entryOrZero i) :
    x.suffixSum k = y.suffixSum k := by
  rw [x.suffixSum_eq_sum_Ico k hk, y.suffixSum_eq_sum_Ico k hk]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  exact hentry i hi'.1 hi'.2

omit [IsOrderedAddMonoid Gamma] in
/-- Two-step monotonicity iterated along an even index gap. -/
theorem entryOrZero_le_of_evenGap {n : Nat}
    (x : BeliOrderSequence n Gamma) (p q : Nat)
    (hpq : p ≤ q) (hq : q < n) (heven : Even (q - p)) :
    x.entryOrZero p ≤ x.entryOrZero q := by
  rcases heven with ⟨r, hr⟩
  have hqp : q = p + 2 * r := by omega
  have hprop : ∀ s : Nat, p + 2 * s < n →
      x.entryOrZero p ≤ x.entryOrZero (p + 2 * s) := by
    intro s
    induction s with
    | zero =>
        intro _
        exact le_rfl
    | succ s ih =>
        intro hs
        have hprevious : p + 2 * s < n := by omega
        have hstep : x.entryOrZero (p + 2 * s) ≤
            x.entryOrZero (p + 2 * Nat.succ s) := by
          have hindex : p + 2 * s + 2 = p + 2 * Nat.succ s := by omega
          simpa only [BeliOrderSequence.entryOrZero_of_lt
              (i := p + 2 * s) x hprevious,
            BeliOrderSequence.entryOrZero_of_lt
              (i := p + 2 * Nat.succ s) x hs,
            BeliOrderSequence.entry, hindex] using
            x.twoStep (p + 2 * s) (by omega)
        exact (ih hprevious).trans hstep
  rw [hqp]
  exact hprop r (by omega)

/-- `c` is the first coordinate at which two sequences differ. -/
structure IsFirstDifferenceAt {m n : Nat}
    (x : BeliOrderSequence m Gamma) (y : BeliOrderSequence n Gamma)
    (c : Nat) : Prop where
  bound : c < n
  ne : x.entryOrZero c ≠ y.entryOrZero c
  before : ∀ i : Nat, i < c → x.entryOrZero i = y.entryOrZero i

/-- `d` is the last coordinate at which two equal-rank sequences differ. -/
structure IsLastDifferenceAt {n : Nat}
    (x y : BeliOrderSequence n Gamma) (d : Nat) : Prop where
  bound : d < n
  ne : x.entryOrZero d ≠ y.entryOrZero d
  after : ∀ i : Nat, d < i → i < n →
    x.entryOrZero i = y.entryOrZero i

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Lemma 5.6(i), final clause: profile of the first difference. -/
theorem firstDifference_profile {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (a c : Nat) (ha : a ≤ n) (haM : a < m)
    (hcA : c < a) (hc : BeliOrderSequence.IsFirstDifferenceAt x y c)
    (haeq : x.prefixSum a = y.prefixSum a) :
    Even (a - c) ∧ x.entryOrZero c < y.entryOrZero c ∧
      ∀ k : Nat, c ≤ k → k ≤ a → Even (k - c) →
        x.entryOrZero k = x.entryOrZero c := by
  have hprefixC := x.prefixSum_eq_of_entryOrZero_eq_before y c hc.before
  have hcLE := h.entryOrZero_le_of_prefixSum_eq c hc.bound hprefixC
  have hcLT : x.entryOrZero c < y.entryOrZero c :=
    lt_of_le_of_ne hcLE hc.ne
  have hparity : Even (a - c) := by
    by_contra hnotEven
    have hodd : Odd (a - c) := Nat.not_even_iff_odd.mp hnotEven
    rcases hodd with ⟨r, hr⟩
    have hnextEven : Even (a - (c + 1)) := by
      refine ⟨r, ?_⟩
      omega
    have hprefixNext := h.prefixSum_eq_of_evenGap a (c + 1) ha
      (by omega) hnextEven haeq
    rw [x.prefixSum_succ, y.prefixSum_succ, hprefixC] at hprefixNext
    exact hc.ne (add_left_cancel hprefixNext)
  refine ⟨hparity, hcLT, ?_⟩
  have hminimum := h.entryOrZero_eq_min_of_prefixSum_eq_of_evenGap
    a c ha haM (by omega) hc.bound hparity haeq
  have hcAeq : x.entryOrZero c = x.entryOrZero a := by
    by_cases hright : x.entryOrZero a ≤ y.entryOrZero c
    · simpa only [min_eq_right hright] using hminimum
    · have hleft : y.entryOrZero c ≤ x.entryOrZero a :=
        (lt_of_not_ge hright).le
      have hcy : x.entryOrZero c = y.entryOrZero c :=
        hminimum.trans (min_eq_left hleft)
      exact (ne_of_lt hcLT hcy).elim
  intro k hck hkA hkEven
  have hkM : k < m := hkA.trans_lt haM
  have hcMonotone := x.entryOrZero_le_of_evenGap c k hck hkM hkEven
  rcases hparity with ⟨r, hr⟩
  rcases hkEven with ⟨s, hs⟩
  have hkaEven : Even (a - k) := by
    refine ⟨r - s, ?_⟩
    omega
  have hkaMonotone := x.entryOrZero_le_of_evenGap k a hkA haM hkaEven
  apply le_antisymm
  · exact hkaMonotone.trans_eq hcAeq.symm
  · exact hcMonotone

/-- Lemma 5.6(ii), final clause: profile of the last difference. -/
theorem lastDifference_profile {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (b d : Nat) (hb0 : 0 < b) (hbd : b ≤ d)
    (hd : BeliOrderSequence.IsLastDifferenceAt x y d)
    (hbeq : x.suffixSum b = y.suffixSum b) :
    Even (d - (b - 1)) ∧ x.entryOrZero d < y.entryOrZero d ∧
      ∀ k : Nat, b - 1 ≤ k → k ≤ d → Even (d - k) →
        y.entryOrZero k = y.entryOrZero d := by
  have hdN : d < n := hd.bound
  have hafter := x.suffixSum_eq_of_entryOrZero_eq_after y (d + 1)
    (by omega) (by
      intro i hdi hi
      exact hd.after i (by omega) hi)
  have hdLE := h.entryOrZero_le_of_suffixSum_eq d hd.bound hafter
  have hdLT : x.entryOrZero d < y.entryOrZero d :=
    lt_of_le_of_ne hdLE hd.ne
  have hparity : Even (d - (b - 1)) := by
    by_contra hnotEven
    have hodd : Odd (d - (b - 1)) := Nat.not_even_iff_odd.mp hnotEven
    rcases hodd with ⟨r, hr⟩
    have hdbEven : Even (d - b) := by
      refine ⟨r, ?_⟩
      omega
    have hsuffixD := h.suffixSum_eq_of_evenGap b d hbd (by omega)
      hdbEven hbeq
    rw [x.suffixSum_succ d (by omega),
      y.suffixSum_succ d (by omega), hafter] at hsuffixD
    exact hd.ne (add_right_cancel hsuffixD)
  refine ⟨hparity, hdLT, ?_⟩
  have hmaximum := h.entryOrZero_eq_max_of_suffixSum_eq_of_evenGap
    b d hb0 (by omega) hd.bound hparity hbeq
  have hdAnchor : y.entryOrZero d = y.entryOrZero (b - 1) := by
    by_cases hleft : x.entryOrZero d ≤ y.entryOrZero (b - 1)
    · simpa only [max_eq_right hleft] using hmaximum
    · have hright : y.entryOrZero (b - 1) ≤ x.entryOrZero d :=
        (lt_of_not_ge hleft).le
      have hyx : y.entryOrZero d = x.entryOrZero d :=
        hmaximum.trans (max_eq_left hright)
      exact (ne_of_gt hdLT hyx).elim
  intro k hbk hkd hkEven
  have hkN : k < n := hkd.trans_lt hd.bound
  rcases hparity with ⟨r, hr⟩
  rcases hkEven with ⟨s, hs⟩
  have hanchorEven : Even (k - (b - 1)) := by
    refine ⟨r - s, ?_⟩
    omega
  have hanchorMonotone := y.entryOrZero_le_of_evenGap
    (b - 1) k hbk hkN hanchorEven
  have hkdMonotone := y.entryOrZero_le_of_evenGap k d hkd hd.bound ⟨s, hs⟩
  apply le_antisymm
  · exact hkdMonotone
  · exact hdAnchor.trans_le hanchorMonotone

end BeliOrderLE

end Bong
