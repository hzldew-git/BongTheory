/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderGap

/-!
# Beli (2019), Lemma 5.6: equality propagation

This file proves the pair-equality part of Lemma 5.6 in both directions.
An equality of prefix sums propagates backwards in steps of two; for equal
ranks, an equality of suffix sums propagates forwards in steps of two.
The parity hypotheses are represented by `Even` differences.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

omit [IsOrderedAddMonoid Gamma] in
theorem suffixSum_add_two {n : Nat} (x : BeliOrderSequence n Gamma)
    (k : Nat) (hk : k + 2 ≤ n) :
    x.suffixSum k =
      (x.entryOrZero k + x.entryOrZero (k + 1)) +
        x.suffixSum (k + 2) := by
  rw [x.suffixSum_eq_total_sub_prefix k (by omega),
    x.suffixSum_eq_total_sub_prefix (k + 2) hk,
    x.prefixSum_add_two]
  abel

omit [IsOrderedAddMonoid Gamma] in
theorem suffixSum_succ {n : Nat} (x : BeliOrderSequence n Gamma)
    (k : Nat) (hk : k + 1 ≤ n) :
    x.suffixSum k = x.entryOrZero k + x.suffixSum (k + 1) := by
  rw [x.suffixSum_eq_total_sub_prefix k (by omega),
    x.suffixSum_eq_total_sub_prefix (k + 1) hk,
    x.prefixSum_succ]
  abel

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- One backward equality-propagation step for a prefix. -/
theorem prefixSum_eq_and_entryPair_eq_of_add_two {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (k : Nat) (hk : k + 1 < n)
    (heq : x.prefixSum (k + 2) = y.prefixSum (k + 2)) :
    x.prefixSum k = y.prefixSum k ∧
      x.entryOrZero k + x.entryOrZero (k + 1) =
        y.entryOrZero k + y.entryOrZero (k + 1) := by
  have hprefix := h.prefixSum_le k (by omega)
  have hkN : k < n := by omega
  have hkM : k < m := hkN.trans_le h.rank
  have hkNextM : k + 1 < m := hk.trans_le h.rank
  have hpair :
      x.entryOrZero k + x.entryOrZero (k + 1) ≤
        y.entryOrZero k + y.entryOrZero (k + 1) := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt
        (i := k) x hkM,
      BeliOrderSequence.entryOrZero_of_lt (i := k + 1) x hkNextM,
      BeliOrderSequence.entryOrZero_of_lt (i := k) y hkN,
      BeliOrderSequence.entryOrZero_of_lt (i := k + 1) y hk] using
      h.pairSum_le k hk
  rw [x.prefixSum_add_two, y.prefixSum_add_two] at heq
  exact add_eq_components_of_le hprefix hpair heq

/-- A prefix equality propagates to every earlier prefix at the same
parity. -/
theorem prefixSum_eq_of_evenGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (a p : Nat) (ha : a ≤ n) (hp : p ≤ a)
    (heven : Even (a - p))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.prefixSum p = y.prefixSum p := by
  rcases heven with ⟨r, hr⟩
  have hpa : p + 2 * r = a := by omega
  have hprop : ∀ s : Nat, ∀ q : Nat, q + 2 * s = a →
      x.prefixSum q = y.prefixSum q := by
    intro s
    induction s with
    | zero =>
        intro q hqa
        have hq : q = a := by omega
        subst q
        exact haeq
    | succ s ih =>
        intro q hqa
        have hnext : q + 2 + 2 * s = a := by omega
        have hnextEq := ih (q + 2) hnext
        have hqBound : q + 1 < n := by omega
        exact
          (h.prefixSum_eq_and_entryPair_eq_of_add_two
            q hqBound hnextEq).1
  exact hprop r p hpa

/-- Lemma 5.6(i), pair-equality clause, in zero-based indexing. -/
theorem entryPair_eq_of_prefixSum_eq_of_evenGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (a k : Nat) (ha : a ≤ n)
    (hk : k + 2 ≤ a) (heven : Even (a - k))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) := by
  rcases heven with ⟨r, hr⟩
  have hrpos : 0 < r := by omega
  have hnextEven : Even (a - (k + 2)) := by
    refine ⟨r - 1, ?_⟩
    omega
  have hnextEq := h.prefixSum_eq_of_evenGap a (k + 2) ha
    (by omega) hnextEven haeq
  exact
    (h.prefixSum_eq_and_entryPair_eq_of_add_two
      k (by omega) hnextEq).2

/-- One forward equality-propagation step for a suffix. -/
theorem entryPair_eq_and_suffixSum_eq_of_add_two {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hk : k + 2 ≤ n)
    (heq : x.suffixSum k = y.suffixSum k) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
        y.entryOrZero k + y.entryOrZero (k + 1) ∧
      x.suffixSum (k + 2) = y.suffixSum (k + 2) := by
  have hpair :
      x.entryOrZero k + x.entryOrZero (k + 1) ≤
        y.entryOrZero k + y.entryOrZero (k + 1) := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt
        (i := k) x (by omega),
      BeliOrderSequence.entryOrZero_of_lt (i := k + 1) x (by omega),
      BeliOrderSequence.entryOrZero_of_lt (i := k) y (by omega),
      BeliOrderSequence.entryOrZero_of_lt (i := k + 1) y (by omega)] using
      h.pairSum_le k (by omega)
  have hsuffix := h.suffixSum_le (k + 2) hk
  rw [x.suffixSum_add_two k hk, y.suffixSum_add_two k hk] at heq
  exact add_eq_components_of_le hpair hsuffix heq

/-- A suffix equality propagates to every later suffix at the same
parity. -/
theorem suffixSum_eq_of_evenGap {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (b p : Nat) (hbp : b ≤ p) (hp : p ≤ n) (heven : Even (p - b))
    (hbeq : x.suffixSum b = y.suffixSum b) :
    x.suffixSum p = y.suffixSum p := by
  rcases heven with ⟨r, hr⟩
  have hpb : p = b + 2 * r := by omega
  have hprop : ∀ s : Nat, b + 2 * s ≤ n →
      x.suffixSum (b + 2 * s) = y.suffixSum (b + 2 * s) := by
    intro s
    induction s with
    | zero =>
        intro _
        simpa using hbeq
    | succ s ih =>
        intro hs
        have hpreviousBound : b + 2 * s + 2 ≤ n := by omega
        have hprevious := ih (by omega)
        have hstep :=
          (h.entryPair_eq_and_suffixSum_eq_of_add_two
            (b + 2 * s) hpreviousBound hprevious).2
        rw [show b + 2 * Nat.succ s = b + 2 * s + 2 by omega]
        exact hstep
  rw [hpb]
  exact hprop r (by omega)

/-- Lemma 5.6(ii), pair-equality clause, in zero-based indexing. -/
theorem entryPair_eq_of_suffixSum_eq_of_evenGap {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (b k : Nat) (hbk : b ≤ k) (hk : k + 2 ≤ n)
    (heven : Even (k - b))
    (hbeq : x.suffixSum b = y.suffixSum b) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) := by
  have hcurrent := h.suffixSum_eq_of_evenGap b k hbk (by omega)
    heven hbeq
  exact
    (h.entryPair_eq_and_suffixSum_eq_of_add_two k hk hcurrent).1

end BeliOrderLE

end Bong
