/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EqualityPropagation

/-!
# Beli (2019), Lemma 5.6(i): the prefix minimum formula

After a prefix-sum equality, entries in the matching parity class satisfy
`x_i = min y_i x_a`, where `a` is the first index after that prefix in
zero-based notation.  The proof isolates the local two-coordinate argument
and then propagates it backwards along the parity chain.
-/

namespace Bong

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Equality of the preceding prefix turns the next prefix inequality into
a coordinate inequality. -/
theorem entryOrZero_le_of_prefixSum_eq {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (k : Nat) (hk : k < n)
    (heq : x.prefixSum k = y.prefixSum k) :
    x.entryOrZero k ≤ y.entryOrZero k := by
  have hnext := h.prefixSum_le (k + 1) (by omega)
  rw [x.prefixSum_succ, y.prefixSum_succ, heq] at hnext
  exact le_of_add_le_add_left hnext

/-- The local two-coordinate mechanism behind Lemma 5.6(i). -/
theorem entryOrZero_eq_min_next_of_prefix_and_pair_eq {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (k : Nat) (hk : k + 1 < n)
    (hkTwoM : k + 2 < m)
    (hprefix : x.prefixSum k = y.prefixSum k)
    (hpair : x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)) :
    x.entryOrZero k =
      min (y.entryOrZero k) (x.entryOrZero (k + 2)) := by
  have hkN : k < n := by omega
  have hkM : k < m := hkN.trans_le h.rank
  have hkNextN : k + 1 < n := hk
  have hkNextM : k + 1 < m := hk.trans_le h.rank
  have hxY := h.entryOrZero_le_of_prefixSum_eq k hkN hprefix
  have hxTwo : x.entryOrZero k ≤ x.entryOrZero (k + 2) := by
    simpa only [BeliOrderSequence.entryOrZero_of_lt (i := k) x hkM,
      BeliOrderSequence.entryOrZero_of_lt (i := k + 2) x hkTwoM,
      BeliOrderSequence.entry] using
      x.twoStep k hkTwoM
  apply le_antisymm (le_min hxY hxTwo)
  by_cases hyx : y.entryOrZero k ≤ x.entryOrZero k
  · exact (min_le_left _ _).trans hyx
  · have hxy : x.entryOrZero k < y.entryOrZero k := lt_of_not_ge hyx
    have hnextLt :
        y.entryOrZero (k + 1) < x.entryOrZero (k + 1) := by
      apply lt_of_add_lt_add_left
      calc
        x.entryOrZero k + y.entryOrZero (k + 1) <
            y.entryOrZero k + y.entryOrZero (k + 1) :=
          add_lt_add_left hxy _
        _ = x.entryOrZero k + x.entryOrZero (k + 1) := hpair.symm
    rcases h.compare (k + 1) hkNextN with hcurrent | ⟨_, htwo, hbound⟩
    · have hcurrentZero :
          x.entryOrZero (k + 1) ≤ y.entryOrZero (k + 1) := by
        simpa only [BeliOrderSequence.entryOrZero_of_lt
            (i := k + 1) x hkNextM,
          BeliOrderSequence.entryOrZero_of_lt
            (i := k + 1) y hkNextN] using hcurrent
      exact (not_lt_of_ge hcurrentZero hnextLt).elim
    · have hboundZero :
          x.entryOrZero (k + 1) + x.entryOrZero (k + 2) ≤
            y.entryOrZero k + y.entryOrZero (k + 1) := by
        have hkSub : k + 1 - 1 = k := by omega
        simp only [hkSub] at hbound
        simpa only [BeliOrderSequence.entryOrZero_of_lt
            (i := k + 1) x hkNextM,
          BeliOrderSequence.entryOrZero_of_lt
            (i := k + 2) x htwo,
          BeliOrderSequence.entryOrZero_of_lt (i := k) y hkN,
          BeliOrderSequence.entryOrZero_of_lt
            (i := k + 1) y hkNextN] using hbound
      have htwoLE : x.entryOrZero (k + 2) ≤ x.entryOrZero k := by
        apply le_of_add_le_add_left
        calc
          x.entryOrZero (k + 1) + x.entryOrZero (k + 2) ≤
              y.entryOrZero k + y.entryOrZero (k + 1) := hboundZero
          _ = x.entryOrZero k + x.entryOrZero (k + 1) := hpair.symm
          _ = x.entryOrZero (k + 1) + x.entryOrZero k := add_comm _ _
      exact (min_le_right _ _).trans htwoLE

/-- Lemma 5.6(i)'s minimum formula.  Index `a` is the first coordinate
after the equal prefix; `k` belongs to the same parity class as `a`. -/
theorem entryOrZero_eq_min_of_prefixSum_eq_of_evenGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (a k : Nat) (ha : a ≤ n) (haM : a < m)
    (hk : k ≤ a) (hkN : k < n) (heven : Even (a - k))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.entryOrZero k = min (y.entryOrZero k) (x.entryOrZero a) := by
  rcases heven with ⟨r, hr⟩
  have hka : k + 2 * r = a := by omega
  have hprop : ∀ s : Nat, ∀ q : Nat, q + 2 * s = a → q < n →
      x.entryOrZero q = min (y.entryOrZero q) (x.entryOrZero a) := by
    intro s
    induction s with
    | zero =>
        intro q hqa hqN
        have hq : q = a := by omega
        subst q
        have hxY := h.entryOrZero_le_of_prefixSum_eq a hqN haeq
        exact (min_eq_right hxY).symm
    | succ s ih =>
        intro q hqa hqN
        have hnextPrefix := h.prefixSum_eq_of_evenGap a (q + 2) ha
          (by omega) (by refine ⟨s, ?_⟩; omega) haeq
        have hstep := h.prefixSum_eq_and_entryPair_eq_of_add_two
          q (by omega) hnextPrefix
        have hlocal := h.entryOrZero_eq_min_next_of_prefix_and_pair_eq
          q (by omega) (by omega) hstep.1 hstep.2
        cases s with
        | zero =>
            have hindex : q + 2 = a := by omega
            simpa only [hindex] using hlocal
        | succ s =>
            have hnextN : q + 2 < n := by omega
            have hnextMin := ih (q + 2) (by omega) hnextN
            have hyTwo :
                y.entryOrZero q ≤ y.entryOrZero (q + 2) := by
              simpa only [BeliOrderSequence.entryOrZero_of_lt
                  (i := q) y hqN,
                BeliOrderSequence.entryOrZero_of_lt
                  (i := q + 2) y hnextN,
                BeliOrderSequence.entry] using
                y.twoStep q hnextN
            calc
              x.entryOrZero q =
                  min (y.entryOrZero q) (x.entryOrZero (q + 2)) := hlocal
              _ = min (y.entryOrZero q)
                    (min (y.entryOrZero (q + 2)) (x.entryOrZero a)) := by
                rw [hnextMin]
              _ = min (y.entryOrZero q) (x.entryOrZero a) := by
                rw [← min_assoc, min_eq_left hyTwo]
  exact hprop r k hka hkN

/-- The same formula with valid entries rather than their zero extensions. -/
theorem entry_eq_min_of_prefixSum_eq_of_evenGap {m n : Nat}
    {x : BeliOrderSequence m Gamma} {y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (a k : Nat) (ha : a ≤ n) (haM : a < m)
    (hk : k ≤ a) (hkN : k < n) (heven : Even (a - k))
    (haeq : x.prefixSum a = y.prefixSum a) :
    x.entry k (hkN.trans_le h.rank) =
      min (y.entry k hkN) (x.entry a haM) := by
  simpa only [BeliOrderSequence.entryOrZero_of_lt
      (i := k) x (hkN.trans_le h.rank),
    BeliOrderSequence.entryOrZero_of_lt (i := k) y hkN,
    BeliOrderSequence.entryOrZero_of_lt (i := a) x haM] using
    h.entryOrZero_eq_min_of_prefixSum_eq_of_evenGap
      a k ha haM hk hkN heven haeq

end BeliOrderLE

end Bong
