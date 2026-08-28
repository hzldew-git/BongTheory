/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixMinimum

/-!
# Beli (2019), Lemma 5.6(ii): the suffix maximum formula

This is the direct suffix counterpart of the prefix minimum formula.  If the
suffixes beginning at `b` agree, the matching parity class satisfies
`y_i = max x_i y_(b-1)`.
-/

namespace Bong

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Equality of the following suffix turns the current suffix inequality
into a coordinate inequality. -/
theorem entryOrZero_le_of_suffixSum_eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hk : k < n)
    (heq : x.suffixSum (k + 1) = y.suffixSum (k + 1)) :
    x.entryOrZero k ≤ y.entryOrZero k := by
  have hcurrent := h.suffixSum_le k (by omega)
  rw [x.suffixSum_succ k (by omega),
    y.suffixSum_succ k (by omega), heq] at hcurrent
  exact le_of_add_le_add_right hcurrent

/-- The local two-coordinate mechanism behind Lemma 5.6(ii). -/
theorem entryOrZero_eq_max_previous_of_suffix_and_pair_eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hk0 : 0 < k) (hk : k + 1 < n)
    (hsuffix : x.suffixSum (k + 2) = y.suffixSum (k + 2))
    (hpair : x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1)) :
    y.entryOrZero (k + 1) =
      max (x.entryOrZero (k + 1)) (y.entryOrZero (k - 1)) := by
  have hkN : k < n := by omega
  have hkNextN : k + 1 < n := hk
  have hkPrevN : k - 1 < n := by omega
  have hxNextY :=
    h.entryOrZero_le_of_suffixSum_eq (k + 1) hkNextN hsuffix
  have hyPrevNext :
      y.entryOrZero (k - 1) ≤ y.entryOrZero (k + 1) := by
    have hindex : k - 1 + 2 = k + 1 := by omega
    simpa only [BeliOrderSequence.entryOrZero_of_lt
        (i := k - 1) y hkPrevN,
      BeliOrderSequence.entryOrZero_of_lt
        (i := k + 1) y hkNextN,
      BeliOrderSequence.entry, hindex] using
      y.twoStep (k - 1) (by omega)
  apply le_antisymm
  · by_cases hyx : y.entryOrZero (k + 1) ≤ x.entryOrZero (k + 1)
    · exact hyx.trans (le_max_left _ _)
    · have hxy :
          x.entryOrZero (k + 1) < y.entryOrZero (k + 1) :=
        lt_of_not_ge hyx
      have hcurrentLt : y.entryOrZero k < x.entryOrZero k := by
        apply lt_of_add_lt_add_right
        calc
          y.entryOrZero k + x.entryOrZero (k + 1) <
              y.entryOrZero k + y.entryOrZero (k + 1) :=
            add_lt_add_right hxy _
          _ = x.entryOrZero k + x.entryOrZero (k + 1) := hpair.symm
      rcases h.compare k hkN with hcurrent | ⟨_, hnext, hbound⟩
      · have hcurrentZero : x.entryOrZero k ≤ y.entryOrZero k := by
          simpa only [BeliOrderSequence.entryOrZero_of_lt
              (i := k) x hkN,
            BeliOrderSequence.entryOrZero_of_lt
              (i := k) y hkN] using hcurrent
        exact (not_lt_of_ge hcurrentZero hcurrentLt).elim
      · have hboundZero :
            x.entryOrZero k + x.entryOrZero (k + 1) ≤
              y.entryOrZero (k - 1) + y.entryOrZero k := by
          simpa only [BeliOrderSequence.entryOrZero_of_lt
              (i := k) x hkN,
            BeliOrderSequence.entryOrZero_of_lt
              (i := k + 1) x hnext,
            BeliOrderSequence.entryOrZero_of_lt
              (i := k - 1) y hkPrevN,
            BeliOrderSequence.entryOrZero_of_lt
              (i := k) y hkN] using hbound
        have hnextPrev :
            y.entryOrZero (k + 1) ≤ y.entryOrZero (k - 1) := by
          apply le_of_add_le_add_left
          calc
            y.entryOrZero k + y.entryOrZero (k + 1) =
                x.entryOrZero k + x.entryOrZero (k + 1) := hpair.symm
            _ ≤ y.entryOrZero (k - 1) + y.entryOrZero k := hboundZero
            _ = y.entryOrZero k + y.entryOrZero (k - 1) := add_comm _ _
        exact hnextPrev.trans (le_max_right _ _)
  · exact max_le hxNextY hyPrevNext

/-- Lemma 5.6(ii)'s maximum formula.  The suffix begins at `b`, and `k`
belongs to the parity class of the preceding index `b - 1`. -/
theorem entryOrZero_eq_max_of_suffixSum_eq_of_evenGap {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (b k : Nat) (hb0 : 0 < b) (hbk : b - 1 ≤ k) (hk : k < n)
    (heven : Even (k - (b - 1)))
    (hbeq : x.suffixSum b = y.suffixSum b) :
    y.entryOrZero k =
      max (x.entryOrZero k) (y.entryOrZero (b - 1)) := by
  rcases heven with ⟨r, hr⟩
  have hkb : k = b - 1 + 2 * r := by omega
  have hprop : ∀ s : Nat, b - 1 + 2 * s < n →
      y.entryOrZero (b - 1 + 2 * s) =
        max (x.entryOrZero (b - 1 + 2 * s))
          (y.entryOrZero (b - 1)) := by
    intro s
    induction s with
    | zero =>
        intro hbaseN
        have hnext : b - 1 + 1 = b := by omega
        have hbaseSuffix :
            x.suffixSum (b - 1 + 1) = y.suffixSum (b - 1 + 1) := by
          simpa only [hnext] using hbeq
        have hxY := h.entryOrZero_le_of_suffixSum_eq
          (b - 1) hbaseN hbaseSuffix
        simpa using (max_eq_right hxY).symm
    | succ s ih =>
        intro htargetN
        let p := b + 2 * s
        have hp0 : 0 < p := by simp [p, hb0]
        have hpPair : p + 2 ≤ n := by
          dsimp [p]
          omega
        have hpSuffix : x.suffixSum p = y.suffixSum p := by
          apply h.suffixSum_eq_of_evenGap b p
          · simp [p]
          · omega
          · refine ⟨s, ?_⟩
            dsimp [p]
            omega
          · exact hbeq
        have hstep := h.entryPair_eq_and_suffixSum_eq_of_add_two
          p hpPair hpSuffix
        have hlocal := h.entryOrZero_eq_max_previous_of_suffix_and_pair_eq
          p hp0 (by omega) hstep.2 hstep.1
        have hpreviousN : b - 1 + 2 * s < n := by omega
        have hprevious := ih hpreviousN
        have hprevIndex : p - 1 = b - 1 + 2 * s := by
          dsimp [p]
          omega
        have htargetIndex : p + 1 = b - 1 + 2 * Nat.succ s := by
          dsimp [p]
          omega
        have htwoIndex : b - 1 + 2 * s + 2 =
            b - 1 + 2 * Nat.succ s := by
          omega
        have hxTwo :
            x.entryOrZero (b - 1 + 2 * s) ≤
              x.entryOrZero (b - 1 + 2 * Nat.succ s) := by
          simpa only [BeliOrderSequence.entryOrZero_of_lt
              (i := b - 1 + 2 * s) x hpreviousN,
            BeliOrderSequence.entryOrZero_of_lt
              (i := b - 1 + 2 * Nat.succ s) x htargetN,
            BeliOrderSequence.entry, htwoIndex] using
            x.twoStep (b - 1 + 2 * s) (by omega)
        rw [htargetIndex, hprevIndex, hprevious] at hlocal
        calc
          y.entryOrZero (b - 1 + 2 * Nat.succ s) =
              max (x.entryOrZero (b - 1 + 2 * Nat.succ s))
                (max (x.entryOrZero (b - 1 + 2 * s))
                  (y.entryOrZero (b - 1))) := hlocal
          _ = max (x.entryOrZero (b - 1 + 2 * Nat.succ s))
                (y.entryOrZero (b - 1)) := by
            rw [← max_assoc, max_eq_left hxTwo]
  rw [hkb]
  exact hprop r (by omega)

end BeliOrderLE

end Bong
