/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSums

/-!
# Beli (2019), Lemma 5.5(ii)-(iii): suffix sums and rigidity

For two order sequences of the same rank, Beli's relation controls sums from
both ends.  The suffix inequality is proved directly by two-step induction,
using the last-coordinate case and the adjacent-pair inequality.  If the two
total sums agree, the prefix and suffix inequalities force every prefix sum,
and hence every entry, to agree.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Sum of the last `d` entries of a rank-`n` sequence.  Values `d > n` are
truncated to the full sequence by natural-number subtraction. -/
def suffixLengthSum {n : Nat} (x : BeliOrderSequence n Gamma)
    (d : Nat) : Gamma :=
  x.prefixSum n - x.prefixSum (n - d)

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem suffixLengthSum_zero {n : Nat} (x : BeliOrderSequence n Gamma) :
    x.suffixLengthSum 0 = 0 := by
  simp [suffixLengthSum]

omit [IsOrderedAddMonoid Gamma] in
theorem suffixLengthSum_one {n : Nat} (x : BeliOrderSequence n Gamma)
    (hn : 0 < n) :
    x.suffixLengthSum 1 = x.entryOrZero (n - 1) := by
  have hnSplit : n = (n - 1) + 1 := by omega
  have hprefix : x.prefixSum n = x.prefixSum ((n - 1) + 1) :=
    congrArg x.prefixSum hnSplit
  rw [suffixLengthSum, hprefix, x.prefixSum_succ]
  abel

omit [IsOrderedAddMonoid Gamma] in
theorem suffixLengthSum_add_two {n : Nat}
    (x : BeliOrderSequence n Gamma) (d : Nat) (hd : d + 2 ≤ n) :
    x.suffixLengthSum (d + 2) =
      (x.entryOrZero (n - (d + 2)) +
        x.entryOrZero (n - (d + 2) + 1)) + x.suffixLengthSum d := by
  have hsplit : n - d = n - (d + 2) + 2 := by omega
  rw [suffixLengthSum, suffixLengthSum, hsplit, x.prefixSum_add_two]
  abel

/-- Sum beginning at index `k`, with zero-based indexing. -/
def suffixSum {n : Nat} (x : BeliOrderSequence n Gamma)
    (k : Nat) : Gamma :=
  x.suffixLengthSum (n - k)

omit [IsOrderedAddMonoid Gamma] in
theorem suffixSum_eq_total_sub_prefix {n : Nat}
    (x : BeliOrderSequence n Gamma) (k : Nat) (hk : k ≤ n) :
    x.suffixSum k = x.prefixSum n - x.prefixSum k := by
  unfold suffixSum suffixLengthSum
  rw [Nat.sub_sub_self hk]

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Beli (2019), Lemma 5.5(ii), in last-`d` form. -/
theorem suffixLengthSum_le {n : Nat} {x y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (d : Nat) (hd : d ≤ n) :
    x.suffixLengthSum d ≤ y.suffixLengthSum d := by
  revert hd
  induction d using Nat.twoStepInduction with
  | zero =>
      intro _
      simp
  | one =>
      intro hd
      have hn : 0 < n := by omega
      rw [x.suffixLengthSum_one hn, y.suffixLengthSum_one hn]
      rcases h.compare (n - 1) (by omega) with hlast | ⟨_, hnext, _⟩
      · simpa only [BeliOrderSequence.entryOrZero_of_lt
            (i := n - 1) x (by omega),
          BeliOrderSequence.entryOrZero_of_lt
            (i := n - 1) y (by omega)] using hlast
      · omega
  | more d ih _ =>
      intro hd
      rw [x.suffixLengthSum_add_two d hd,
        y.suffixLengthSum_add_two d hd]
      apply add_le_add
      · have hnext : n - (d + 2) + 1 < n := by omega
        simpa only [BeliOrderSequence.entryOrZero_of_lt
            (i := n - (d + 2)) x (by omega),
          BeliOrderSequence.entryOrZero_of_lt
            (i := n - (d + 2) + 1) x hnext,
          BeliOrderSequence.entryOrZero_of_lt
            (i := n - (d + 2)) y (by omega),
          BeliOrderSequence.entryOrZero_of_lt
            (i := n - (d + 2) + 1) y hnext] using
          h.pairSum_le (n - (d + 2)) hnext
      · exact ih (by omega)

/-- Beli (2019), Lemma 5.5(ii), with the starting index exposed. -/
theorem suffixSum_le {n : Nat} {x y : BeliOrderSequence n Gamma}
    (h : BeliOrderLE x y) (k : Nat) (_hk : k ≤ n) :
    x.suffixSum k ≤ y.suffixSum k := by
  exact h.suffixLengthSum_le (n - k) (Nat.sub_le n k)

/-- Beli (2019), Lemma 5.5(iii): on a fixed-rank stratum, equality of the
total sums upgrades the one-sided Beli relation to equality. -/
theorem eq_of_totalPrefixSum_eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (htotal : x.prefixSum n = y.prefixSum n) :
    x = y := by
  have hprefix : ∀ k : Nat, k ≤ n → x.prefixSum k = y.prefixSum k := by
    intro k hk
    have hpLE := h.prefixSum_le k hk
    have hsLE := h.suffixSum_le k hk
    rw [x.suffixSum_eq_total_sub_prefix k hk,
      y.suffixSum_eq_total_sub_prefix k hk, htotal] at hsLE
    have hpGE : y.prefixSum k ≤ x.prefixSum k := by
      simpa only [sub_le_sub_iff_left] using hsLE
    exact le_antisymm hpLE hpGE
  apply BeliOrderSequence.ext
  funext i
  have hbefore := hprefix i.val (by omega)
  have hafter := hprefix (i.val + 1) (by omega)
  rw [x.prefixSum_succ, y.prefixSum_succ, hbefore] at hafter
  have hentry := add_left_cancel hafter
  simpa only [BeliOrderSequence.entryOrZero_of_lt x i.isLt,
    BeliOrderSequence.entryOrZero_of_lt y i.isLt,
    BeliOrderSequence.entry] using hentry

end BeliOrderLE

namespace BONG.GoodBONG

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The equal-rank BONG form of Lemma 5.5(iii). -/
theorem orderSequence_eq_of_representationOrderCondition_of_total_eq
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (htotal : a.orderPrefixSum (n + 1) = b.orderPrefixSum (n + 1)) :
    a.orderSequence = b.orderSequence := by
  apply BeliOrderLE.eq_of_totalPrefixSum_eq
    ((a.representationOrderCondition_iff b le_rfl).mp horder)
  exact htotal

end BONG.GoodBONG

end Bong
