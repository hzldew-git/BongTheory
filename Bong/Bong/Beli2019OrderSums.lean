/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSequence

/-!
# Beli (2019), Lemma 5.5(i): cumulative order sums

This is the first purely combinatorial layer used in Sections 5-6.  Prefix
sums are defined with a zero extension, so their recursion laws do not carry
dependent bound proofs.  On the valid range they are the ordinary sums of
the entries.  Lemma 5.5(i) then follows by two-step induction from the first
coordinate and adjacent-pair inequalities already proved in Lemma 1.6.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- An entry of a Beli order sequence, extended by zero past its rank. -/
def entryOrZero {n : Nat} (x : BeliOrderSequence n Gamma) (i : Nat) : Gamma :=
  if hi : i < n then x.entry i hi else 0

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem entryOrZero_of_lt {n : Nat} (x : BeliOrderSequence n Gamma)
    {i : Nat} (hi : i < n) :
    x.entryOrZero i = x.entry i hi := by
  simp only [entryOrZero, dif_pos hi]

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem entryOrZero_of_le {n : Nat} (x : BeliOrderSequence n Gamma)
    {i : Nat} (hi : n ≤ i) :
    x.entryOrZero i = 0 := by
  simp only [entryOrZero, dif_neg (Nat.not_lt.mpr hi)]

/-- Sum of the first `k` entries, using the zero extension outside the
sequence. -/
def prefixSum {n : Nat} (x : BeliOrderSequence n Gamma) (k : Nat) : Gamma :=
  ∑ i ∈ Finset.range k, x.entryOrZero i

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem prefixSum_zero {n : Nat} (x : BeliOrderSequence n Gamma) :
    x.prefixSum 0 = 0 := by
  simp [prefixSum]

omit [IsOrderedAddMonoid Gamma] in
theorem prefixSum_succ {n : Nat} (x : BeliOrderSequence n Gamma) (k : Nat) :
    x.prefixSum (k + 1) = x.prefixSum k + x.entryOrZero k := by
  simp only [prefixSum, Finset.sum_range_succ]

omit [IsOrderedAddMonoid Gamma] in
theorem prefixSum_add_two {n : Nat}
    (x : BeliOrderSequence n Gamma) (k : Nat) :
    x.prefixSum (k + 2) =
      x.prefixSum k + (x.entryOrZero k + x.entryOrZero (k + 1)) := by
  rw [show k + 2 = (k + 1) + 1 by omega, x.prefixSum_succ,
    x.prefixSum_succ]
  ac_rfl

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem prefixSum_one {n : Nat} (x : BeliOrderSequence n Gamma) :
    x.prefixSum 1 = x.entryOrZero 0 := by
  simpa using x.prefixSum_succ 0

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Beli (2019), Lemma 5.5(i): `x ≤ y` implies every valid prefix-sum
inequality. -/
theorem prefixSum_le {m n : Nat} {x : BeliOrderSequence m Gamma}
    {y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hk : k ≤ n) :
    x.prefixSum k ≤ y.prefixSum k := by
  revert hk
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _
      simp
  | one =>
      intro hk
      have hn : 0 < n := by omega
      have hm : 0 < m := hn.trans_le h.rank
      simpa only [BeliOrderSequence.prefixSum_one,
        BeliOrderSequence.entryOrZero_of_lt x hm,
        BeliOrderSequence.entryOrZero_of_lt y hn] using h.first_le hn
  | more k ih _ =>
      intro hk
      have hkn : k + 1 < n := by omega
      have hkm : k < m := (show k < n by omega).trans_le h.rank
      have hkNextM : k + 1 < m := hkn.trans_le h.rank
      rw [x.prefixSum_add_two, y.prefixSum_add_two]
      apply add_le_add (ih (by omega))
      simpa only [BeliOrderSequence.entryOrZero_of_lt x hkm,
        BeliOrderSequence.entryOrZero_of_lt x hkNextM,
        BeliOrderSequence.entryOrZero_of_lt y (show k < n by omega),
        BeliOrderSequence.entryOrZero_of_lt y hkn] using
        h.pairSum_le k hkn

end BeliOrderLE

namespace BONG.GoodBONG

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Sum of the first `k` valuation orders of a good BONG. -/
noncomputable def orderPrefixSum (a : GoodBONG q L (m + 1))
    (k : Nat) : Int :=
  a.orderSequence.prefixSum k

/-- Condition 2.1(i) implies the cumulative order inequality in Lemma
5.5(i), for arbitrary compatible ranks. -/
theorem orderPrefixSum_le_of_representationOrderCondition
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (k : Nat) (hk : k ≤ n + 1) :
    a.orderPrefixSum k ≤ b.orderPrefixSum k := by
  unfold orderPrefixSum
  exact ((a.representationOrderCondition_iff b hRank).mp horder).prefixSum_le k hk

end BONG.GoodBONG

end Bong
