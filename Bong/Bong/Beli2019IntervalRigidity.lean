/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderGap

/-!
# Interval rigidity for Beli order sequences

This file supplies the local form of Lemma 5.5(iii) used in the proof of
Beli (2019), Lemma 6.9(v).  A finite interval inherits Beli's order relation
when both boundary coordinates satisfy the direct alternative.  Equality of
the interval sums then forces equality at every coordinate of the interval.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The contiguous subsequence of length `length` beginning at `start`. -/
def segmentSequence {n : Nat} (x : BeliOrderSequence n Gamma)
    (start length : Nat) (hbound : start + length ≤ n) :
    BeliOrderSequence length Gamma where
  value i := x.value ⟨start + i.1, by omega⟩
  twoStep := by
    intro i hi
    have h := x.twoStep (start + i) (by omega)
    change x.value ⟨start + i, by omega⟩ ≤
      x.value ⟨start + (i + 2), by omega⟩
    simpa only [Nat.add_assoc] using h

omit [IsOrderedAddMonoid Gamma] in
@[simp]
theorem segmentSequence_value {n : Nat} (x : BeliOrderSequence n Gamma)
    (start length : Nat) (hbound : start + length ≤ n)
    (i : Fin length) :
    (x.segmentSequence start length hbound).value i =
      x.value ⟨start + i.1, by omega⟩ :=
  rfl

omit [IsOrderedAddMonoid Gamma] in
theorem segmentSequence_entryOrZero {n : Nat}
    (x : BeliOrderSequence n Gamma) (start length : Nat)
    (hbound : start + length ≤ n) (i : Nat) (hi : i < length) :
    (x.segmentSequence start length hbound).entryOrZero i =
      x.entryOrZero (start + i) := by
  rw [entryOrZero_of_lt _ hi, entryOrZero_of_lt _ (by omega)]
  rfl

omit [IsOrderedAddMonoid Gamma] in
theorem segmentSequence_prefixSum {n : Nat}
    (x : BeliOrderSequence n Gamma) (start length : Nat)
    (hbound : start + length ≤ n) (k : Nat) (hk : k ≤ length) :
    (x.segmentSequence start length hbound).prefixSum k =
      x.segmentSum start (start + k) := by
  induction k with
  | zero =>
      simp [segmentSum]
  | succ k ih =>
      have hkLength : k < length := by omega
      rw [(x.segmentSequence start length hbound).prefixSum_succ,
        ih (by omega), x.segmentSequence_entryOrZero start length
          hbound k hkLength]
      unfold segmentSum
      rw [show start + (k + 1) = (start + k) + 1 by omega,
        x.prefixSum_succ (start + k)]
      abel

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- A nonempty interval inherits Beli's order relation when its two boundary
coordinates satisfy the direct comparison alternative. -/
theorem segmentSequence_le {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (start length : Nat) (hbound : start + length ≤ n)
    (hpos : 0 < length)
    (hfirst : x.entryOrZero start ≤ y.entryOrZero start)
    (hlast : x.entryOrZero (start + length - 1) ≤
      y.entryOrZero (start + length - 1)) :
    BeliOrderLE
      (x.segmentSequence start length hbound)
      (y.segmentSequence start length hbound) where
  rank := le_rfl
  compare := by
    intro i hi
    by_cases hiZero : i = 0
    · subst i
      left
      have hfirst' := hfirst
      rw [BeliOrderSequence.entryOrZero_of_lt x (by omega),
        BeliOrderSequence.entryOrZero_of_lt y (by omega)] at hfirst'
      simpa only [BeliOrderSequence.entry,
        BeliOrderSequence.segmentSequence, Nat.add_zero] using hfirst'
    · by_cases hiLast : i + 1 = length
      · left
        have hlast' := hlast
        rw [BeliOrderSequence.entryOrZero_of_lt x (by omega),
          BeliOrderSequence.entryOrZero_of_lt y (by omega)] at hlast'
        simpa only [BeliOrderSequence.entry,
          BeliOrderSequence.segmentSequence,
          show start + length - 1 = start + i by omega] using hlast'
      · have hiNext : i + 1 < length := by omega
        rcases h.compare (start + i) (by omega) with
          hcurrent | ⟨_, _, hpair⟩
        · left
          simpa only [BeliOrderSequence.entry,
            BeliOrderSequence.segmentSequence] using hcurrent
        · right
          refine ⟨by omega, hiNext, ?_⟩
          simpa only [BeliOrderSequence.entry,
            BeliOrderSequence.segmentSequence,
            show start + i - 1 = start + (i - 1) by omega,
            show start + i + 1 = start + (i + 1) by omega] using hpair

/-- Local Lemma 5.5(iii): equality of interval sums upgrades the restricted
one-sided relation to equality of the whole interval. -/
theorem segmentSequence_eq_of_segmentSum_eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (start length : Nat) (hbound : start + length ≤ n)
    (hpos : 0 < length)
    (hfirst : x.entryOrZero start ≤ y.entryOrZero start)
    (hlast : x.entryOrZero (start + length - 1) ≤
      y.entryOrZero (start + length - 1))
    (hsum : x.segmentSum start (start + length) =
      y.segmentSum start (start + length)) :
    x.segmentSequence start length hbound =
      y.segmentSequence start length hbound := by
  apply BeliOrderLE.eq_of_totalPrefixSum_eq
    (h.segmentSequence_le start length hbound hpos hfirst hlast)
  rw [x.segmentSequence_prefixSum start length hbound length le_rfl,
    y.segmentSequence_prefixSum start length hbound length le_rfl]
  exact hsum

/-- Coordinate form of local interval rigidity. -/
theorem entryOrZero_eq_of_segmentSum_eq {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (start length : Nat) (hbound : start + length ≤ n)
    (hpos : 0 < length)
    (hfirst : x.entryOrZero start ≤ y.entryOrZero start)
    (hlast : x.entryOrZero (start + length - 1) ≤
      y.entryOrZero (start + length - 1))
    (hsum : x.segmentSum start (start + length) =
      y.segmentSum start (start + length))
    (k : Nat) (hk : k < length) :
    x.entryOrZero (start + k) = y.entryOrZero (start + k) := by
  have heq := h.segmentSequence_eq_of_segmentSum_eq start length
    hbound hpos hfirst hlast hsum
  have hvalue := congrArg
    (fun z : BeliOrderSequence length Gamma => z.value ⟨k, hk⟩) heq
  have hxBound : start + k < n := by omega
  rw [BeliOrderSequence.entryOrZero_of_lt x hxBound,
    BeliOrderSequence.entryOrZero_of_lt y hxBound]
  simpa only [BeliOrderSequence.entry,
    BeliOrderSequence.segmentSequence] using hvalue

end BeliOrderLE

end Bong
