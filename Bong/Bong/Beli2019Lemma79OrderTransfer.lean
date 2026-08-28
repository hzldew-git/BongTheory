/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78TargetPropagation

/-!
# Beli (2019), Lemma 7.9: transport of condition (i)

The proof of Lemma 7.9 compares three order sequences.  Away from the finite
interval on which the first two sequences differ, condition 2.1(i) transports
formally.  More generally, it transports at any coordinate where both the
current entry and the following pair do not increase.
-/

namespace Bong

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- A local comparison for `x ≤ z` also proves the corresponding comparison
for `y ≤ z` if the current `y` entry and its following pair are bounded by
the corresponding data of `x`. -/
theorem compare_of_source_bounds {n : Nat}
    {x y z : BeliOrderSequence n Gamma} (hxz : BeliOrderLE x z)
    (i : Nat) (hi : i < n)
    (hcurrent : y.entryOrZero i ≤ x.entryOrZero i)
    (hpair : y.entryOrZero i + y.entryOrZero (i + 1) ≤
      x.entryOrZero i + x.entryOrZero (i + 1)) :
    y.entry i hi ≤ z.entry i hi ∨
      ∃ (hi0 : 0 < i) (hiNext : i + 1 < n),
        y.entry i hi + y.entry (i + 1) hiNext ≤
          z.entry (i - 1) (by omega) + z.entry i hi := by
  rcases hxz.compare i hi with hxCurrent | ⟨hi0, hiNext, hxPair⟩
  · left
    have hcurrent' : y.entry i hi ≤
        x.entry i (hi.trans_le hxz.rank) := by
      calc
        y.entry i hi = y.entryOrZero i :=
          (y.entryOrZero_of_lt hi).symm
        _ ≤ x.entryOrZero i := hcurrent
        _ = x.entry i (hi.trans_le hxz.rank) :=
          x.entryOrZero_of_lt (hi.trans_le hxz.rank)
    exact hcurrent'.trans hxCurrent
  · right
    refine ⟨hi0, hiNext, ?_⟩
    have hpair' : y.entry i hi + y.entry (i + 1) hiNext ≤
        x.entry i (hi.trans_le hxz.rank) + x.entry (i + 1) hiNext := by
      calc
        y.entry i hi + y.entry (i + 1) hiNext =
            y.entryOrZero i + y.entryOrZero (i + 1) := by
          rw [y.entryOrZero_of_lt hi, y.entryOrZero_of_lt hiNext]
        _ ≤ x.entryOrZero i + x.entryOrZero (i + 1) := hpair
        _ = x.entry i (hi.trans_le hxz.rank) +
            x.entry (i + 1) hiNext := by
          rw [x.entryOrZero_of_lt (hi.trans_le hxz.rank),
            x.entryOrZero_of_lt hiNext]
    exact hpair'.trans hxPair

/-- Pointwise source domination transports the complete order relation. -/
theorem of_source_pointwise_le {n : Nat}
    {x y z : BeliOrderSequence n Gamma} (hxz : BeliOrderLE x z)
    (hyx : ∀ i : Nat, y.entryOrZero i ≤ x.entryOrZero i) :
    BeliOrderLE y z where
  rank := le_rfl
  compare := by
    intro i hi
    apply compare_of_source_bounds hxz i hi (hyx i)
    exact add_le_add (hyx i) (hyx (i + 1))

/-- After the last coordinate at which `x` and `y` differ, every local
comparison for `x ≤ z` is literally the corresponding comparison for
`y ≤ z`. -/
theorem compare_after_lastDifference {n : Nat}
    {x y z : BeliOrderSequence n Gamma} (hxz : BeliOrderLE x z)
    {last i : Nat} (D : BeliOrderSequence.IsLastDifferenceAt x y last)
    (hlast : last < i) (hi : i < n) :
    y.entry i hi ≤ z.entry i hi ∨
      ∃ (hi0 : 0 < i) (hiNext : i + 1 < n),
        y.entry i hi + y.entry (i + 1) hiNext ≤
          z.entry (i - 1) (by omega) + z.entry i hi := by
  have hcurrentEq := D.after i hlast hi
  apply compare_of_source_bounds hxz i hi (le_of_eq hcurrentEq.symm)
  by_cases hiNext : i + 1 < n
  · have hnextEq := D.after (i + 1) (by omega) hiNext
    rw [← hcurrentEq, ← hnextEq]
  · rw [BeliOrderSequence.entryOrZero_of_le x (Nat.le_of_not_gt hiNext),
      BeliOrderSequence.entryOrZero_of_le y (Nat.le_of_not_gt hiNext),
      hcurrentEq]

/-- Before the first differing coordinate, the same transport applies as
long as the following coordinate is still before that first difference. -/
theorem compare_before_firstDifference {n : Nat}
    {x y z : BeliOrderSequence n Gamma} (hxz : BeliOrderLE x z)
    {first i : Nat} (D : BeliOrderSequence.IsFirstDifferenceAt x y first)
    (hiNext : i + 1 < first) (hi : i < n) :
    y.entry i hi ≤ z.entry i hi ∨
      ∃ (hi0 : 0 < i) (hiNextBound : i + 1 < n),
        y.entry i hi + y.entry (i + 1) hiNextBound ≤
          z.entry (i - 1) (by omega) + z.entry i hi := by
  have hcurrentEq := D.before i (by omega)
  have hnextEq := D.before (i + 1) hiNext
  apply compare_of_source_bounds hxz i hi (le_of_eq hcurrentEq.symm)
  rw [← hcurrentEq, ← hnextEq]

/-- To prove `y ≤ z`, after a known last difference it is enough to check
the local comparisons up to that last coordinate. -/
theorem of_compare_through_lastDifference {n : Nat}
    {x y z : BeliOrderSequence n Gamma} (hxz : BeliOrderLE x z)
    {last : Nat} (D : BeliOrderSequence.IsLastDifferenceAt x y last)
    (hinside : ∀ (i : Nat) (hi : i < n), i ≤ last →
      y.entry i hi ≤ z.entry i hi ∨
        ∃ (hi0 : 0 < i) (hiNext : i + 1 < n),
          y.entry i hi + y.entry (i + 1) hiNext ≤
            z.entry (i - 1) (by omega) + z.entry i hi) :
    BeliOrderLE y z where
  rank := le_rfl
  compare := by
    intro i hi
    by_cases hilast : i ≤ last
    · exact hinside i hi hilast
    · exact compare_after_lastDifference hxz D
        (lt_of_not_ge hilast) hi

end BeliOrderLE

end Bong
