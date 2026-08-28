/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019NormGeneratorOrders

/-!
# Beli (2019), Corollary 5.8: reconstruction of the order sequence

The maximal index `l` records the last tail entry at an odd one-based
coordinate whose order is below the first order of the original lattice.
The formulas below reconstruct the original order sequence from that first
order and the good order sequence of the projected tail.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Zero-based form of the maximal index in Corollary 5.8.  When `l = 0`,
the `below_or_zero` field implements the paper's fallback convention. -/
structure IsMaximalTailOddBelowFirst {n : Nat}
    (x y : BeliOrderSequence n Gamma) (l : Nat) : Prop where
  bound : 2 * l < n
  below_or_zero : l = 0 ∨ x.entryOrZero (2 * l) < y.entryOrZero 0
  maximal (r : Nat) (hlr : l < r) (hr : 2 * r < n) :
    y.entryOrZero 0 ≤ x.entryOrZero (2 * r)

/-- The three coordinate formulas stated in Corollary 5.8. -/
structure NormGeneratorOrderFormula {n : Nat}
    (x y : BeliOrderSequence n Gamma) (l : Nat) : Prop where
  stable_after (j : Nat) (hlj : 2 * l < j) (hjn : j < n) :
    x.entryOrZero j = y.entryOrZero j
  initial_odd (r : Nat) (hr : r ≤ l) :
    y.entryOrZero (2 * r) = y.entryOrZero 0
  even_coordinate (r : Nat) (hr : r < l) :
    y.entryOrZero (2 * r + 1) =
      x.entryOrZero (2 * r + 1) + x.entryOrZero (2 * r + 2) -
        y.entryOrZero 0

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Beli (2019), Corollary 5.8. -/
theorem normGeneratorOrderFormula {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k l : Nat) (hplateau : y.IsMaximalInitialOddPlateau k)
    (hthreshold : BeliOrderSequence.IsMaximalTailOddBelowFirst x y l)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.NormGeneratorOrderFormula x y l := by
  have hprofile := h.normGeneratorOrderProfile k hplateau htail
  have hlk : l ≤ k := by
    rcases hthreshold.below_or_zero with rfl | hbelow
    · exact Nat.zero_le k
    · by_contra hnot
      have hkl : k < l := Nat.lt_of_not_ge hnot
      have htargetLT := hplateau.lt_of_lt hkl hthreshold.bound
      have heq := hprofile.stable_after (2 * l) (by omega)
        hthreshold.bound
      exact (not_lt_of_ge hbelow.le) (heq.symm ▸ htargetLT)
  have hstable (j : Nat) (hlj : 2 * l < j) (hjn : j < n) :
      x.entryOrZero j = y.entryOrZero j := by
    by_cases hlkeq : l = k
    · subst k
      exact hprofile.stable_after j hlj hjn
    · have hlkStrict : l < k := lt_of_le_of_ne hlk hlkeq
      let pivot := 2 * l + 1
      have hpivot0 : 0 < pivot := by omega
      have hpivotK : pivot < 2 * k := by
        dsimp [pivot]
        omega
      have hpivotOdd : Odd pivot := by
        exact ⟨l, by simp [pivot, two_mul]⟩
      have hcurrent := hprofile.target_le_source pivot hpivot0
        hpivotK hpivotOdd
      have hnextBound : 2 * (l + 1) < n := by
        have := hplateau.bound
        omega
      have hnext := hthreshold.maximal (l + 1) (by omega) hnextBound
      have hpair := hprofile.pair_sum pivot hpivot0 hpivotK hpivotOdd
      have htarget := hprofile.target_pair pivot hpivot0 hpivotK hpivotOdd
      have hpivotNext : pivot + 1 = 2 * (l + 1) := by
        dsimp [pivot]
        omega
      rw [hpivotNext] at hpair
      have hsum :
          y.entryOrZero pivot + y.entryOrZero 0 =
            x.entryOrZero pivot + x.entryOrZero (2 * (l + 1)) := by
        exact (hpair.trans htarget).symm
      have hcomponents := add_eq_components_of_le hcurrent hnext hsum
      have hpivotEq : x.entryOrZero pivot = y.entryOrZero pivot :=
        hcomponents.1.symm
      apply hprofile.stable_from_eq pivot hpivot0 hpivotK hpivotOdd
        hpivotEq j
      · dsimp [pivot]
        omega
      · exact hjn
  refine
    { stable_after := hstable
      initial_odd := ?_
      even_coordinate := ?_ }
  · intro r hrl
    exact hplateau.eq_zero r (hrl.trans hlk)
  · intro r hrl
    let j := 2 * r + 1
    have hj0 : 0 < j := by
      dsimp [j]
      omega
    have hjk : j < 2 * k := by
      dsimp [j]
      omega
    have hjodd : Odd j := ⟨r, by simp [j, two_mul]⟩
    have hpair := hprofile.pair_sum j hj0 hjk hjodd
    have htarget := hprofile.target_pair j hj0 hjk hjodd
    have hsum :
        x.entryOrZero j + x.entryOrZero (j + 1) =
          y.entryOrZero j + y.entryOrZero 0 := hpair.trans htarget
    calc
      y.entryOrZero (2 * r + 1) = y.entryOrZero j := by rfl
      _ = (y.entryOrZero j + y.entryOrZero 0) -
          y.entryOrZero 0 := by simp
      _ = (x.entryOrZero j + x.entryOrZero (j + 1)) -
          y.entryOrZero 0 := by rw [hsum]
      _ = x.entryOrZero (2 * r + 1) +
          x.entryOrZero (2 * r + 2) - y.entryOrZero 0 := by
        simp [j]

end BeliOrderLE

end Bong
