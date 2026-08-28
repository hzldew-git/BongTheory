/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSequence

/-!
# Beli (2019), Section 5: order arithmetic for an index-p inclusion

This file begins the proof of condition 2.1(i) in the index-uniformizer
case.  The exceptional unary Jordan case at the end of Section 5.4 produces
two odd-length blocks

`low, high, low, ..., high, low`

and

`high, low, high, ..., low, high`.

The coordinatewise inequality fails exactly at the odd positions.  At each
such position, the adjacent-pair alternative in Beli's order relation is an
equality.  The theorem below formalizes this whole case at once.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The odd-length alternating block beginning and ending with `low`. -/
def alternatingLowFirst (low high : Gamma) (k : Nat) :
    BeliOrderSequence (2 * k + 1) Gamma where
  value i := if i.val % 2 = 0 then low else high
  twoStep := by
    intro i hi
    change (if i % 2 = 0 then low else high) ≤
      (if (i + 2) % 2 = 0 then low else high)
    have hmod : (i + 2) % 2 = i % 2 := by omega
    rw [hmod]

/-- The odd-length alternating block beginning and ending with `high`. -/
def alternatingHighFirst (low high : Gamma) (k : Nat) :
    BeliOrderSequence (2 * k + 1) Gamma where
  value i := if i.val % 2 = 0 then high else low
  twoStep := by
    intro i hi
    change (if i % 2 = 0 then high else low) ≤
      (if (i + 2) % 2 = 0 then high else low)
    have hmod : (i + 2) % 2 = i % 2 := by omega
    rw [hmod]

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem alternatingLowFirst_entry (low high : Gamma) (k i : Nat)
    (hi : i < 2 * k + 1) :
    (alternatingLowFirst low high k).entry i hi =
      if i % 2 = 0 then low else high :=
  rfl

omit [AddCommGroup Gamma] [IsOrderedAddMonoid Gamma] in
@[simp]
theorem alternatingHighFirst_entry (low high : Gamma) (k i : Nat)
    (hi : i < 2 * k + 1) :
    (alternatingHighFirst low high k).entry i hi =
      if i % 2 = 0 then high else low :=
  rfl

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Section 5.4, exceptional alternating block: the low-first block is
below the high-first block in Beli's order.  At even positions this is the
direct inequality `low ≤ high`; at odd positions the adjacent sums agree. -/
theorem alternating_shift_le {low high : Gamma} (hlh : low ≤ high)
    (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.alternatingLowFirst low high k)
      (BeliOrderSequence.alternatingHighFirst low high k) where
  rank := le_rfl
  compare := by
    intro i hi
    by_cases heven : i % 2 = 0
    · left
      simp only [BeliOrderSequence.alternatingLowFirst_entry,
        BeliOrderSequence.alternatingHighFirst_entry, heven, if_pos]
      exact hlh
    · have hodd : i % 2 = 1 := by omega
      have hi0 : 0 < i := by omega
      have hiNext : i + 1 < 2 * k + 1 := by omega
      refine Or.inr ⟨hi0, hiNext, ?_⟩
      have hprevious : (i - 1) % 2 = 0 := by omega
      have hnext : (i + 1) % 2 = 0 := by omega
      simp only [BeliOrderSequence.alternatingLowFirst_entry,
        BeliOrderSequence.alternatingHighFirst_entry, hodd,
        hprevious, hnext, one_ne_zero, if_false, if_true]
      exact le_rfl

/-- The numerical block in the final paragraph of the proof of condition
2.1(i): `r - 2, r, r - 2, ...` is below its one-place shift. -/
theorem indexP_unary_exceptional_block_le (r : Int) (k : Nat) :
    BeliOrderLE
      (BeliOrderSequence.alternatingLowFirst (r - 2) r k)
      (BeliOrderSequence.alternatingHighFirst (r - 2) r k) :=
  alternating_shift_le (by omega) k

end BeliOrderLE

end Bong
