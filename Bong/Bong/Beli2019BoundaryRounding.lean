/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeISum

/-!
# Boundary rounding for Beli's sequence order

The endpoint calculation in Beli (2019), Lemma 6.9(v), first obtains a
half-integral error bound from an adjacent-pair inequality.  When the two
boundary coordinates are integral, that error rounds down to the required
direct comparison.  This file isolates the reusable order-theoretic step.
-/

namespace Bong

/-- Adding the cast of an integer preserves rational integrality. -/
theorem IsRationalInteger.intCast_add {x : ℚ}
    (hx : IsRationalInteger x) (z : Int) :
    IsRationalInteger ((z : ℚ) + x) := by
  rcases hx with ⟨a, ha⟩
  refine ⟨z + a, ?_⟩
  rw [ha]
  push_cast
  rfl

/-- Subtracting a rational integer from an integer cast preserves rational
integrality. -/
theorem IsRationalInteger.intCast_sub {x : ℚ}
    (hx : IsRationalInteger x) (z : Int) :
    IsRationalInteger ((z : ℚ) - x) := by
  rcases hx with ⟨a, ha⟩
  refine ⟨z - a, ?_⟩
  rw [ha]
  push_cast
  rfl

/-- Two integral rational numbers cannot be separated by a positive amount
of at most one half without already being ordered. -/
theorem IsRationalInteger.le_of_le_add_half {x y : ℚ}
    (hx : IsRationalInteger x) (hy : IsRationalInteger y)
    (hxy : x ≤ y + 1 / 2) : x ≤ y := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  rw [ha, hb] at hxy ⊢
  by_contra hnot
  have hstep : b + 1 ≤ a := by
    have : b < a := by exact_mod_cast (lt_of_not_ge hnot)
    omega
  have hstepQ : (b : ℚ) + 1 ≤ (a : ℚ) := by
    exact_mod_cast hstep
  norm_num at hxy
  linarith

namespace BeliOrderLE

/-- At the first coordinate, Beli's comparison has no crossing alternative. -/
theorem entryOrZero_zero_le {n : Nat}
    {x y : BeliOrderSequence n ℚ} (h : BeliOrderLE x y) (hn : 0 < n) :
    x.entryOrZero 0 ≤ y.entryOrZero 0 := by
  rcases h.compare 0 hn with hdirect | ⟨hpositive, _, _⟩
  · rw [BeliOrderSequence.entryOrZero_of_lt x hn,
      BeliOrderSequence.entryOrZero_of_lt y hn]
    exact hdirect
  · omega

/-- At the last coordinate, Beli's comparison has no crossing alternative. -/
theorem entryOrZero_last_le {n : Nat}
    {x y : BeliOrderSequence n ℚ} (h : BeliOrderLE x y) (hn : 0 < n) :
    x.entryOrZero (n - 1) ≤ y.entryOrZero (n - 1) := by
  have hlast : n - 1 < n := by omega
  rcases h.compare (n - 1) hlast with hdirect | ⟨_, hnext, _⟩
  · rw [BeliOrderSequence.entryOrZero_of_lt x hlast,
      BeliOrderSequence.entryOrZero_of_lt y hlast]
    exact hdirect
  · omega

/-- A one-half estimate for the preceding coordinate forces a direct
comparison at the current integral coordinate. -/
theorem entryOrZero_le_of_previous_le_add_half {n : Nat}
    {x y : BeliOrderSequence n ℚ} (h : BeliOrderLE x y)
    (i : Nat) (hiPos : 0 < i) (hi : i < n)
    (hprevious : y.entryOrZero (i - 1) ≤
      x.entryOrZero (i - 1) + 1 / 2)
    (hxi : IsRationalInteger (x.entryOrZero i))
    (hyi : IsRationalInteger (y.entryOrZero i)) :
    x.entryOrZero i ≤ y.entryOrZero i := by
  have hpairRaw := h.pairSum_le (i - 1) (by omega)
  have hpair : x.entryOrZero (i - 1) + x.entryOrZero i ≤
      y.entryOrZero (i - 1) + y.entryOrZero i := by
    rw [BeliOrderSequence.entryOrZero_of_lt x (by omega),
      BeliOrderSequence.entryOrZero_of_lt x hi,
      BeliOrderSequence.entryOrZero_of_lt y (by omega),
      BeliOrderSequence.entryOrZero_of_lt y hi]
    simpa only [show i - 1 + 1 = i by omega] using hpairRaw
  apply hxi.le_of_le_add_half hyi
  linarith

/-- The right-handed form: a one-half estimate for the following coordinate
forces a direct comparison at the current integral coordinate. -/
theorem entryOrZero_le_of_next_le_add_half {n : Nat}
    {x y : BeliOrderSequence n ℚ} (h : BeliOrderLE x y)
    (i : Nat) (hiNext : i + 1 < n)
    (hnext : y.entryOrZero (i + 1) ≤
      x.entryOrZero (i + 1) + 1 / 2)
    (hxi : IsRationalInteger (x.entryOrZero i))
    (hyi : IsRationalInteger (y.entryOrZero i)) :
    x.entryOrZero i ≤ y.entryOrZero i := by
  have hpairRaw := h.pairSum_le i hiNext
  have hpair : x.entryOrZero i + x.entryOrZero (i + 1) ≤
      y.entryOrZero i + y.entryOrZero (i + 1) := by
    rw [BeliOrderSequence.entryOrZero_of_lt x (by omega),
      BeliOrderSequence.entryOrZero_of_lt x hiNext,
      BeliOrderSequence.entryOrZero_of_lt y (by omega),
      BeliOrderSequence.entryOrZero_of_lt y hiNext]
    exact hpairRaw
  apply hxi.le_of_le_add_half hyi
  linarith

end BeliOrderLE

end Bong
