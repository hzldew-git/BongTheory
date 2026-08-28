/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderReconstruction

/-!
# Beli (2019), Corollary 5.9(i): the second-order criterion

This is the exact order-sequence core of Corollary 5.9(i).  The second order
of the original good BONG is at most the first order of the projected tail.
Equality is equivalent to equality of every tail order.  The ideal-theoretic
translation is handled separately, using that the first vector of a BONG
generates the norm ideal of its lattice.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- The order content of Corollary 5.9(i), in zero-based indexing. -/
structure SecondOrderCriterion {n : Nat}
    (x y : BeliOrderSequence n Gamma) : Prop where
  second_le : y.entryOrZero 1 ≤ x.entryOrZero 1
  second_eq_iff_tail_eq :
    x.entryOrZero 1 = y.entryOrZero 1 ↔
      ∀ q : Nat, 1 ≤ q → q < n →
        x.entryOrZero q = y.entryOrZero q

end BeliOrderSequence

namespace BeliOrderLE

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

/-- Beli (2019), Corollary 5.9(i), order-sequence form. -/
theorem secondOrderCriterion {n : Nat}
    {x y : BeliOrderSequence n Gamma} (h : BeliOrderLE x y)
    (k : Nat) (hn : 2 ≤ n)
    (hplateau : y.IsMaximalInitialOddPlateau k)
    (htail : x.suffixSum 1 = y.suffixSum 1) :
    BeliOrderSequence.SecondOrderCriterion x y := by
  have hprofile := h.normGeneratorOrderProfile k hplateau htail
  have hsecond : y.entryOrZero 1 ≤ x.entryOrZero 1 := by
    by_cases hk : k = 0
    · subst k
      exact (hprofile.stable_after 1 (by omega) (by omega)).ge
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      exact hprofile.target_le_source 1 (by omega) (by omega)
        ⟨0, by omega⟩
  refine ⟨hsecond, ?_⟩
  constructor
  · intro heq
    by_cases hk : k = 0
    · subst k
      intro q hq _
      exact hprofile.stable_after q (by omega) (by assumption)
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      exact hprofile.stable_from_eq 1 (by omega) (by omega)
        ⟨0, by omega⟩ heq
  · intro hall
    exact hall 1 (by omega) (by omega)

end BeliOrderLE

end Bong
