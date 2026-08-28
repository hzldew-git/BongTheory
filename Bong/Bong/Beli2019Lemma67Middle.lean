/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Outer

/-!
# Beli (2019), Lemma 6.7: propagation across the middle interval

Once the first common middle entry is known, the cross-order alternative of
Lemma 6.5 propagates that value through every common entry before the right
transition.  The proof is the induction in the final third of Lemma 6.7:
two-step monotonicity supplies the lower bound, and either branch of the
cross-order alternative supplies the upper bound.
-/

namespace Bong

namespace BeliOrderLE

/-- The middle plateau in the type-II branch, conditional only on its first
entry and the already-proved Lemma 6.5 cross alternatives. -/
theorem middle_eq_leftTarget_of_seed_of_cross {n : Nat}
    {x y : BeliOrderSequence n Int}
    (T : PrefixGapTransitionConsequences x y)
    (hseed : x.entryOrZero (T.lastZero + 1) =
      y.entryOrZero T.lastZero)
    (hcross : ∀ p, T.lastZero + 1 < p → p + 1 < T.firstTwo →
      x.entryOrZero p ≤ y.entryOrZero (p - 1) ∨
        x.entryOrZero p + x.entryOrZero (p + 1) ≤
          y.entryOrZero (p - 2) + y.entryOrZero (p - 1)) :
    ∀ k, T.lastZero < k → k + 1 < T.firstTwo →
      x.entryOrZero k = y.entryOrZero T.lastZero := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hlast hkFirst
      by_cases hbase : k = T.lastZero + 1
      · simpa only [hbase] using hseed
      · have hkLarge : T.lastZero + 1 < k := by omega
        have hprevious := ih (k - 1) (by omega)
          (by omega) (by omega)
        have hpreviousMiddle := T.middle (k - 1) (by omega) (by omega)
        have hyPrevious :
            y.entryOrZero (k - 1) = y.entryOrZero T.lastZero := by
          rw [← hpreviousMiddle]
          exact hprevious
        have hcurrentMiddle := T.middle k hlast hkFirst
        have hupper :
            x.entryOrZero k ≤ y.entryOrZero T.lastZero := by
          rcases hcross k hkLarge hkFirst with hdirect | hpair
          · exact hdirect.trans_eq hyPrevious
          · have hxMonotone := x.entryOrZero_le_of_evenGap
                (k - 1) (k + 1) (by omega)
                (by have := T.firstTwo_le_rank; omega)
                (by refine ⟨1, ?_⟩; omega)
            have hyEarlier :
                y.entryOrZero (k - 2) =
                  y.entryOrZero T.lastZero := by
              by_cases hfirstStep : k = T.lastZero + 2
              · have hindex : k - 2 = T.lastZero := by omega
                rw [hindex]
              · have hearlier := ih (k - 2) (by omega)
                  (by omega) (by omega)
                have hearlierMiddle := T.middle (k - 2)
                  (by omega) (by omega)
                rw [← hearlierMiddle]
                exact hearlier
            omega
        have hlower :
            y.entryOrZero T.lastZero ≤ x.entryOrZero k := by
          by_cases hfirstStep : k = T.lastZero + 2
          · have hyMonotone := y.entryOrZero_le_of_evenGap
                T.lastZero k (by omega)
                (by have := T.firstTwo_le_rank; omega)
                (by refine ⟨1, ?_⟩; omega)
            rw [hcurrentMiddle]
            exact hyMonotone
          · have hearlier := ih (k - 2) (by omega)
                (by omega) (by omega)
            have hxMonotone := x.entryOrZero_le_of_evenGap
              (k - 2) k (by omega)
              (by have := T.firstTwo_le_rank; omega)
              (by refine ⟨1, ?_⟩; omega)
            exact hearlier ▸ hxMonotone
        exact le_antisymm hupper hlower

end BeliOrderLE

end Bong
