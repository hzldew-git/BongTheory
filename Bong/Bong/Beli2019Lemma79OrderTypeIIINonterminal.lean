/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIITerminalSwitch

/-!
# Beli (2019), Lemma 7.9(i): nonterminal type-III coordinates

The left outer interval, the elementary alternating right class, and the
hard even-distance class cover every coordinate with a successor through
the last difference of a normalized type-III profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at every nonterminal coordinate of the normalized
type-III branch. -/
theorem beli2019Lemma79_i_typeIII_nonterminal
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hlastK : k ≤ D.outer.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hleft : k ≤ D.outer.transition.lastZero
  · exact a.beli2019Lemma79_i_typeIII_leftOuter
      b c D hfirst hac hnorm k hk hleft
  · have hright : D.outer.transition.firstTwo - 1 ≤ k := by
      rw [D.adjacent]
      omega
    rcases Nat.even_or_odd
        (k - (D.outer.transition.firstTwo - 1)) with heven | hodd
    · by_cases hdirect : b.orderSequence.entry k hk ≤
          c.orderSequence.entry k hk
      · exact Or.inl hdirect
      · have hcurrent : c.orderSequence.entryOrZero k <
            b.orderSequence.entryOrZero k := by
          rw [b.orderSequence.entryOrZero_of_lt hk,
            c.orderSequence.entryOrZero_of_lt hk]
          exact lt_of_not_ge hdirect
        rcases heven with ⟨d, hd⟩
        by_cases hbeforeLast : k < D.outer.last
        · rcases D.outer.right_even_distance with ⟨e, he⟩
          have hkNextNext : k + 2 < n + 2 := by
            have hlastBound := D.outer.lastDifference.bound
            omega
          have hpair := a.lemma79_typeIII_interiorPair
            b c D hfirst hdefectAB hdefectAC hnotOverlap hinitial hnorm
              k hk hkNext hkNextNext hright hbeforeLast
                ⟨d, hd⟩ hcurrent
          exact Or.inr ⟨by
            have hseparated := D.outer.transition.separated
            omega, hkNext, by
              simpa only [BeliOrderSequence.entryOrZero_of_lt _ hk,
                BeliOrderSequence.entryOrZero_of_lt _ hkNext,
                BeliOrderSequence.entryOrZero_of_lt _
                  (show k - 1 < n + 2 by
                    have hseparated := D.outer.transition.separated
                    omega)] using hpair⟩
        · have hkLast : k = D.outer.last := by omega
          exact a.beli2019Lemma79_i_typeIII_nonoverlap_terminalSwitch
            b c D hfirst hdefectAB hdefectAC hnotOverlap hinitial hnorm
              k hk hkNext hkLast hright ⟨d, hd⟩
    · exact a.beli2019Lemma79_i_typeIII_rightAlternating
        b c D hac k hk hright hlastK hodd

end BONG.GoodBONG

end Bong
