/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIBoundary
import Bong.Bong.Beli2019Lemma79OrderTypeIIMiddle
import Bong.Bong.Beli2019Lemma79OrderTypeIITerminal

/-!
# Beli (2019), Lemma 7.9(i): complete type-II branch

The left outer interval, constant middle, right predecessor, alternating
right interval, hard right parity class, and full-rank endpoint together
cover every coordinate through the last difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- Condition 2.1(i) at every altered coordinate in the type-II branch of
Lemma 7.9. -/
theorem beli2019Lemma79_i_typeII
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefect : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hlast : k ≤ D.outer.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hleft : k ≤ D.outer.transition.lastZero
  · exact a.beli2019Lemma79_i_typeII_leftOuter
      b c D hfirst hac hnorm k hk hleft
  · have hleftStrict : D.outer.transition.lastZero < k := by omega
    by_cases hmiddle : k + 2 < D.outer.transition.firstTwo
    · exact a.beli2019Lemma79_i_typeII_constantMiddle
        b c D hac k hleftStrict hmiddle
    · by_cases htransition : k + 2 = D.outer.transition.firstTwo
      · exact a.beli2019Lemma79_i_typeII_rightPredecessor
          b c D hfirst hdefect hnorm k htransition
      · have hright : D.outer.transition.firstTwo - 1 ≤ k := by
          have hseparated := D.outer.transition.separated
          omega
        rcases Nat.even_or_odd
            (k - (D.outer.transition.firstTwo - 1)) with heven | hodd
        · by_cases hkNext : k + 1 < n + 2
          · exact a.beli2019Lemma79_i_typeII_rightEven
              b c D hfirst hdefect hnorm k hk hkNext hright hlast heven
          · left
            apply a.beli2019Lemma79_i_typeII_terminal
              b c D hfirst hnorm k (by omega) hright hlast heven
        · exact a.beli2019Lemma79_i_typeII_rightAlternating
            b c D hac k hk hright hlast hodd

end BONG.GoodBONG

end Bong
