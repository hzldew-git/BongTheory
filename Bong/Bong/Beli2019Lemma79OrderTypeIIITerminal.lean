/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal

/-!
# Beli (2019), Lemma 7.9(i): the terminal type-III coordinate

For a normalized full-span type-III profile the last difference is `n + 1`,
whereas condition 2.1(i) stops at coordinate `n`. Thus its terminal
coordinate is the odd-distance right-alternating class already contained in
the uniform type-III proof. This file records that endpoint explicitly.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at the final admissible coordinate of a normalized
full-span type-III profile. -/
theorem beli2019Lemma79_i_typeIII_terminal
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.orderSequence.entry n (by omega) ≤
        c.orderSequence.entry n (by omega) ∨
      ∃ (hn0 : 0 < n) (hnNext : n + 1 < n + 2),
        b.orderSequence.entry n (by omega) +
            b.orderSequence.entry (n + 1) hnNext ≤
          c.orderSequence.entry (n - 1) (by omega) +
            c.orderSequence.entry n (by omega) := by
  exact a.beli2019Lemma79_i_typeIII_nonterminal
    b c D hfirst hac hdefectAB hdefectAC hnotOverlap
      hinitial hnorm n (by omega) (by omega) (by rw [hlast]; omega)

end BONG.GoodBONG

end Bong
