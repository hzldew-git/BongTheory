/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIOpposite

/-!
# Beli (2019), Lemma 7.9(ii), case 6: complete type-III assembly

The current target order is congruent modulo two either to the preceding
third order or to that order plus one.  The first alternative was the easy
same-current-parity profile; the second is the completed hard type-III
branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The complete nonoverlapping type-III second-parity branch of case 6. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hcomparison : Odd
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases modEq_two_or_add_one
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) with hsame | hopposite
  · exact beli2019Lemma79_typeIII_caseSix_secondParity_sameCurrentParity
      a b c D hfirst hdefect hnotOverlap hnorm i hright hthroughLast
        heven hcomparison hsame
  · exact
      beli2019Lemma79_typeIII_caseSix_secondParity_oppositeCurrentParity
        a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
          hnorm i hright hthroughLast heven hopposite

end BONG.GoodBONG

end Bong
