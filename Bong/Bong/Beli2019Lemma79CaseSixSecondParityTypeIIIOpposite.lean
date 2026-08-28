/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIBoundaryAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 6: opposite type-III parity

This assembles the complete hard type-III branch.  A mixed prefix no larger
than the central value is handled by the primary candidate.  Otherwise
Lemma 7.8 and sharp multiplication identify the third self-prefix, after
which domination gives either the strict-order branch or the completed
boundary-witness branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The complete opposite-current-parity branch for nonoverlapping type III. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_oppositeCurrentParity
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
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1)) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hmixed : b.truncatedPrefixDefect c (-1)
      (i.val + 1) (i.val - 1) ≤
    ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
        a.orderSequence.entryOrZero
          (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ)
  · exact beli2019Lemma79_typeIII_caseSix_secondParity_of_mixed_le
      a b c D hfirst hdefect hnotOverlap hnorm i hright hthroughLast
        heven horders hmixed
  · have hmixedStrict :
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) : WithTop ℚ) <
          b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) :=
      lt_of_not_ge hmixed
    have hthird :=
      beli2019Lemma79_typeIII_caseSix_thirdPrefixDefect_eq_mixedShift
        a b c D hfirst hlast horder hdefect htotal hnotOverlap hinitial
          i hright hthroughLast heven hmixedStrict
    rcases beli2019Lemma79_typeIII_caseSix_secondParity_or_boundaryWitness
        a b c D hfirst hnorm i hright hthroughLast heven hthird with
      hdone | hboundary
    · exact hdone
    · exact beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryWitness
        a b c D hfirst hdefect hnotOverlap i hright hthroughLast heven
          horders hthird hboundary

end BONG.GoodBONG

end Bong
