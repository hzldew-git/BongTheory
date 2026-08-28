/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIEndpointStrict

/-!
# Beli (2019), Lemma 7.9(ii), case 6: boundary-witness assembly

For the sole boundary witness `T_j = R + 1`, the final right endpoint is
either equal to the endpoint at `j` or strictly smaller.  Equality is the
odd-adjacent-pair branch; strictness is completed by the integral versus
nonintegral split for the final alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Every exact type-III boundary witness satisfies condition 2.1(ii). -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryWitness
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (horders : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1) + 1))
    (hthird : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ))
    (H : Lemma79CaseSixTypeIIIBoundaryWitness a b c D i) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases H with ⟨j, hjEven, hjlt, hjDefect, _hjCoefficient, hjOrder⟩
  have hjLast : j ≤ evenTargetPreviousAlphaIndex i := by
    change j.val ≤ (evenTargetPreviousAlphaIndex i).val
    simp only [evenTargetPreviousAlphaIndex]
    omega
  have hendpointLe := c.alphaRightEndpoint_antitone hjLast
  by_cases heq : c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i)
  · exact
      beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_eq
        a b c D hfirst hdefect hnotOverlap i hright hthroughLast heven
          horders hthird j hjlt hjOrder heq
  · have hendpointLt :
        c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i) <
          c.alphaRightEndpoint j :=
      lt_of_le_of_ne hendpointLe (Ne.symm heq)
    by_cases hintegral : IsRationalInteger
        (c.alphaValue (evenTargetPreviousAlphaIndex i))
    · exact
        beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_lt_of_integral
          a b c D i hright hthroughLast heven j hjlt hjDefect hjOrder
            hendpointLt hintegral
    · exact
        beli2019Lemma79_typeIII_caseSix_secondParity_of_boundaryEndpoint_lt_of_nonintegral
          a b c D i hright hthroughLast heven j hjlt hjDefect hjOrder
            hendpointLt hintegral

end BONG.GoodBONG

end Bong
