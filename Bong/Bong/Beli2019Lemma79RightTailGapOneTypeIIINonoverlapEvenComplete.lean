/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenEquality

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete even type-III branch

This assembles the exact comparison prefix, capped domination, the
integral/nonintegral strict split, and the equality parity argument.  It
completes the even part of lines 5812--5838 in the nonoverlapping type-III
case.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
/-- The complete beta estimate at an even coordinate in a nonoverlapping
type-III gap-one tail. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_beta_bound
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap (Fin.mk 0 (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hiEven : Even i.val)
    (hmixedStrict :
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
        a.truncatedPrefixDefect c 1 i.val i.val) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let centralQ : Rat :=
    ((b.order
          (Fin.mk D.outer.transition.lastZero (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) -
        a.order
          (Fin.mk (D.outer.transition.lastZero + 1) (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) : Int) : Rat)
  have hiTwo : 2 <= i.val := by
    have hlastOdd := beli2019Lemma79_typeIII_last_odd a b D hfirst
    rcases hlastOdd with ⟨d, hd⟩
    omega
  have hself :=
    beli2019Lemma79_typeIII_nonoverlap_even_comparisonPrefixDefect
      a b c D hfirst hdefect hnotOverlap hinitial hlast i hafter H
        hstrictLast hiEven hmixedStrict
  rcases
      beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_or_exists_lowWitness
        a b c D hfirst hnorm hlast i hafter H hstrictLast hiEven hiTwo
          hself with
    hdone | ⟨j, hjEven, hjBefore, hjOrder, hjPair, hjCoefficient⟩
  · exact hdone
  · by_cases hstrict :
        ((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) < centralQ
    · by_cases hintegral : IsRationalInteger
          (c.alphaValue (evenTargetPreviousAlphaIndex i))
      · apply
          beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_strict_integral
            a b c D hlast i hafter H hstrictLast hiTwo j hjOrder
              (by exact_mod_cast hstrict) hintegral
      · exact
          beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_nonintegral
            a b c D hfirst hdefect hnotOverlap hnorm hlast i hafter H
              hstrictLast hiEven hiTwo hintegral
    · have heq :
          ((c.order j.castSucc -
              c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) = centralQ :=
        le_antisymm (by simpa only [centralQ] using hjCoefficient)
          (le_of_not_gt hstrict)
      have hodd :=
        beli2019Lemma79_typeIII_nonoverlap_even_equality_primaryProduct_odd
          a b c D hfirst hdefect hnotOverlap hnorm hlast i hafter H
            hstrictLast hiEven hiTwo hself j hjEven hjBefore hjOrder hjPair
              (by simpa only [centralQ] using heq)
      exact
        beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_equality
          a b c D hlast i hafter H hstrictLast hprefix j hjOrder
            (by simpa only [centralQ] using heq) hodd

end BONG.GoodBONG

end Bong
