/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddSeparated
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddEquality

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete odd type-III branch

At an odd index the comparison prefix is either separated
from the central type-III defect, which gives the beta estimate directly,
or it equals that defect.  In the latter case capped domination gives a
high-order exit or an exact low witness.  Strict low witnesses are closed
by the integral/nonintegral split, while equality is impossible by the
prefix-parity argument.
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
-- The nested domination and parity branches need a larger elaboration budget.
/-- The complete beta estimate at an odd coordinate in a
nonoverlapping type-III gap-one tail. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound
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
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hiOdd : Odd i.val) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
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
  by_cases hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        (centralQ : WithTop Rat)
  · rcases
        beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_or_exists_lowWitness
          a b c D hfirst hnorm hlast i hafter H hstrictLast hiOdd
            (by simpa only [centralQ] using hcomparison) with
      hdone | ⟨j, hjEven, hjBefore, hjOrder, hjPair, hjCoefficient⟩
    · exact hdone
    · by_cases hstrict :
          ((c.order j.castSucc -
              c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) < centralQ
      · by_cases hintegral : IsRationalInteger
            (c.alphaValue (evenTargetPreviousAlphaIndex i))
        · have hiTwo : 2 ≤ i.val := by
            have hlastOdd := beli2019Lemma79_typeIII_last_odd a b D hfirst
            rcases hlastOdd with ⟨d, hd⟩
            omega
          exact
            beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_strict_integral
              a b c D hlast i hafter H hstrictLast hiTwo j hjOrder
                (by exact_mod_cast hstrict) hintegral
        · exact
            beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_of_nonintegral
              a b c D hlast i hafter H hstrictLast j hjOrder
                (by exact_mod_cast hstrict) hintegral
      · have heq :
            ((c.order j.castSucc -
                c.order (evenTargetPreviousIndex i) : Int) : Rat) +
              c.alphaValue (evenTargetPreviousAlphaIndex i) = centralQ :=
          le_antisymm (by simpa only [centralQ] using hjCoefficient)
            (le_of_not_gt hstrict)
        exact False.elim
          (beli2019Lemma79_typeIII_nonoverlap_odd_domination_equality_false
            a b c D hfirst hdefect hnotOverlap hnorm hlast i hafter H
              hstrictLast hiOdd hprefix
              (by simpa only [centralQ] using hcomparison) j hjEven hjBefore
              hjOrder hjPair (by simpa only [centralQ] using heq))
  · exact
      beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_of_comparisonPrefix_ne
        a b c D hfirst hdefect hnotOverlap hinitial hnorm hlast i hafter H
          hstrictLast hprefix hiOdd
          (by simpa only [centralQ] using hcomparison)

end BONG.GoodBONG

end Bong
