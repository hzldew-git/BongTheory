/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddSeparated
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenComparison

/-!
# Beli (2019), Lemma 7.9(ii), case 8: even type-III comparison prefix

At an even index, the source and target self-prefixes have the central
defect.  The target equality puts that value below `beta_i`; the strict
case-8 mixed defect is larger.  Sharp multiplication therefore gives the
same exact value for the comparison self-prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- In the strict even nonoverlapping type-III branch, the comparison
self-prefix has exact defect `R - S + 2`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_comparisonPrefixDefect
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
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
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiEven : Even i.val)
    (hmixedStrict :
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
        a.truncatedPrefixDefect c 1 i.val i.val) :
    c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  let central : WithTop Rat :=
    (((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : Rat) : WithTop Rat)
  have hsource :=
    beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_at_evenIndex
      a b D hfirst hdefect hnotOverlap hinitial hlast i hafter H
        hstrictLast hiEven
  have htarget :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_evenIndex
      a b D hfirst hdefect hnotOverlap hinitial hlast i hafter H
        hstrictLast hiEven
  have hcap := b.truncatedPrefixDefect_le_rightCap
    b ((-1) ^ (i.val / 2)) 0 i.val
  have hcapValue : b.prefixAlphaCap i.val =
      (b.alphaValue last : WithTop Rat) := by
    have hraw := b.prefixAlphaCap_of_internal i.pos i.lt_large
    simpa only [last, caseEightLastAlphaIndex] using hraw
  have hcentralLe : central ≤ (b.alphaValue last : WithTop Rat) := by
    rw [hcapValue] at hcap
    rw [htarget] at hcap
    simpa only [central, last] using hcap
  have hstrict : central <
      a.truncatedPrefixDefect c 1 i.val i.val :=
    hcentralLe.trans_lt (by simpa only [last] using hmixedStrict)
  exact truncatedPrefixDefect_comparisonSelf_eq_of_sourceSelf_lt_mixed
    a c ((-1) ^ (i.val / 2)) i.val central
      (by simpa only [central] using hsource) hstrict

end BONG.GoodBONG

end Bong
