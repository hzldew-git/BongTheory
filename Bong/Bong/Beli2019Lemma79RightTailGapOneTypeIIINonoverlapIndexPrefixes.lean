/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapTarget
import Bong.Bong.Beli2019Lemma79RightTailGapOneAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 8: nonoverlap prefixes at `i`

The propagation theorems are rewritten at the representation index used in
the paper.  At an even index both prefixes of length `i` have the central
type-III defect; at an odd nonterminal index the target prefix of length
`i + 1` has it.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At an even index, the source prefix of length `i` has the central
nonoverlapping type-III defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_at_evenIndex
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
    (hiEven : Even i.val) :
    a.truncatedPrefixDefect a ((-1) ^ (i.val / 2)) 0 i.val =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  exact beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect
    a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictLast
      i.val hafter (by
        simp only [caseEightLastAlphaIndex_val]
        have hiPos := i.pos
        omega) hiEven

/-- At an even index, the target prefix of length `i` has the same central
nonoverlapping type-III defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_evenIndex
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
    (hiEven : Even i.val) :
    b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  exact beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect
    a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictLast
      i.val hafter (by
        simp only [caseEightLastAlphaIndex_val]
        have hiPos := i.pos
        omega) hiEven

/-- At an odd nonterminal index, the target prefix of length `i + 1` has
the central nonoverlapping type-III defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_oddIndex
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
    (hiOdd : Odd i.val) (hiNonterminal : i.val < n + 1) :
    b.truncatedPrefixDefect b ((-1) ^ ((i.val + 1) / 2)) 0
        (i.val + 1) =
      (((b.order ⟨D.outer.transition.lastZero, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ -
          a.order ⟨D.outer.transition.lastZero + 1, by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega⟩ : Int) : Rat) : WithTop Rat) := by
  have hfirstTail :
      (⟨D.outer.last, hlast⟩ : Fin (n + 1)) ≤
        caseEightLastAlphaIndex i := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hparity : Odd
      ((caseEightLastAlphaIndex i).val - D.outer.last) := by
    rcases beli2019Lemma79_typeIII_last_odd a b D hfirst with ⟨u, hu⟩
    rcases hiOdd with ⟨r, hr⟩
    refine ⟨r - u - 1, ?_⟩
    simp only [caseEightLastAlphaIndex_val]
    omega
  have hraw :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_endpoint
      a b D hfirst hdefect hnotOverlap hinitial hlast H hfirstTail
        hstrictLast (by
          simp only [caseEightLastAlphaIndex_val]
          omega) hparity
  have hlength : (caseEightLastAlphaIndex i).val + 2 =
      i.val + 1 := by
    simp only [caseEightLastAlphaIndex_val]
    have hiPos := i.pos
    omega
  rw [hlength] at hraw
  exact hraw

end BONG.GoodBONG

end Bong
