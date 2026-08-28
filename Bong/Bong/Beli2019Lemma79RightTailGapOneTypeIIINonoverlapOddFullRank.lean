/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapIndexPrefixes
import Bong.Bong.Beli2019Lemma78TargetPropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd full-rank type-III prefix

The endpoint propagation used at odd indices needs a target alpha after the
strict tail and is therefore nonterminal.  The corresponding source prefix,
however, is available at full rank.  Full-rank self-prefix invariance then
transfers that source identity to the target and removes the artificial
nonterminal restriction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At every odd current index, including the terminal one, the source
prefix of length `i + 1` has the central nonoverlapping type-III defect. -/
theorem beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_at_oddIndex
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val) :
    a.truncatedPrefixDefect a ((-1) ^ ((i.val + 1) / 2)) 0
        (i.val + 1) =
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat) := by
  have hfirstTail :
      (Fin.mk D.outer.last hlast : Fin (n + 1)) ≤
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
  rcases hparity with ⟨pairs, hpairs⟩
  have htailEq :
      (caseEightLastAlphaIndex i).val =
        D.outer.last + 2 * pairs + 1 := by
    change D.outer.last ≤ (caseEightLastAlphaIndex i).val at hfirstTail
    omega
  have hraw :=
    beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_succ
      a b D hfirst hdefect hnotOverlap hinitial hlast H hstrictLast pairs
        (by omega)
  have hlength :
      D.outer.last + 1 + 2 * (pairs + 1) = i.val + 1 := by
    simp only [caseEightLastAlphaIndex_val] at htailEq
    have hiPos := i.pos
    omega
  rw [hlength] at hraw
  simpa only [hlength] using hraw

/-- The odd target-prefix identity at every index.  The terminal case is
obtained from the source identity and full-rank self-prefix invariance. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_oddIndex_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
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
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val) :
    b.truncatedPrefixDefect b ((-1) ^ ((i.val + 1) / 2)) 0
        (i.val + 1) =
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat) := by
  by_cases hiNonterminal : i.val < n + 1
  · exact
      beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_oddIndex
        a b D hfirst hdefect hnotOverlap hinitial hlast i hafter H
          hstrictLast hiOdd hiNonterminal
  · have hiTerminal : i.val = n + 1 := by
      have hi := i.lt_large
      omega
    have hsource :=
      beli2019Lemma79_typeIII_nonoverlap_sourcePrefixDefect_at_oddIndex
        a b D hfirst hdefect hnotOverlap hinitial hlast i hafter H
          hstrictLast hiOdd
    have hlength : i.val + 1 = n + 2 := by omega
    rw [hlength]
    rw [a.truncatedPrefixDefect_self_full_eq b
      ((-1) ^ ((n + 2) / 2))]
    simpa only [hlength] using hsource

end BONG.GoodBONG

end Bong
