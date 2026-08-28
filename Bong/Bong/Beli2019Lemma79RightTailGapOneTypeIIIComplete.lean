/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenComplete
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddComplete
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIOverlapComplete

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete type-III gap one

The nonoverlapping branch is assembled directly from the strict-tail data
and the even/odd beta estimates.  Splitting on the final half-gap closes its
nonstrict alternative.  A final split on the central order gap combines it
with the already completed overlapping type-II/III branch.
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
-- The case split elaborates two long concrete beta-bound derivations.
/-- The strict nonoverlapping type-III gap-one branch, with no residual
local-law or numerical callback. -/
theorem beli2019Lemma79_ii_typeIII_caseEight_gapOne_strict_of_nonoverlap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
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
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hlast : D.outer.last < n + 1 := by
    have hi := i.lt_large
    omega
  have hsuffix := beli2019Lemma79_typeIII_caseEight_suffix
    a b D i (by omega)
  apply beli2019Lemma79_ii_caseEight_of_strict_beta_bound
    a b c hdefectAB hdefectAC i hsuffix
  intro hmixedStrict
  obtain ⟨H, hprefix⟩ :=
    beli2019Lemma79_typeIII_caseEight_strictData_complete
      a b c D horderAB hdefectAB htotal i hafter hnotAttains hmixedStrict
  have hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i) := by
    simpa only [caseEightLastAlphaIndex] using
      caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
        a c i (b.alphaValue (caseEightLastAlphaIndex i)) hmixedStrict
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact
      beli2019Lemma79_typeIII_nonoverlap_even_beta_bound
        a b c D hfirst hdefectAB hnotOverlap hinitial hnorm hlast i hafter
          H hstrictLast hprefix hiEven hmixedStrict
  · exact
      beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound
        a b c D hfirst hdefectAB hnotOverlap hinitial hnorm hlast i hafter
          H hstrictLast hprefix hiOdd

/-- The complete nonoverlapping type-III gap-one branch, including the
half-gap exit. -/
theorem beli2019Lemma79_ii_typeIII_caseEight_gapOne_of_nonoverlap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
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
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hattains : b.alphaValue (caseEightLastAlphaIndex i) =
      b.halfGapValue (caseEightLastAlphaIndex i)
  · apply beli2019Lemma79_ii_caseEight_of_finalBeta_attainsHalfGap
      a b c horderBC hdefectAB hdefectAC i
    · exact beli2019Lemma79_typeIII_caseEight_suffix
        a b D i (by omega)
    · simpa only [caseEightLastAlphaIndex] using hattains
  · exact
      beli2019Lemma79_ii_typeIII_caseEight_gapOne_strict_of_nonoverlap
        a b c D hfirst hnotOverlap hinitial hnorm horderAB hdefectAB
          hdefectAC htotal i hafter hattains

/-- The complete type-III gap-one case, both at and away from the
overlapping type-II boundary. -/
theorem beli2019Lemma79_ii_typeIII_caseEight_gapOne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap (Fin.mk 0 (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hoverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) = 1
  · exact
      beli2019Lemma79_ii_typeIII_caseEight_gapOne_of_overlap
        a b c D hfirst hoverlap hnorm horderAB horderBC hdefectAB
          hdefectAC htotal i hafter
  · exact
      beli2019Lemma79_ii_typeIII_caseEight_gapOne_of_nonoverlap
        a b c D hfirst hoverlap hinitial hnorm horderAB horderBC hdefectAB
          hdefectAC htotal i hafter

end BONG.GoodBONG

end Bong
