/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIITypes
import Bong.Bong.Beli2019Lemma79RightTailHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: completed type-I/type-II gap one

The concrete evidence of the preceding file discharges the last callback
in the strict-tail assembly.  Splitting on whether the final beta attains
its half-gap then completes the entire gap-one branch for types I and II.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The strict type-I gap-one branch with no residual evidence argument. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapOne_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  apply beli2019Lemma79_ii_typeI_caseEight_gapOne_of_evidence
    a b c D horderAB hdefectAB hdefectAC htotal i hafter
      hnotAttains hgapOne
  intro _ H hprefix hstrictLast
  exact beli2019Lemma79_typeI_caseEight_gapOne_evidence
    a b c D hfirst hnorm i hafter hgapOne H hprefix hstrictLast

/-- The strict type-II gap-one branch with no residual evidence argument. -/
theorem beli2019Lemma79_ii_typeII_caseEight_gapOne_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
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
  apply beli2019Lemma79_ii_typeII_caseEight_gapOne_of_evidence
    a b c D horderAB hdefectAB hdefectAC htotal i hafter hnotAttains
  intro _ H hprefix hstrictLast
  exact beli2019Lemma79_typeII_caseEight_gapOne_evidence
    a b c D hfirst hnorm i hafter H hprefix hstrictLast

/-- The complete type-I gap-one branch, including the half-gap exit. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapOne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 ≤ i.val)
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hattains : b.alphaValue (caseEightLastAlphaIndex i) =
      b.halfGapValue (caseEightLastAlphaIndex i)
  · apply beli2019Lemma79_ii_caseEight_of_finalBeta_attainsHalfGap
      a b c horderBC hdefectAB hdefectAC i
    · exact beli2019Lemma79_typeI_caseEight_suffix
        a b D i (by omega)
    · simpa only [caseEightLastAlphaIndex] using hattains
  · exact beli2019Lemma79_ii_typeI_caseEight_gapOne_strict
      a b c D hfirst hnorm horderAB hdefectAB hdefectAC htotal i
        hafter hattains hgapOne

/-- The complete type-II gap-one branch, including the half-gap exit. -/
theorem beli2019Lemma79_ii_typeII_caseEight_gapOne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
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
    · exact beli2019Lemma79_typeII_caseEight_suffix
        a b D i (by omega)
    · simpa only [caseEightLastAlphaIndex] using hattains
  · exact beli2019Lemma79_ii_typeII_caseEight_gapOne_strict
      a b c D hfirst hnorm horderAB hdefectAB hdefectAC htotal i
        hafter hattains

end BONG.GoodBONG

end Bong
