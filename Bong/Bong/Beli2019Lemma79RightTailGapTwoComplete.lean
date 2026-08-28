/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddFullRank
import Bong.Bong.Beli2019Lemma79RightTailGapTwoCase
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIComplete
import Bong.Bong.Beli2019Lemma79RightTailLastGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete type I

The full-rank odd-prefix theorem removes the final index restriction from
the gap-two numerical estimate.  The strict-beta and half-gap branches then
complete gap two at every admissible index.  Finally the structural last-gap
alternative joins this result to the previously completed gap-one branch.
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
-- Both parity branches expand the propagated prefix identities and their
-- domination arguments; the odd branch may also use full-rank transport.
/-- The strict type-I gap-two beta estimate at every admissible index. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_strict_beta_bound_complete
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hmixedStrict :
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
        a.truncatedPrefixDefect c 1 i.val i.val) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  have hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i) := by
    have hstrict := caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
      a c i (b.alphaValue (caseEightLastAlphaIndex i)) hmixedStrict
    simpa only [caseEightLastAlphaIndex] using hstrict
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hiTwo : 2 <= i.val := by
      rcases hiEven with ⟨d, hd⟩
      omega
    have hself :=
      beli2019Lemma79_typeI_caseEight_gapTwo_even_comparisonPrefixDefect
        a b c D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast
          hiEven hmixedStrict
    exact beli2019Lemma79_typeI_caseEight_gapTwo_even_beta_bound
      a b c D hfirst hgapTwo hlast hnorm i hafter H hiEven hiTwo hself hprefix
  · have htarget :=
      beli2019Lemma79_typeI_caseEight_gapTwo_targetPrefixDefect_at_oddIndex_complete
        a b D hfirst hgapTwo hlast horder hdefect i hafter H hstrictLast hiOdd
    exact beli2019Lemma79_typeI_caseEight_gapTwo_odd_beta_bound
      a b c D hfirst hgapTwo hlast hnorm i hafter H hiOdd htarget hprefix

/-- The strict type-I gap-two case, with no terminal restriction or residual
beta callback. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapTwo_strict
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
    (hafter : D.profile.last + 1 <= i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hlast : D.profile.last < n + 1 := by
    have hi := i.lt_large
    omega
  have hsuffix := beli2019Lemma79_typeI_caseEight_suffix
    a b D i (by omega)
  apply beli2019Lemma79_ii_caseEight_of_strict_beta_bound
    a b c hdefectAB hdefectAC i hsuffix
  intro hmixedStrict
  obtain ⟨H, hprefix⟩ :=
    beli2019Lemma79_typeI_caseEight_strictData_complete
      a b c D horderAB hdefectAB htotal i hafter hnotAttains hmixedStrict
  exact beli2019Lemma79_typeI_caseEight_gapTwo_strict_beta_bound_complete
    a b c D hfirst hgapTwo hlast horderAB hdefectAB hnorm i hafter H
      hprefix hmixedStrict

/-- The complete type-I gap-two branch, including the half-gap exit and the
full-rank endpoint. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapTwo
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
    (hafter : D.profile.last + 1 <= i.val)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hattains : b.alphaValue (caseEightLastAlphaIndex i) =
      b.halfGapValue (caseEightLastAlphaIndex i)
  · apply beli2019Lemma79_ii_caseEight_of_finalBeta_attainsHalfGap
      a b c horderBC hdefectAB hdefectAC i
    · exact beli2019Lemma79_typeI_caseEight_suffix
        a b D i (by omega)
    · simpa only [caseEightLastAlphaIndex] using hattains
  · exact beli2019Lemma79_ii_typeI_caseEight_gapTwo_strict
      a b c D hfirst hnorm horderAB hdefectAB hdefectAC htotal i
        hafter hattains hgapTwo

/-- Lemma 7.9(ii), case 8, in type I, with the last-gap alternative fully
discharged. -/
theorem beli2019Lemma79_ii_typeI_caseEight
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
    (hafter : D.profile.last + 1 <= i.val) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  rcases beli2019Lemma79_typeI_caseEight_lastGap a b D with
    hgapOne | hgapTwo
  · exact beli2019Lemma79_ii_typeI_caseEight_gapOne
      a b c D hfirst hnorm horderAB horderBC hdefectAB hdefectAC htotal
        i hafter hgapOne
  · exact beli2019Lemma79_ii_typeI_caseEight_gapTwo
      a b c D hfirst hnorm horderAB horderBC hdefectAB hdefectAC htotal
        i hafter hgapTwo

end BONG.GoodBONG

end Bong
