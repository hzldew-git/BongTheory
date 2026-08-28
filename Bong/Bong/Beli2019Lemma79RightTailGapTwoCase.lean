/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoStrict
import Bong.Bong.Beli2019Lemma79RightTailStrictComplete
import Bong.Bong.Beli2019Lemma79RightTailHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the nonterminal gap-two branch

The complete strict-tail package supplies the beta profile and the prefix
parity needed by the numerical gap-two estimate.  The generic strict-beta
assembly then proves condition (ii).  Splitting on whether the final beta
attains its half-gap also restores the easy exit and completes the entire
type-I gap-two branch away from the terminal representation index.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The strict type-I gap-two branch, assembled directly from the paper's
representation hypotheses. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapTwo_strict_nonterminal
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
    (hiNonterminal : i.val < n + 1)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hlast : D.profile.last < n + 1 := by omega
  have hsuffix := beli2019Lemma79_typeI_caseEight_suffix
    a b D i (by omega)
  apply beli2019Lemma79_ii_caseEight_of_strict_beta_bound
    a b c hdefectAB hdefectAC i hsuffix
  intro hmixedStrict
  obtain ⟨H, hprefix⟩ :=
    beli2019Lemma79_typeI_caseEight_strictData_complete
      a b c D horderAB hdefectAB htotal i hafter hnotAttains hmixedStrict
  exact beli2019Lemma79_typeI_caseEight_gapTwo_strict_beta_bound
    a b c D hfirst hgapTwo hlast horderAB hdefectAB hnorm i hafter
      hiNonterminal H hprefix hmixedStrict

/-- The complete nonterminal type-I gap-two branch, including the half-gap
exit. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapTwo_nonterminal
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
    (hiNonterminal : i.val < n + 1)
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
  · exact beli2019Lemma79_ii_typeI_caseEight_gapTwo_strict_nonterminal
      a b c D hfirst hnorm horderAB hdefectAB hdefectAC htotal i
        hafter hiNonterminal hattains hgapTwo

end BONG.GoodBONG

end Bong
