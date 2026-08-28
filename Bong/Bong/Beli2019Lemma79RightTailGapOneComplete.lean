/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailStrictComplete

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete gap-one reduction

The strict case-8 assembly is closed as soon as one of the three concrete
gap-one beta witnesses is available.  The generic theorem below performs
all tail propagation, endpoint conversion, and mixed-prefix assembly.
The three type-specific corollaries leave only the numerical witness
constructed by the remaining order-parity argument of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A strict tail, its comparison-prefix parity, and concrete numerical
evidence close the complete gap-one branch of case 8. -/
theorem beli2019Lemma79_ii_caseEight_gapOne_of_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first ≤ caseEightLastAlphaIndex i)
    (hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hentry : b.orderSequence.entryOrZero first.val =
      a.orderSequence.entryOrZero first.val + 1)
    (hstrictData : ∀ hbeta :
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
          a.truncatedPrefixDefect c 1 i.val i.val,
      CaseEightStrictBetaTailConsequences b first
          (caseEightLastAlphaIndex i) ∧
        Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val))
    (hevidence : ∀ (hbeta :
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
          a.truncatedPrefixDefect c 1 i.val i.val)
        (H : CaseEightStrictBetaTailConsequences b first
          (caseEightLastAlphaIndex i))
        (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val))
        (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
          a.alphaValue (caseEightLastAlphaIndex i)),
      CaseEightGapOneBetaEvidence b c i (b.order first.castSucc)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hfirstBoundary : first.val + 1 ≤ i.val := by
    have hiPos := i.pos
    change first.val ≤ i.val - 1 at hfirstLast
    omega
  have hsuffixI : ∀ k, i.val ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hik hkn
    exact hsuffix k (hfirstBoundary.trans hik) hkn
  apply beli2019Lemma79_ii_caseEight_of_strict_beta_bound
    a b c hdefectAB hdefectAC i hsuffixI
  intro hbeta
  obtain ⟨H, hprefix⟩ := hstrictData hbeta
  have hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i) := by
    simpa only [caseEightLastAlphaIndex] using
      caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
        a c i (b.alphaValue (caseEightLastAlphaIndex i)) hbeta
  have hformulaData := H.gapOne_formula_of_entryOrZero
    hfirstLast hsuffix hentry hstrictLast
  have hformula := hformulaData.2 (caseEightLastAlphaIndex i)
    hfirstLast le_rfl
  have E := hevidence hbeta H hprefix hstrictLast
  exact_mod_cast E.beta_bound hformula

/-- Type-I gap-one case reduced to its concrete numerical evidence. -/
theorem beli2019Lemma79_ii_typeI_caseEight_gapOne_of_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hgapOne : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 1)
    (hevidence : ∀ (hbeta :
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
          a.truncatedPrefixDefect c 1 i.val i.val)
        (H : CaseEightStrictBetaTailConsequences b
          (Fin.mk D.profile.last (by
            have hi := i.lt_large
            omega)) (caseEightLastAlphaIndex i))
        (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val))
        (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
          a.alphaValue (caseEightLastAlphaIndex i)),
      CaseEightGapOneBetaEvidence b c i
        (b.order (Fin.mk D.profile.last (by
          have hi := i.lt_large
          omega)).castSucc)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let first : Fin (n + 1) := Fin.mk D.profile.last (by
    have hi := i.lt_large
    omega)
  have hfirstLast : first ≤ caseEightLastAlphaIndex i := by
    change D.profile.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  apply beli2019Lemma79_ii_caseEight_gapOne_of_strictData
    a b c hdefectAB hdefectAC i first hfirstLast hsuffix
      (by simpa only [first] using hgapOne)
  · intro hbeta
    simpa only [first] using
      beli2019Lemma79_typeI_caseEight_strictData_complete
        a b c D horder hdefectAB htotal i hafter hnotAttains hbeta
  · intro hbeta H hprefix hstrictLast
    simpa only [first] using
      hevidence hbeta (by simpa only [first] using H)
        hprefix hstrictLast

/-- Type-II gap-one case reduced to its concrete numerical evidence. -/
theorem beli2019Lemma79_ii_typeII_caseEight_gapOne_of_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hevidence : ∀ (hbeta :
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
          a.truncatedPrefixDefect c 1 i.val i.val)
        (H : CaseEightStrictBetaTailConsequences b
          (Fin.mk D.outer.last (by
            have hi := i.lt_large
            omega)) (caseEightLastAlphaIndex i))
        (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val))
        (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
          a.alphaValue (caseEightLastAlphaIndex i)),
      CaseEightGapOneBetaEvidence b c i
        (b.order (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega)).castSucc)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let first : Fin (n + 1) := Fin.mk D.outer.last (by
    have hi := i.lt_large
    omega)
  have hfirstLast : first ≤ caseEightLastAlphaIndex i := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hgapOne := beli2019Lemma79_typeII_caseEight_lastGap a b D
  apply beli2019Lemma79_ii_caseEight_gapOne_of_strictData
    a b c hdefectAB hdefectAC i first hfirstLast hsuffix
      (by simpa only [first] using hgapOne)
  · intro hbeta
    simpa only [first] using
      beli2019Lemma79_typeII_caseEight_strictData_complete
        a b c D horder hdefectAB htotal i hafter hnotAttains hbeta
  · intro hbeta H hprefix hstrictLast
    simpa only [first] using
      hevidence hbeta (by simpa only [first] using H)
        hprefix hstrictLast

/-- Type-III gap-one case reduced to its concrete numerical evidence. -/
theorem beli2019Lemma79_ii_typeIII_caseEight_gapOne_of_evidence
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (hnotAttains : b.alphaValue (caseEightLastAlphaIndex i) ≠
      b.halfGapValue (caseEightLastAlphaIndex i))
    (hevidence : ∀ (hbeta :
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) <
          a.truncatedPrefixDefect c 1 i.val i.val)
        (H : CaseEightStrictBetaTailConsequences b
          (Fin.mk D.outer.last (by
            have hi := i.lt_large
            omega)) (caseEightLastAlphaIndex i))
        (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
          (c.orderSequence.prefixSum i.val))
        (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
          a.alphaValue (caseEightLastAlphaIndex i)),
      CaseEightGapOneBetaEvidence b c i
        (b.order (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega)).castSucc)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let first : Fin (n + 1) := Fin.mk D.outer.last (by
    have hi := i.lt_large
    omega)
  have hfirstLast : first ≤ caseEightLastAlphaIndex i := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hsuffix : ∀ k, first.val + 1 ≤ k → k < n + 2 →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · simp only [first] at hk
      omega
    · exact hkn
  have hgapOne := beli2019Lemma79_typeIII_caseEight_lastGap a b D
  apply beli2019Lemma79_ii_caseEight_gapOne_of_strictData
    a b c hdefectAB hdefectAC i first hfirstLast hsuffix
      (by simpa only [first] using hgapOne)
  · intro hbeta
    simpa only [first] using
      beli2019Lemma79_typeIII_caseEight_strictData_complete
        a b c D horder hdefectAB htotal i hafter hnotAttains hbeta
  · intro hbeta H hprefix hstrictLast
    simpa only [first] using
      hevidence hbeta (by simpa only [first] using H)
        hprefix hstrictLast

end BONG.GoodBONG

end Bong
