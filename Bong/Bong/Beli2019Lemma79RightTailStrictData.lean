/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailSourceDomination
import Bong.Bong.Beli2019Lemma79RightTailStrict

/-!
# Beli (2019), Lemma 7.9(ii), case 8: strict-branch data

The paper's strict branch compares beta with the capped source/comparison
prefix defect.  The left alpha cap turns this into the source-alpha
inequality used by the tail propagation.  For each Lemma 6.7 type, the
same hypotheses also give the comparison-prefix parity needed later in
case 8.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A strict beta/source-prefix comparison is automatically a strict
beta/source-alpha comparison at the same boundary. -/
theorem caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (beta : Rat)
    (hbeta : (beta : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    beta < a.alphaValue (Fin.mk (i.val - 1) (by
      have hi := i.lt_large
      omega)) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap
    c 1 i.val i.val
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large] at hcap
  exact WithTop.coe_lt_coe.mp (hbeta.trans_le hcap)

/-- Type-I strict case-8 data: the propagated beta tail together with the
target/comparison prefix parity. -/
theorem beli2019Lemma79_typeI_caseEight_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 < i.val)
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.profile.last (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  let last : Fin (n + 1) := Fin.mk (i.val - 1) (by
    have hi := i.lt_large
    omega)
  have hstrict : b.alphaValue last < a.alphaValue last := by
    simpa only [last] using
      caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
        a c i (b.alphaValue last) hbeta
  have htail := beli2019Lemma79_typeI_caseEight_strictBetaTail
    a b D horder hdefect last (by
      simp only [last]
      omega) hstrict
  have hsuffix := beli2019Lemma79_typeI_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeI_caseEight_prefix_modEq
    a b D htotal i (by omega)
  have hcomparison :=
    caseEight_prefixSum_modEq_comparison_of_beta_lt_source
      a b c hdefect i hsuffix hab hbeta
  exact ⟨by simpa only [last] using htail, hcomparison⟩

/-- Type-II strict case-8 data. -/
theorem beli2019Lemma79_typeII_caseEight_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 < i.val)
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  let last : Fin (n + 1) := Fin.mk (i.val - 1) (by
    have hi := i.lt_large
    omega)
  have hstrict : b.alphaValue last < a.alphaValue last := by
    simpa only [last] using
      caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
        a c i (b.alphaValue last) hbeta
  have htail := beli2019Lemma79_typeII_caseEight_strictBetaTail
    a b D horder hdefect last (by
      simp only [last]
      omega) hstrict
  have hsuffix := beli2019Lemma79_typeII_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeII_caseEight_prefix_modEq
    a b D htotal i (by omega)
  have hcomparison :=
    caseEight_prefixSum_modEq_comparison_of_beta_lt_source
      a b c hdefect i hsuffix hab hbeta
  exact ⟨by simpa only [last] using htail, hcomparison⟩

/-- Type-III strict case-8 data. -/
theorem beli2019Lemma79_typeIII_caseEight_strictData
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 < i.val)
    (hbeta : (b.alphaValue (Fin.mk (i.val - 1) (by
        have hi := i.lt_large
        omega)) : WithTop Rat) <
      a.truncatedPrefixDefect c 1 i.val i.val) :
    CaseEightStrictBetaTailConsequences b
        (Fin.mk D.outer.last (by
          have hi := i.lt_large
          omega))
        (Fin.mk (i.val - 1) (by
          have hi := i.lt_large
          omega)) ∧
      Int.ModEq 2 (b.orderSequence.prefixSum i.val)
        (c.orderSequence.prefixSum i.val) := by
  let last : Fin (n + 1) := Fin.mk (i.val - 1) (by
    have hi := i.lt_large
    omega)
  have hstrict : b.alphaValue last < a.alphaValue last := by
    simpa only [last] using
      caseEight_beta_lt_sourceAlpha_of_lt_sourceDefect
        a c i (b.alphaValue last) hbeta
  have htail := beli2019Lemma79_typeIII_caseEight_strictBetaTail
    a b D horder hdefect last (by
      simp only [last]
      omega) hstrict
  have hsuffix := beli2019Lemma79_typeIII_caseEight_suffix
    a b D i (by omega)
  have hab := beli2019Lemma79_typeIII_caseEight_prefix_modEq
    a b D htotal i (by omega)
  have hcomparison :=
    caseEight_prefixSum_modEq_comparison_of_beta_lt_source
      a b c hdefect i hsuffix hab hbeta
  exact ⟨by simpa only [last] using htail, hcomparison⟩

end BONG.GoodBONG

end Bong
