/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69RightTailMinimum
import Bong.Bong.Beli2019Lemma79RightTailBetaProfile
import Bong.Bong.Beli2019Lemma79RightTailProfile

/-!
# Beli (2019), Lemma 7.9(ii), case 8: strict tails from conditions

Lemma 6.9(iv) now supplies the shifted beta identity from conditions
2.1(i),(ii) and an unchanged order suffix.  This file connects that result
to the propagation and strict-beta packages, then instantiates the bridge at
the canonical last-difference coordinate in each type of Lemma 6.7.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- An unchanged order suffix identifies the final half-gap candidates once
the final boundary lies strictly after the last changed order. -/
theorem caseEight_halfGapValue_eq_of_orderSuffix
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (first last : Fin (n + 1)) (hfirstLast : first < last)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k) :
    a.halfGapValue last = b.halfGapValue last := by
  have hcurrent := hsuffix last.val (by omega) (by omega)
  have hnext := hsuffix (last.val + 1) (by omega) (by omega)
  have hcurrentA := a.orderSequence_entryOrZero_eq_order
    ⟨last.val, by omega⟩
  have hcurrentB := b.orderSequence_entryOrZero_eq_order
    ⟨last.val, by omega⟩
  have hnextA := a.orderSequence_entryOrZero_eq_order
    ⟨last.val + 1, by omega⟩
  have hnextB := b.orderSequence_entryOrZero_eq_order
    ⟨last.val + 1, by omega⟩
  rw [hcurrentA, hcurrentB] at hcurrent
  rw [hnextA, hnextB] at hnext
  have hcurrentIndex :
      (⟨last.val, by omega⟩ : Fin (n + 2)) = last.castSucc := by
    apply Fin.ext
    rfl
  have hnextIndex :
      (⟨last.val + 1, by omega⟩ : Fin (n + 2)) = last.succ := by
    apply Fin.ext
    rfl
  have hcurrentOrder :
      a.order last.castSucc = b.order last.castSucc := by
    simpa only [hcurrentIndex] using hcurrent
  have hnextOrder : a.order last.succ = b.order last.succ := by
    simpa only [hnextIndex] using hnext
  unfold halfGapValue orderGap
  rw [hcurrentOrder, hnextOrder]

/-- The strict case-8 beta profile derived only from conditions 2.1(i),(ii),
the actual unchanged order suffix, and the strict beta/source-alpha branch.
-/
theorem caseEight_strictBetaTailConsequences_of_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (first last : Fin (n + 1)) (hfirstLast : first < last)
    (hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k)
    (hstrict : b.alphaValue last < a.alphaValue last) :
    CaseEightStrictBetaTailConsequences b first last := by
  have hshift := beli2019Lemma69_iv_beta_shift_of_lt_sourceAlpha
    a b horder hdefect first last hfirstLast.le hsuffix hstrict
  have H := caseEight_betaTailConsequences_of_beta_shift
    b first last hfirstLast hshift
  have hhalf : b.alphaValue last < b.halfGapValue last := by
    calc
      b.alphaValue last < a.alphaValue last := hstrict
      _ <= a.halfGapValue last := a.alphaValue_le_halfGapValue last
      _ = b.halfGapValue last :=
        caseEight_halfGapValue_eq_of_orderSuffix
          a b first last hfirstLast hsuffix
  exact caseEight_strictBetaTailConsequences b first last H hhalf

/-- Case 8's strict beta tail for the canonical type-I last difference. -/
theorem beli2019Lemma79_typeI_caseEight_strictBetaTail
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (last : Fin (n + 1)) (hafter : D.profile.last < last.val)
    (hstrict : b.alphaValue last < a.alphaValue last) :
    CaseEightStrictBetaTailConsequences b
      ⟨D.profile.last, by omega⟩ last := by
  let first : Fin (n + 1) := ⟨D.profile.last, by omega⟩
  have hfirstLast : first < last := by
    change D.profile.last < last.val
    exact hafter
  have hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.profile.lastDifference.after k
    · change D.profile.last + 1 <= k at hk
      omega
    · omega
  have H := caseEight_strictBetaTailConsequences_of_conditions
    a b horder hdefect first last hfirstLast hsuffix hstrict
  simpa only [first] using H

/-- Case 8's strict beta tail for the canonical type-II last difference. -/
theorem beli2019Lemma79_typeII_caseEight_strictBetaTail
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (last : Fin (n + 1)) (hafter : D.outer.last < last.val)
    (hstrict : b.alphaValue last < a.alphaValue last) :
    CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, by omega⟩ last := by
  let first : Fin (n + 1) := ⟨D.outer.last, by omega⟩
  have hfirstLast : first < last := by
    change D.outer.last < last.val
    exact hafter
  have hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · change D.outer.last + 1 <= k at hk
      omega
    · omega
  have H := caseEight_strictBetaTailConsequences_of_conditions
    a b horder hdefect first last hfirstLast hsuffix hstrict
  simpa only [first] using H

/-- Case 8's strict beta tail for the canonical type-III last difference. -/
theorem beli2019Lemma79_typeIII_caseEight_strictBetaTail
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (last : Fin (n + 1)) (hafter : D.outer.last < last.val)
    (hstrict : b.alphaValue last < a.alphaValue last) :
    CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, by omega⟩ last := by
  let first : Fin (n + 1) := ⟨D.outer.last, by omega⟩
  have hfirstLast : first < last := by
    change D.outer.last < last.val
    exact hafter
  have hsuffix : forall k, first.val + 1 <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero k := by
    intro k hk hkn
    apply D.outer.lastDifference.after k
    · change D.outer.last + 1 <= k at hk
      omega
    · omega
  have H := caseEight_strictBetaTailConsequences_of_conditions
    a b horder hdefect first last hfirstLast hsuffix hstrict
  simpa only [first] using H

end BONG.GoodBONG

end Bong
