/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIISourceAlpha
import Bong.Bong.Beli2019Lemma69TypeIILeftAlpha
import Bong.Bong.Beli2019Lemma78PreviousAlpha
import Bong.Bong.Beli2019Lemma79EvenAlphaShift

/-!
# Beli (2019), Lemma 7.9(ii), case 3: left-outer alpha shift

The no-gap left profile supplies the four order identities needed by the
generic alpha-shift theorem.  Lemma 6.9(i) supplies the preceding alpha
bounds, while the strict small-gap branch rules out a zero target alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The identity `beta_i = alpha_i + 2` on a normalized no-gap left
outer interval in the strict small-source-gap branch. -/
theorem lemma79_even_alphaShift_of_noGap_leftOuter
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ O.transition.lastZero)
    (hsourcePrevious : a.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = 1)
    (htargetPrevious : b.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ ≤ 1)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hmiddleOdd : Odd (i.val - 1) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have haPrevious := O.source_leftEven_eq_first
    hfirst (i.val - 2) (by omega) hpreviousEven
  have haCurrent := O.source_leftEven_eq_first
    hfirst i.val hleft hiEven
  have hbPrevious := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val - 2) (by omega) hpreviousEven
  have hbCurrent := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hleft hiEven
  have hmiddle := O.source_leftOdd_eq_target_add_one
    hfirst hnoTwo (i.val - 1) (by omega) hmiddleOdd
  have htwoA : a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = a.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact haPrevious.trans haCurrent.symm
  have htwoB : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hbPrevious.trans hbCurrent.symm
  have hleftShift : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero (i.val - 2) =
      a.orderSequence.entryOrZero (i.val - 2) + 1
    omega
  have hmiddleShift : b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ - 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    change b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) - 1
    omega
  have htargetOne :=
    b.previousAlpha_eq_one_of_twoStep_of_nextGap_lt_twoE
      i hiTwo htwoB hsmall htargetPrevious
  apply currentAlpha_eq_add_two_of_shifted_twoStep
    a b i hiTwo htwoA htwoB
  · rw [htargetOne, hsourcePrevious]
  · exact hleftShift
  · exact hmiddleShift

/-- Type II specialization of the left-outer alpha shift. -/
theorem beli2019Lemma79_typeII_even_left_alphaShift
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  apply lemma79_even_alphaShift_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma69_typeII_sourcePreviousAlpha_eq_one
      b D hfirst i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeII_targetLeftTail
      b D hfirst (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  · exact hsmall

/-- Type III specialization of the left-outer alpha shift. -/
theorem beli2019Lemma79_typeIII_even_left_alphaShift
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  apply lemma79_even_alphaShift_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail
      b D hfirst horder hdefect htotal hlast (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  · exact hsmall

end BONG.GoodBONG

end Bong
