/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenSecondaryArithmetic

/-!
# Beli (2019), Lemma 7.9(ii), case 3: neighboring alpha closeness

Two-step equality in the left outer profile gives exact alpha recurrences.
The preceding source alpha is one and the corresponding target alpha is at
most one, so the next target alpha is at most the source alpha plus two.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The alpha recurrence is monotone under the left-profile shifts
`+1,-1` when the preceding target alpha is no larger. -/
theorem currentAlpha_le_add_two_of_shifted_twoStep
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (htwoA : a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val, i.lt_large⟩)
    (htwoB : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hprevious : b.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩)
    (hleft : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ + 1)
    (hmiddle : b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ - 1) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  rw [b.currentAlpha_eq_order_sub_add_previous_of_twoStep
      i hiTwo htwoB,
    a.currentAlpha_eq_order_sub_add_previous_of_twoStep
      i hiTwo htwoA]
  have hleftQ :
      (b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ : ℚ) =
        (a.order ⟨i.val - 2, by
          have hb := i.lt_large
          omega⟩ : ℚ) + 1 := by
    exact_mod_cast hleft
  have hmiddleQ :
      (b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : ℚ) =
        (a.order ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ : ℚ) - 1 := by
    exact_mod_cast hmiddle
  push_cast
  rw [hleftQ, hmiddleQ]
  linarith

/-- The neighboring alpha values are within two units throughout a
normalized no-gap left outer interval. -/
theorem lemma79_even_alphaClose_of_noGap_leftOuter
    [Beli2006AlphaLaws.{u, v} K]
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
        omega⟩ ≤ 1) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
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
  have hmiddleRaw := O.source_leftOdd_eq_target_add_one
    hfirst hnoTwo (i.val - 1) (by omega) hmiddleOdd
  have htwoA : a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact haPrevious.trans haCurrent.symm
  have htwoB : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
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
  apply currentAlpha_le_add_two_of_shifted_twoStep
    a b i hiTwo htwoA htwoB
  · rw [hsourcePrevious]
    exact htargetPrevious
  · exact hleftShift
  · exact hmiddleShift

/-- Type-II specialization of neighboring alpha closeness. -/
theorem beli2019Lemma79_typeII_even_left_alphaClose
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  apply lemma79_even_alphaClose_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma69_typeII_sourcePreviousAlpha_eq_one
      b D hfirst i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeII_targetLeftTail
      b D hfirst (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

/-- Type-III specialization of neighboring alpha closeness. -/
theorem beli2019Lemma79_typeIII_even_left_alphaClose
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
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  apply lemma79_even_alphaClose_of_noGap_leftOuter
    a b D.outer hfirst D.no_gap_two i hiTwo hiEven hleft
  · exact a.lemma78_typeIII_sourcePreviousAlpha_eq_one
      b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
        i.val hiTwo hleft hiEven
  · apply a.beli2019Lemma69_i_typeIII_targetLeftTail
      b D hfirst horder hdefect htotal hlast (i.val - 2) (by omega)
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩

end BONG.GoodBONG

end Bong
