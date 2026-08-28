/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftOrders
import Bong.Bong.Beli2019Lemma79EvenAlphaCloseLeftOuter

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the early type-I alpha shift

Before the first canonical type-I switch, the source orders two places
apart agree and the target orders are shifted by `+1,-1`.  The exact and
inequality forms of the alpha recurrence therefore follow from the generic
two-step lemmas.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The four order identities needed by the early type-I alpha recurrence. -/
theorem lemma79_typeI_even_left_shiftedTwoStep
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hbefore : i.val < C.leftSwitch) :
    a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = a.order ⟨i.val, i.lt_large⟩ ∧
      b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ ∧
      b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
        a.order ⟨i.val - 2, by
          have hb := i.lt_large
          omega⟩ + 1 ∧
      b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
        a.order ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ - 1 := by
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i.val hiTwo hbefore.le hiEven
  have ha : a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = a.order ⟨i.val, i.lt_large⟩ := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.1.symm
  have hleftShift : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.1
  have hmiddleShift : b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ - 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.2
  have hb : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ = b.order ⟨i.val, i.lt_large⟩ := by
    rw [hleftShift]
    have hcurrentTarget := C.target_before_left i.val hbefore hiEven
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    change a.orderSequence.entryOrZero (i.val - 2) + 1 =
      b.orderSequence.entryOrZero i.val
    rw [hcurrentTarget]
    have hpreviousEven : Even (i.val - 2) := by
      rcases hiEven with ⟨d, hd⟩
      exact ⟨d - 1, by omega⟩
    have hpreviousSource := C.source_to_anchor (i.val - 2)
      ((Nat.sub_le i.val 2).trans hbefore.le |>.trans C.left_le_anchor)
      hpreviousEven
    rw [hpreviousSource]
  exact ⟨ha, hb, hleftShift, hmiddleShift⟩

/-- Neighboring target and source alphas differ by at most two throughout
the early type-I interval. -/
theorem beli2019Lemma79_typeI_even_left_alphaClose
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hbefore : i.val < C.leftSwitch) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ ≤
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have horders := lemma79_typeI_even_left_shiftedTwoStep
    a b D C hfirst i hiTwo hiEven hbefore
  have hsourcePrevious := lemma69_typeI_left_previousAlpha_eq_one
    a b D C hfirst hleftPos hdefect i.val hiTwo hbefore.le hiEven
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have htargetPrevious := beli2019Lemma69_i_typeI_targetLeftTail
    a b D C hfirst hleftPos (i.val - 2) (by omega) hpreviousEven
  apply currentAlpha_le_add_two_of_shifted_twoStep
    a b i hiTwo horders.1 horders.2.1
  · rw [hsourcePrevious]
    exact htargetPrevious
  · exact horders.2.2.1
  · exact horders.2.2.2

/-- In the strict small-gap branch, the early type-I target alpha is the
corresponding source alpha plus two. -/
theorem beli2019Lemma79_typeI_even_left_alphaShift
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hbefore : i.val < C.leftSwitch)
    (hsmall : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ < 2 * (ramificationIndex K : Int)) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have hleftPos : 0 < C.leftSwitch := by omega
  have horders := lemma79_typeI_even_left_shiftedTwoStep
    a b D C hfirst i hiTwo hiEven hbefore
  have hsourcePrevious := lemma69_typeI_left_previousAlpha_eq_one
    a b D C hfirst hleftPos hdefect i.val hiTwo hbefore.le hiEven
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have htargetPrevious := beli2019Lemma69_i_typeI_targetLeftTail
    a b D C hfirst hleftPos (i.val - 2) (by omega) hpreviousEven
  have htargetOne := b.previousAlpha_eq_one_of_twoStep_of_nextGap_lt_twoE
    i hiTwo horders.2.1 hsmall htargetPrevious
  apply currentAlpha_eq_add_two_of_shifted_twoStep
    a b i hiTwo horders.1 horders.2.1
  · rw [htargetOne, hsourcePrevious]
  · exact horders.2.2.1
  · exact horders.2.2.2

end BONG.GoodBONG

end Bong
