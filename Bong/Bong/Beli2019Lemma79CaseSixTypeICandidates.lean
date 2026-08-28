/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightTargetValue
import Bong.Bong.Beli2019Lemma79CaseSixCandidateShift
import Bong.Bong.Beli2019Lemma79CaseSixTypeIProfile
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii), case 6: type-I candidate shifts

After the canonical type-I right switch, the current target order is one
above the source order.  Remark 6.16 handles the primary mixed prefix, while
the exact target alpha `beta = 1` caps the secondary mixed prefix.  Hence all
three candidates move by at most one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The half-gap candidate shifts by at most one on the type-I case-6
interval. -/
theorem lemma79_typeI_caseSix_halfGap_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((1 : ℚ) : WithTop ℚ) := by
  have hcurrentRaw := lemma79_typeI_caseSix_current_eq_source_add_one
    a b D C hfirst i hright hthroughLast hiEven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentRaw
  exact representationHalfGap_le_add_one_of_order_eq_add_one
    a b c i hcurrent

set_option maxHeartbeats 3000000 in
-- Remark 6.16 is instantiated at the following odd coordinate.
/-- The primary candidate shifts by at most one on the type-I case-6
interval. -/
theorem beli2019Lemma79_typeI_caseSix_primary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i + ((1 : ℚ) : WithTop ℚ) := by
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hiTwoLast : i.val + 2 ≤ D.profile.last := by
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hnextBound : i.val + 1 < n + 2 :=
    (by omega : i.val + 1 < D.profile.last) |>.trans
      D.profile.lastDifference.bound
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hnextOdd : Odd nextIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hAlpha := beli2019Lemma69_ii_typeI_targetRightValue
    a b D C hfirst hrightLast hdefect nextIdx (by
      simp only [nextIdx]
      omega) (by simp only [nextIdx]; omega) hnextOdd
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using hformula.le.trans (min_le_left _ _)
  have hcurrentRaw := lemma79_typeI_caseSix_current_eq_source_add_one
    a b D C hfirst i hright hbeforeLast.le hiEven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentRaw
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i hcurrent hprefix

set_option maxHeartbeats 3000000 in
-- The dependent successor and cap indices are normalized together.
/-- The secondary candidate shifts by at most one on the type-I case-6
interval. -/
theorem beli2019Lemma79_typeI_caseSix_secondary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((1 : ℚ) : WithTop ℚ) := by
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hiTwoLast : i.val + 2 ≤ D.profile.last := by
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  have hfarBound : i.val + 2 < n + 2 :=
    hiTwoLast.trans_lt D.profile.lastDifference.bound
  have hnextOdd : Odd (i.val + 1) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnextOrders := lemma69_typeI_rightOdd_orders
    a b D C hfirst (i.val + 1) (by omega) (by omega) hnextOdd
  have hcurrentRaw := lemma79_typeI_caseSix_current_eq_source_add_one
    a b D C hfirst i hright hbeforeLast.le hiEven
  have hcurrent : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hcurrentRaw
  have hnext : a.order ⟨i.val + 1, hi.2⟩ =
      b.order ⟨i.val + 1, hi.2⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hnextOrders.1
  have hsum : b.order ⟨i.val, i.lt_large⟩ +
        b.order ⟨i.val + 1, hi.2⟩ =
      a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hi.2⟩ := by
    omega
  have hbeta := beli2019Remark613_typeI_targetRightAlpha_eq_one
    a b D C hfirst hrightLast hdefect (i.val + 1)
      (by omega) (by omega) hnextOdd
  have htargetCap := b.truncatedPrefixDefect_le_leftCap
    c 1 (i.val + 2) (i.val - 2)
  rw [b.prefixAlphaCap_of_internal (by omega) hfarBound] at htargetCap
  have htargetOne : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤ ((1 : ℚ) : WithTop ℚ) :=
    htargetCap.trans (by exact_mod_cast hbeta.le)
  have hsourceNonneg := a.truncatedPrefixDefect_nonneg
    c 1 (i.val + 2) (i.val - 2)
  have hprefix : b.truncatedPrefixDefect c 1 (i.val + 2)
      (i.val - 2) ≤
      a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) +
        ((1 : ℚ) : WithTop ℚ) := by
    calc
      _ ≤ ((1 : ℚ) : WithTop ℚ) := htargetOne
      _ ≤ a.truncatedPrefixDefect c 1 (i.val + 2) (i.val - 2) + 1 := by
        simpa [add_comm] using
          add_le_add_right hsourceNonneg (1 : WithTop ℚ)
  exact representationSecondaryDefect_le_add_one_of_orderSum_eq
    a b c i hi hsum hprefix

set_option maxHeartbeats 4000000 in
-- All three candidate comparisons are assembled at once.
/-- The one-unit comparison `B_i ≤ C_i + 1` on the type-I case-6
interval. -/
theorem beli2019Lemma79_typeI_caseSix_alpha_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hbeforeLast : i.val < D.profile.last) (hiEven : Even i.val) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      (a.representationAlphaValue c i : WithTop ℚ) +
        ((1 : ℚ) : WithTop ℚ) := by
  apply lemma79_caseSix_alpha_le_add_one_of_candidate_bounds a b c i
  · exact lemma79_typeI_caseSix_halfGap_le_add_one
      a b c D C hfirst i hright hbeforeLast.le hiEven
  · exact beli2019Lemma79_typeI_caseSix_primary_le_add_one
      a b c D C hfirst hrightLast hdefect i hright hbeforeLast hiEven
  · intro hi
    exact beli2019Lemma79_typeI_caseSix_secondary_le_add_one
      a b c D C hfirst hrightLast hdefect i hi hright hbeforeLast hiEven

end BONG.GoodBONG

end Bong
