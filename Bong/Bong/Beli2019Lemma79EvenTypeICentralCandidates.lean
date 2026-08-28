/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenSecondaryInterior
import Bong.Bong.Beli2019Lemma79EvenTypeICentralAlpha
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central type-I candidates

Inside the canonical interval, even target orders are shifted by two and
adjacent order sums are unchanged.  The two branches of Remark 6.16 compare
the primary and secondary mixed prefixes, giving a two-unit bound for every
candidate of the representation alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A two-unit order shift and a decreasing mixed prefix give the required
primary-candidate comparison. -/
theorem representationPrimaryDefect_le_add_two_of_order_eq_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 2)
    (hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
        (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hcoefficientInt :
      b.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ =
        (a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩) + 2 := by
    omega
  have hcoefficient :
      (((b.order ⟨i.val, i.lt_large⟩ -
        c.order ⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Int) : ℚ) : WithTop ℚ) =
        (((a.order ⟨i.val, i.lt_large⟩ -
          c.order ⟨i.val - 1, by
            have hi := i.lt_large
            omega⟩ : Int) : ℚ) : WithTop ℚ) +
          ((2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hcoefficientInt
  unfold representationPrimaryDefect
  rw [hcoefficient]
  let coefficient : WithTop ℚ :=
    (((a.order ⟨i.val, i.lt_large⟩ -
      c.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Int) : ℚ) : WithTop ℚ)
  change (coefficient + 2) +
      b.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) ≤
    (coefficient +
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1)) + 2
  calc
    _ ≤ (coefficient + 2) +
        a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) :=
      by
        simpa only [add_comm] using
          add_le_add_left hprefix (coefficient + 2)
    _ = _ := by ac_rfl

/-- The half-gap candidate comparison in the central type-I interval. -/
theorem lemma79_typeI_central_even_halfGap_le_add_two
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val ≤ C.rightSwitch) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((2 : ℚ) : WithTop ℚ) := by
  have hentry := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven hiLeft hiRight
  apply representationHalfGap_le_add_two_of_order_le_add_four a b c i
  rw [← a.orderSequence_entryOrZero_eq_order,
    ← b.orderSequence_entryOrZero_eq_order]
  change b.orderSequence.entryOrZero i.val ≤
    a.orderSequence.entryOrZero i.val + 4
  omega

set_option maxHeartbeats 3000000 in
-- Remark 6.16 is instantiated at the following odd boundary.
/-- The primary candidate comparison in the strict central type-I interval. -/
theorem beli2019Lemma79_typeI_central_even_primary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hiRight : i.val < C.rightSwitch) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((2 : ℚ) : WithTop ℚ) := by
  have hentry := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst i.val hiEven hiLeft hiRight.le
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hiNext, hiNext.le⟩
  have hnextOdd : Odd nextIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hAlpha := beli2019Lemma69_ii_typeI_targetValue_from_conditions
    a b D C hfirst hrightLast horderAB hdefectAB nextIdx hnextOdd
      (by simp only [nextIdx]; omega) (by simp only [nextIdx]; omega)
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefectAB nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
      a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_two_of_order_eq_add_two
    a b c i horderShift hprefix

set_option maxHeartbeats 4000000 in
-- The boundary `i + 2` and its mixed prefixes carry dependent indices.
/-- The secondary candidate comparison before the right end of the central
type-I interval. -/
theorem beli2019Lemma79_typeI_central_even_secondary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val) (hiLeft : C.leftSwitch ≤ i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    b.representationSecondaryDefect c i hi ≤
      a.representationSecondaryDefect c i hi +
        ((2 : ℚ) : WithTop ℚ) := by
  have hrightBound : C.rightSwitch < n + 2 :=
    C.right_le_last.trans_lt D.profile.lastDifference.bound
  have hfarBound : i.val + 2 < n + 2 := by omega
  let farIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 2, by omega, hfarBound, hfarBound.le⟩
  have hfarEven : Even farIdx.val := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d + 1, by simp only [farIdx]; omega⟩
  have hfarLeft : C.leftSwitch ≤ farIdx.val - 1 := by
    simp only [farIdx]
    omega
  have hfarRight' : farIdx.val - 1 < C.rightSwitch := by
    simp only [farIdx]
    omega
  have hAlphaRaw :=
    (lemma69_typeI_central_values_from_conditions
      a b D C hfirst hrightLast horderAB hdefectAB farIdx
        hfarLeft hfarRight').2 hfarEven
  have hAlpha : a.representationAlphaValue b farIdx =
      a.alphaValue ⟨farIdx.val - 1, by
        have hf := farIdx.lt_large
        omega⟩ := by
    apply WithTop.coe_injective
    rw [a.coe_representationAlphaValue b farIdx]
    exact hAlphaRaw
  have hclose := beli2019Lemma79_typeI_central_even_alphaShift
    a b D C hfirst hrightLast horderAB hdefectAB farIdx hfarEven
      hfarLeft hfarRight'
  have hprefix := lemma79_even_secondaryPrefix_le_add_two_of_leftAlpha
    a b c hdefectAB i hfarBound
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hAlpha)
      (by simpa only [farIdx,
        show i.val + 2 - 1 = i.val + 1 by omega] using hclose.le)
  have hsumRaw := lemma69_v_typeI_adjacent_entry_sum_eq
    a b D C hfirst i.val hiLeft (by omega)
  apply representationSecondaryDefect_le_add_two_of_orderSum_eq
    a b c i hi
  · rw [← a.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hsumRaw.symm
  · exact hprefix

end BONG.GoodBONG

end Bong
