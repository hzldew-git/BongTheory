/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIIRightValue
import Bong.Bong.Beli2019Lemma69TypeIIIRightValue
import Bong.Bong.Beli2019Lemma79CaseSixCandidateShift
import Bong.Bong.Beli2019Remark616RightMixedGeneral

/-!
# Beli (2019), Lemma 7.9(ii), case 6: half-gap and primary candidates

The even-distance right profile raises the target current order by one.
At the following boundary Lemma 6.9 identifies the representation alpha
with the target alpha, so Remark 6.16 decreases the primary mixed prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The common half-gap comparison on the case-6 parity class of a
no-gap-two right profile. -/
theorem lemma79_caseSix_profile_halfGap_le_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : O.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < O.last)
    (heven : Even (i.val - (O.transition.firstTwo - 1))) :
    b.representationHalfGap c i ≤
      a.representationHalfGap c i + ((1 : ℚ) : WithTop ℚ) := by
  have hentry := O.target_rightEven_eq_source_add_one
    hnoTwo i.val hright hbeforeLast.le heven
  have horder : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  exact representationHalfGap_le_add_one_of_order_eq_add_one
    a b c i horder

set_option maxHeartbeats 3000000 in
-- Remark 6.16 is instantiated at the following right-profile boundary.
/-- The primary candidate comparison on the type-II case-6 parity class.
-/
theorem beli2019Lemma79_typeII_caseSix_primary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hlast : D.outer.last = n + 1)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hbeforeLast.le heven
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextBound : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hnextStart : D.outer.transition.firstTwo ≤ nextIdx.val := by
    simp only [nextIdx]
    have hseparated := D.outer.transition.separated
    omega
  have hnextOdd : Odd
      (nextIdx.val - (D.outer.transition.firstTwo - 1)) := by
    rcases heven with ⟨d, hd⟩
    exact ⟨d, by simp only [nextIdx]; omega⟩
  have hAlpha := a.beli2019Lemma69_ii_typeII_targetRightValue
    b D hlast horder hdefect htotal nextIdx.val hnextStart hnextOdd
      nextIdx.lt_large
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i horderShift hprefix

set_option maxHeartbeats 4000000 in
-- The type-III parity is converted from distance parity to absolute parity.
/-- The primary candidate comparison on the nonoverlapping type-III
case-6 parity class. -/
theorem beli2019Lemma79_typeIII_caseSix_primary_le_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
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
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1))) :
    b.representationPrimaryDefect c i ≤
      a.representationPrimaryDefect c i +
        ((1 : ℚ) : WithTop ℚ) := by
  have hentry := D.outer.target_rightEven_eq_source_add_one
    D.no_gap_two i.val hright hbeforeLast.le heven
  have horderShift : b.order ⟨i.val, i.lt_large⟩ =
      a.order ⟨i.val, i.lt_large⟩ + 1 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hentry
  have hnextBound : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  let nextIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by omega, hnextBound, hnextBound.le⟩
  have hleftEven : Even D.outer.transition.lastZero := by
    by_cases heq : D.outer.first = D.outer.transition.lastZero
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.outer.first < D.outer.transition.lastZero :=
        lt_of_le_of_ne D.outer.first_le_left heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.outer.leftProfile hlt).1
  have hnextEven : Even nextIdx.val := by
    rcases hleftEven with ⟨p, hp⟩
    rcases heven with ⟨d, hd⟩
    refine ⟨p + d + 1, ?_⟩
    simp only [nextIdx]
    have hbase : D.outer.transition.firstTwo - 1 =
        D.outer.transition.lastZero + 1 := by
      rw [D.adjacent]
      omega
    have hiEq : i.val =
        (D.outer.transition.firstTwo - 1) + (d + d) := by
      omega
    omega
  have hnextStart : D.outer.transition.lastZero + 2 ≤
      nextIdx.val := by
    simp only [nextIdx]
    rw [← D.adjacent]
    have hseparated := D.outer.transition.separated
    omega
  have hAlpha := a.beli2019Lemma69_ii_typeIII_targetRightValue
    b D hfirst hlast horder hdefect htotal hnotOverlap hinitial
      nextIdx.val hnextStart hnextEven nextIdx.lt_large
  have hformula := beli2019Remark616_rightMixedPrefix_at
    a b c hdefect nextIdx hAlpha (-1) (i.val - 1)
  have hprefix : b.truncatedPrefixDefect c (-1) (i.val + 1)
      (i.val - 1) ≤
    a.truncatedPrefixDefect c (-1) (i.val + 1) (i.val - 1) := by
    simpa only [nextIdx] using
      (hformula.le.trans (min_le_left _ _))
  exact representationPrimaryDefect_le_add_one_of_order_eq_add_one
    a b c i horderShift hprefix

end BONG.GoodBONG

end Bong
