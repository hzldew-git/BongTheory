/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanProfile

/-!
# Section 5.4 with equal-scale endpoint amalgamations

This file repeats the coordinate comparison of Beli (2019), Section 5.4 on
the uniform weak profiles.  Hence the formulas cover both strict Jordan
splittings and the endpoint cases where the selected component is
amalgamated with an adjacent equal-scale common component.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- At an aligned selected component, the larger-lattice order is bounded by
the smaller-lattice order.  The statement is independent of endpoint scale
collisions. -/
theorem weakAligned_selected_order_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Fin n)
    (hi : ((D.largeWeakProfileWitness a).indexEquiv i).1 =
      D.largeSelectedPosition) :
    a.order i ≤ b.order i := by
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b i
  have hy : ((D.smallWeakProfileWitness b).indexEquiv i).1 =
      D.smallSelectedPosition := by
    calc
      ((D.smallWeakProfileWitness b).indexEquiv i).1 =
          ((D.largeWeakProfileWitness a).indexEquiv i).1 :=
        hcoordinates.1.symm
      _ = D.largeSelectedPosition := hi
      _ = D.smallSelectedPosition := hselected.symm
  rw [D.largeWeak_order_eq_localOrder a i,
    D.smallWeak_order_eq_localOrder b i]
  simp only [hi, hy, D.largeAlmostJordan_scaleGenerator_selected,
    D.smallAlmostJordan_scaleGenerator_selected]
  rcases D.rank_one_or_two with hOne | hTwo
  · have hlargeEffective :=
      D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hOne
    have hsmallEffective :=
      D.smallSelected_effectiveNormOrder_eq_scale_of_rank_one hOne
    rw [hlargeEffective, hsmallEffective]
    simp only [JordanProfileOrder.localOrder_of_proper]
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hRankOne | hRankTwo <;> omega
  · have hlargeLe := D.largeSelected_effectiveNormOrder_le_smallSelected
    have hsmallLe :=
      D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
        hTwo
    have hlargeScale :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
        D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator)
    have hsmallScale :=
      D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
        D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator)
    have hrank : finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv i).1).carrier = 2 := by
      rw [hi, D.largeAlmostJordan_finrank_selected, hTwo]
    have hjlt :
        ((D.largeWeakProfileWitness a).indexEquiv i).2.val < 2 := by
      simpa only [hrank] using
        ((D.largeWeakProfileWitness a).indexEquiv i).2.isLt
    have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 1 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        hRankOne | hRankTwo
      · omega
      · exact hRankTwo.2
    interval_cases hlocal :
        ((D.largeWeakProfileWitness a).indexEquiv i).2.val
    · have hsmallLocal :
          ((D.smallWeakProfileWitness b).indexEquiv i).2.val = 0 := by
        omega
      simp only [hsmallLocal]
      rw [JordanProfileOrder.localOrder_even_of_scale_le hlargeScale (by simp),
        JordanProfileOrder.localOrder_even_of_scale_le hsmallScale (by simp)]
      exact hlargeLe
    · have hsmallLocal :
          ((D.smallWeakProfileWitness b).indexEquiv i).2.val = 1 := by
        omega
      simp only [hsmallLocal]
      rw [JordanProfileOrder.localOrder_odd_of_scale_le hlargeScale (by simp),
        JordanProfileOrder.localOrder_odd_of_scale_le hsmallScale (by simp)]
      omega

/-- A common component before the selected component, at a local coordinate
with a successor, has the Section 5.4 coordinate certificate. -/
theorem weakAligned_common_before_coordinate_of_local_succ_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore : D.smallCommonPosition c < D.smallSelectedPosition)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change (x.indexEquiv I).2.val + 1 <
    finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      at hlocalNext
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    simpa only [scale] using
      D.smallCommon_scale_lt_selected_of_position_lt c hsmallBefore
  have heffective : sourceEffective ≤ targetEffective :=
    D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_le
    a.orderSequence b.orderSequence i hi localIndex scale
      sourceEffective targetEffective hsourceScale htargetScale heffective
      hsourceCurrent htargetCurrent
  intro hodd
  have hlocalPos : 0 < localIndex := by
    by_contra hnot
    have hzero : localIndex = 0 := Nat.eq_zero_of_not_pos hnot
    subst localIndex
    exact hodd ⟨0, by omega⟩
  have hi0 : 0 < i := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change i = _ at hindex
    omega
  have hiNext : i + 1 < n := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
    have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hnextBound :=
      (x.indexEquiv.symm
        ⟨(x.indexEquiv I).1,
          ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
    have hval' :
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          simpa using hval
        _ = i + 1 := by rw [hcurrent]
    exact hval' ▸ hnextBound
  have hevenNext : Even (localIndex + 1) := (Nat.even_add_one).2 hodd
  have hevenPrevious : Even (localIndex - 1) := by
    rcases (Nat.not_even_iff_odd.mp hodd) with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hsourceNext :
      a.orderSequence.entry (i + 1) hiNext = sourceEffective := by
    change a.order ⟨i + 1, hiNext⟩ = sourceEffective
    have h := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hiNext hlocalNext
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    simp only [I] at h
    change a.order ⟨i + 1, hiNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsourceScale hevenNext] at h
    exact h
  have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    exact hlocalPos
  have htargetPrevious :
      b.orderSequence.entry (i - 1) (by omega) = targetEffective := by
    change b.order ⟨i - 1, by omega⟩ = targetEffective
    have h := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred
      I hsmallLocalPos
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [htargetScaleAt, htargetEffectiveAt] at h
    simp only [I] at h
    have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by omega
    change b.order ⟨i - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val - 1) at h
    rw [hprev, JordanProfileOrder.localOrder_even_of_scale_le
      htargetScale hevenPrevious] at h
    exact h
  exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- Aligned-position specialization of the preceding local-successor
certificate. -/
theorem weakAligned_common_before_coordinate_of_local_succ
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.weakAligned_common_before_coordinate_of_local_succ_of_alignment
    a b i hi c hposition
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact hlocalNext

/-- The last odd coordinate of a common component before the selected
component, including endpoint-amalgamation cases. -/
theorem weakAligned_common_before_last_odd_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore : D.smallCommonPosition c < D.smallSelectedPosition)
    (hlast :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier)
    (hodd : ¬Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := D.largeCommonPosition c
  let pNext : Fin (D.complementComponentCount + 1) :=
    ⟨p.val + 1, by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hbefore)
        D.largeSelectedPosition.isLt⟩
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let nextScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = p at hposition
  change (x.indexEquiv I).2.val + 1 =
    finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      at hlast
  change ¬Even (x.indexEquiv I).2.val at hodd
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = p := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    simpa only [scale] using
      D.smallCommon_scale_lt_selected_of_position_lt c hsmallBefore
  have heffective : sourceEffective ≤ targetEffective :=
    D.large_effectiveNormOrderAt_le_small_of_target_lt
      p (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition]
    exact D.largeAlmostJordan_scaleGenerator_common c ▸ rfl
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  by_cases heq : sourceEffective = targetEffective
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent, heq]
  · have hlt : sourceEffective < targetEffective :=
      lt_of_le_of_ne heffective heq
    apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_le
      a.orderSequence b.orderSequence i hi localIndex scale
        sourceEffective targetEffective hsourceScale htargetScale heffective
        hsourceCurrent htargetCurrent
    intro _
    have hlocalPos : 0 < localIndex := by
      by_contra hnot
      have hzero : localIndex = 0 := Nat.eq_zero_of_not_pos hnot
      subst localIndex
      exact hodd ⟨0, by omega⟩
    have hi0 : 0 < i := by
      have hindex := x.index_val_eq_componentStart_add_local I
      change i = _ at hindex
      omega
    have hpNextVal : pNext.val = p.val + 1 := rfl
    have hpNextLeSelected : pNext ≤ D.largeSelectedPosition := by
      change p.val + 1 ≤ D.largeSelectedPosition.val
      omega
    have hpLeNext : p ≤ pNext := by
      change p.val ≤ p.val + 1
      omega
    have hscaleNext : scale ≤ nextScale := by
      have hmono := D.largeAlmostJordan.scaleOrder_mono hpLeNext
      change scale ≤ nextScale
      simpa only [p, scale, nextScale,
        D.largeAlmostJordan_scaleGenerator_common] using hmono
    have hnextScaleSelected : nextScale ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
      have hmono := D.largeAlmostJordan.scaleOrder_mono hpNextLeSelected
      simpa only [nextScale,
        D.largeAlmostJordan_scaleGenerator_selected] using hmono
    have hsourceSelected : sourceEffective =
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) :=
      D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
        p (D.smallCommonPosition c) p scale scale le_rfl
          (hscaleNext.trans hnextScaleSelected) hlt
    have hnextEffective :
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale =
          sourceEffective := by
      calc
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale =
            ordUnit K (D.largeAlmostJordan.normGeneratorUnit
              D.largeSelectedPosition) :=
          D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
            p (D.smallCommonPosition c) pNext scale nextScale hscaleNext
              hnextScaleSelected hlt
        _ = sourceEffective := hsourceSelected.symm
    have hnextRankPos : 0 <
        finrank K (D.largeAlmostJordan.component pNext).carrier :=
      D.largeAlmostJordan.component_finrank_pos pNext
    have hiNext : i + 1 < n := by
      have hval := x.inverse_index_val_next_component
        (x.indexEquiv I).1 pNext (by rw [hposition])
          (x.indexEquiv I).2 hlast hnextRankPos
      have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
        x.indexEquiv.symm_apply_apply I
      have hbound :=
        (x.indexEquiv.symm ⟨pNext, ⟨0, hnextRankPos⟩⟩).isLt
      have hval' :
          (x.indexEquiv.symm ⟨pNext, ⟨0, hnextRankPos⟩⟩).val = i + 1 := by
        calc
          _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
            simpa using hval
          _ = i + 1 := by rw [hcurrent]
      exact hval' ▸ hbound
    have hnextScaleLower : nextScale ≤
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt pNext nextScale
    have hsourceNext :
        a.orderSequence.entry (i + 1) hiNext = sourceEffective := by
      change a.toBONG.order ⟨i + 1, hiNext⟩ = sourceEffective
      have h := x.order_succ_eq_weakJordanExpectedOrder_of_next_component
        I hiNext pNext (by rw [hposition]) hlast hnextRankPos
      simp only [BONG.weakJordanExpectedOrder] at h
      rw [hnextEffective] at h hnextScaleLower
      rw [JordanProfileOrder.localOrder_even_of_scale_le hnextScaleLower
        (by simp)] at h
      simpa only [I] using h
    have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
      rw [← hcoordinates.2]
      exact hlocalPos
    have hevenPrevious : Even (localIndex - 1) := by
      rcases (Nat.not_even_iff_odd.mp hodd) with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have htargetPrevious :
        b.orderSequence.entry (i - 1) (by omega) = targetEffective := by
      change b.order ⟨i - 1, by omega⟩ = targetEffective
      have h := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred
        I hsmallLocalPos
      simp only [BONG.weakJordanExpectedOrder] at h
      rw [htargetScaleAt, htargetEffectiveAt] at h
      simp only [I] at h
      have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by omega
      change b.order ⟨i - 1, by omega⟩ =
        JordanProfileOrder.localOrder scale targetEffective
          ((y.indexEquiv I).2.val - 1) at h
      rw [hprev, JordanProfileOrder.localOrder_even_of_scale_le
        htargetScale hevenPrevious] at h
      exact h
    exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- Aligned specialization of the last-odd common-component case. -/
theorem weakAligned_common_before_last_odd_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hlast :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier)
    (hodd : ¬Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.weakAligned_common_before_last_odd_coordinate_of_alignment
    a b i hi c hposition hbefore
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact hlast
  · exact hodd

/-- An interior coordinate of a common component after the selected
component, with both local neighbours available. -/
theorem weakAligned_common_after_coordinate_of_local_neighbors_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hlocalPos : 0 <
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change 0 < (x.indexEquiv I).2.val at hlocalPos
  change (x.indexEquiv I).2.val + 1 <
    finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      at hlocalNext
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    simpa only [scale] using
      D.largeSelected_scale_lt_common_of_position_lt c hafter
  have heffective : targetEffective ≤ sourceEffective :=
    D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      (D.smallCommonPosition c) (D.largeCommonPosition c) scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_ge
    a.orderSequence b.orderSequence i hi localIndex scale
      sourceEffective targetEffective hsourceScale htargetScale heffective
      hsourceCurrent htargetCurrent
  intro heven
  have hi0 : 0 < i := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change i = _ at hindex
    change 0 < localIndex at hlocalPos
    omega
  have hiNext : i + 1 < n := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
    have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hnextBound :=
      (x.indexEquiv.symm
        ⟨(x.indexEquiv I).1,
          ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
    have hval' :
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          simpa using hval
        _ = i + 1 := by rw [hcurrent]
    exact hval' ▸ hnextBound
  have hoddNext : ¬Even (localIndex + 1) := by
    intro h
    exact (Nat.even_add_one.mp h) heven
  have hoddPrevious : ¬Even (localIndex - 1) := by
    rcases heven with ⟨k, hk⟩
    intro h
    rcases h with ⟨l, hl⟩
    change 0 < localIndex at hlocalPos
    omega
  have hsourceNext :
      a.orderSequence.entry (i + 1) hiNext =
        2 * scale - sourceEffective := by
    change a.order ⟨i + 1, hiNext⟩ = _
    have h := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hiNext hlocalNext
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    simp only [I] at h
    change a.order ⟨i + 1, hiNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_odd_of_scale_le
      hsourceScale hoddNext] at h
    exact h
  have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    exact hlocalPos
  have htargetPrevious :
      b.orderSequence.entry (i - 1) (by omega) =
        2 * scale - targetEffective := by
    change b.order ⟨i - 1, by omega⟩ = _
    have h := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred
      I hsmallLocalPos
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [htargetScaleAt, htargetEffectiveAt] at h
    simp only [I] at h
    have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by omega
    change b.order ⟨i - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val - 1) at h
    rw [hprev, JordanProfileOrder.localOrder_odd_of_scale_le
      htargetScale hoddPrevious] at h
    exact h
  exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- Aligned specialization of the interior after-component case. -/
theorem weakAligned_common_after_coordinate_of_local_neighbors
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hlocalPos : 0 <
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  exact D.weakAligned_common_after_coordinate_of_local_neighbors_of_alignment
    a b i hi c hposition hafter
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions hlocalPos hlocalNext

/-- The first coordinate of a common component after the selected component.
If the small selected component has the same scale, anchor-independence of
the effective norm replaces the strict-scale step in the original proof. -/
theorem weakAligned_common_after_first_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallAfter : D.smallSelectedPosition < D.smallCommonPosition c)
    (hfirst :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val = 0) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let pLarge := D.largeCommonPosition c
  let pSmall := D.smallCommonPosition c
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt pLarge scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt pSmall scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = pLarge at hposition
  change (x.indexEquiv I).2.val = 0 at hfirst
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hpEq : pLarge = pSmall := by
    simpa only [pLarge, pSmall] using hcommonPositions.symm
  have hsmallPosition : (y.indexEquiv I).1 = pSmall := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = pLarge := hposition
      _ = pSmall := hpEq
  have hsmallFirst : (y.indexEquiv I).2.val = 0 := by omega
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    simpa only [scale] using
      D.largeSelected_scale_lt_common_of_position_lt c hafter
  have heffective : targetEffective ≤ sourceEffective :=
    D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      pSmall pLarge scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt pLarge scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt pSmall scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition]
    simp only [pLarge, scale, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition]
    simp only [pSmall, scale, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  by_cases heq : sourceEffective = targetEffective
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent, heq]
  · have hlt : targetEffective < sourceEffective :=
      lt_of_le_of_ne heffective (Ne.symm heq)
    apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_ge
      a.orderSequence b.orderSequence i hi localIndex scale
        sourceEffective targetEffective hsourceScale htargetScale heffective
        hsourceCurrent htargetCurrent
    intro _
    have hsourceStrict : scale < sourceEffective :=
      htargetScale.trans_lt hlt
    have hrankEven := D.largeCommon_componentRank_even_of_scale_lt_effective
      c (by simpa only [pLarge, scale, sourceEffective] using hsourceStrict)
    have hcurrentRankPos : 0 <
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier :=
      D.largeAlmostJordan.component_finrank_pos (x.indexEquiv I).1
    have hlocalNext : (x.indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      rw [hfirst, hposition]
      have hrankEven' : Even
          (finrank K (D.largeAlmostJordan.component pLarge).carrier) := by
        simpa only [pLarge] using hrankEven
      rcases hrankEven' with ⟨k, hk⟩
      have hpos := D.largeAlmostJordan.component_finrank_pos pLarge
      omega
    have hiNext : i + 1 < n := by
      have hval := x.inverse_index_val_local_succ
        (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
      have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
        x.indexEquiv.symm_apply_apply I
      have hnextBound :=
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
      have hval' :
          (x.indexEquiv.symm
            ⟨(x.indexEquiv I).1,
              ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
        calc
          _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
            simpa using hval
          _ = i + 1 := by rw [hcurrent]
      exact hval' ▸ hnextBound
    have hsourceNext :
        a.orderSequence.entry (i + 1) hiNext =
          2 * scale - sourceEffective := by
      change a.order ⟨i + 1, hiNext⟩ = _
      have h := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
        I hiNext hlocalNext
      simp only [BONG.weakJordanExpectedOrder] at h
      rw [hsourceScaleAt, hsourceEffectiveAt] at h
      simp only [I] at h
      change a.order ⟨i + 1, hiNext⟩ =
        JordanProfileOrder.localOrder scale sourceEffective
          (localIndex + 1) at h
      have hodd : ¬Even (localIndex + 1) := by
        rw [show localIndex = 0 by exact hfirst]
        simp
      rw [JordanProfileOrder.localOrder_odd_of_scale_le
        hsourceScale hodd] at h
      exact h
    have hpSmallPos : 0 < pSmall.val := by
      have := hsmallAfter
      omega
    let pPrev : Fin (D.complementComponentCount + 1) :=
      ⟨pSmall.val - 1, by have := pSmall.isLt; omega⟩
    have hpPrevNext : pSmall.val = pPrev.val + 1 := by
      simp only [pPrev]
      omega
    have hpSelectedPrev : D.smallSelectedPosition ≤ pPrev := by
      change D.smallSelectedPosition.val ≤ pSmall.val - 1
      omega
    have hpPrevCurrent : pPrev ≤ pSmall := by
      change pSmall.val - 1 ≤ pSmall.val
      omega
    let prevScale := ordUnit K (D.smallAlmostJordan.scaleGenerator pPrev)
    let prevEffective :=
      D.smallAlmostJordan.effectiveNormOrderAt pPrev prevScale
    have hselectedScalePrev :
        ordUnit K D.input.block.scaleGenerator ≤ prevScale := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono hpSelectedPrev
      simpa only [prevScale,
        D.smallAlmostJordan_scaleGenerator_selected] using hmono
    have hprevScaleCurrent : prevScale ≤ scale := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono hpPrevCurrent
      simpa only [prevScale, pSmall, scale,
        D.smallAlmostJordan_scaleGenerator_common] using hmono
    have hcomplementary : 2 * prevScale - prevEffective =
        2 * scale - targetEffective := by
      by_cases hselectedLt :
          ordUnit K D.input.block.scaleGenerator < scale
      · have htargetSelectedAdjusted : targetEffective =
            JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily scale
              D.smallSelectedPosition :=
          D.small_effectiveNormOrderAt_eq_selected_of_lt
            pSmall pLarge scale hlt
        have hprevSelectedAdjusted : prevEffective =
            JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily prevScale
              D.smallSelectedPosition :=
          D.small_effectiveNormOrderAt_eq_selectedAdjusted_of_lt
            pSmall pLarge pPrev prevScale scale hselectedScalePrev
              hprevScaleCurrent hlt
        rw [hprevSelectedAdjusted, htargetSelectedAdjusted]
        simp only [JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily,
          D.smallAlmostJordan_scaleGenerator_selected]
        rw [if_pos hselectedLt]
        by_cases hprevLt :
            ordUnit K D.input.block.scaleGenerator < prevScale
        · rw [if_pos hprevLt]
          omega
        · rw [if_neg hprevLt]
          omega
      · have hselectedLeScale :
            ordUnit K D.input.block.scaleGenerator ≤ scale := by
          have hmono := D.smallAlmostJordan.scaleOrder_mono hsmallAfter.le
          simpa only [pSmall, scale,
            D.smallAlmostJordan_scaleGenerator_selected,
            D.smallAlmostJordan_scaleGenerator_common] using hmono
        have hselectedEqScale :
            ordUnit K D.input.block.scaleGenerator = scale := by omega
        have hprevScaleEq : prevScale = scale := by omega
        have hprevEffectiveEq : prevEffective = targetEffective := by
          dsimp only [prevEffective, targetEffective]
          rw [hprevScaleEq]
          exact D.smallAlmostJordan.effectiveNormOrderAt_anchor_irrel
            pPrev pSmall scale
        omega
    have hprevRankPos : 0 <
        finrank K (D.smallAlmostJordan.component pPrev).carrier :=
      D.smallAlmostJordan.component_finrank_pos pPrev
    have hcurrentSmallRankPos : 0 <
        finrank K (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier :=
      D.smallAlmostJordan.component_finrank_pos (y.indexEquiv I).1
    have hi0 : 0 < i :=
      y.index_val_pos_of_previous_component I pPrev
        (by rw [hsmallPosition]; exact hpPrevNext) hprevRankPos
    have htargetPrevious :
        b.orderSequence.entry (i - 1) (by omega) =
          2 * scale - targetEffective := by
      change b.toBONG.order ⟨i - 1, by omega⟩ = _
      have h := y.order_pred_eq_weakJordanExpectedOrder_of_previous_component
        I hi0 pPrev (by rw [hsmallPosition]; exact hpPrevNext)
          hsmallFirst hprevRankPos hcurrentSmallRankPos
      simp only [BONG.weakJordanExpectedOrder] at h
      change b.toBONG.order ⟨i - 1, by omega⟩ =
        JordanProfileOrder.localOrder prevScale prevEffective
          (finrank K (D.smallAlmostJordan.component pPrev).carrier - 1) at h
      have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pPrev
      change JordanProfileOrder.localOrder prevScale prevEffective
          (finrank K (D.smallAlmostJordan.component pPrev).carrier - 1) =
        2 * prevScale - prevEffective at hlast
      rw [hlast, hcomplementary] at h
      exact h
    exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- Aligned specialization of the first-coordinate after-component case. -/
theorem weakAligned_common_after_first_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hfirst :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val = 0) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.weakAligned_common_after_first_coordinate_of_alignment
    a b i hi c hposition hafter
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hafter
  · exact hfirst

/-- The last coordinate of a common component after the selected component. -/
theorem weakAligned_common_after_last_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hlast :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change (x.indexEquiv I).2.val + 1 =
    finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      at hlast
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    simpa only [scale] using
      D.largeSelected_scale_lt_common_of_position_lt c hafter
  have heffective : targetEffective ≤ sourceEffective :=
    D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      (D.smallCommonPosition c) (D.largeCommonPosition c) scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.direct
  rw [hsourceCurrent, htargetCurrent]
  apply JordanProfileOrder.localOrder_le_of_effective_ge_at_last
    hsourceScale htargetScale heffective
  · intro hstrict
    have hparity := D.largeCommon_componentRank_even_of_scale_lt_effective
      c hstrict
    change Even (finrank K
      (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier)
    rw [hposition]
    exact hparity
  · exact hlast

/-- Aligned specialization of the last-coordinate after-component case. -/
theorem weakAligned_common_after_last_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hlast :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1).carrier) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi :=
  D.weakAligned_common_after_last_coordinate_of_alignment
    a b i hi c hposition hafter
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    (D.commonPositions_eq_of_selectedPositions_eq hselected c) hlast

/-- Complete certificate for a common component after the aligned selected
component. -/
theorem weakAligned_common_after_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let x := D.largeWeakProfileWitness a
  let I : Fin n := ⟨i, hi⟩
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hfirst : (x.indexEquiv I).2.val = 0
  · exact D.weakAligned_common_after_first_coordinate
      hselected a b i hi c hposition hafter hfirst
  · by_cases hnext : (x.indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
    · exact D.weakAligned_common_after_coordinate_of_local_neighbors
        hselected a b i hi c hposition hafter
          (Nat.pos_of_ne_zero hfirst) hnext
    · have hlast : (x.indexEquiv I).2.val + 1 =
          finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
        have hbound := (x.indexEquiv I).2.isLt
        omega
      exact D.weakAligned_common_after_last_coordinate
        hselected a b i hi c hposition hafter hlast

/-- At every even coordinate in a common component before the selected
component, the source order is directly bounded by the target order. -/
theorem weakAligned_common_before_even_order_le_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore : D.smallCommonPosition c < D.smallSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    a.orderSequence.entry i hi ≤ b.orderSequence.entry i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change Even (x.indexEquiv I).2.val at heven
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    simpa only [scale] using
      D.smallCommon_scale_lt_selected_of_position_lt c hsmallBefore
  have heffective : sourceEffective ≤ targetEffective :=
    D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeWeak_order_eq_localOrder a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  rw [hsourceCurrent, htargetCurrent,
    JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven,
    JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  exact heffective

/-- Certificate wrapper for the direct even-coordinate comparison. -/
theorem weakAligned_common_before_even_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore : D.smallCommonPosition c < D.smallSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi :=
  .direct (D.weakAligned_common_before_even_order_le_of_alignment
    a b i hi c hposition hcoordinates hcommonPositions hsmallBefore heven)

/-- Aligned specialization of the even before-component case. -/
theorem weakAligned_common_before_even_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.weakAligned_common_before_even_coordinate_of_alignment
    a b i hi c hposition
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact heven

/-- Aligned direct inequality at an even coordinate in a common component
strictly before the selected component. -/
theorem weakAligned_common_before_even_order_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).2.val) :
    a.order ⟨i, hi⟩ ≤ b.order ⟨i, hi⟩ := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.weakAligned_common_before_even_order_le_of_alignment
    a b i hi c hposition
    (D.weakProfile_coordinates_eq hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact heven

/-- Every even local coordinate at or before the aligned selected component
has the direct source-to-target order inequality.  This is stronger than the
general Section 5.4 certificate, whose odd coordinates may use the adjacent
Jordan-pair alternative. -/
theorem weakAligned_order_le_of_component_le_selected_of_local_even
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hcomponent :
      ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
        D.largeSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val) :
    a.order I ≤ b.order I := by
  let x := D.largeWeakProfileWitness a
  change (x.indexEquiv I).1 ≤ D.largeSelectedPosition at hcomponent
  rcases lt_or_eq_of_le hcomponent with hbefore | hposition
  · rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
      hselectedPosition | ⟨c, hcommonPosition⟩
    · exact False.elim ((ne_of_lt hbefore) hselectedPosition)
    · apply D.weakAligned_common_before_even_order_le
        hselected a b I.val I.isLt c
      · simpa only [x] using hcommonPosition
      · rw [← hcommonPosition]
        exact hbefore
      · simpa only [x] using heven
  · apply D.weakAligned_selected_order_le hselected a b I
    simpa only [x] using hposition

/-- Complete certificate for a common component before the aligned selected
component. -/
theorem weakAligned_common_before_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let x := D.largeWeakProfileWitness a
  let I : Fin n := ⟨i, hi⟩
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hnext : (x.indexEquiv I).2.val + 1 <
      finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
  · exact D.weakAligned_common_before_coordinate_of_local_succ
      hselected a b i hi c hposition hbefore hnext
  · have hlast : (x.indexEquiv I).2.val + 1 =
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      have hbound := (x.indexEquiv I).2.isLt
      omega
    by_cases heven : Even (x.indexEquiv I).2.val
    · exact D.weakAligned_common_before_even_coordinate
        hselected a b i hi c hposition hbefore heven
    · exact D.weakAligned_common_before_last_odd_coordinate
        hselected a b i hi c hposition hbefore hlast heven

/-- Every coordinate is certified when the distinguished insertion positions
agree, with no restriction on endpoint equal-scale amalgamations. -/
theorem weakAligned_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
    hposition | ⟨c, hposition⟩
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    exact D.weakAligned_selected_order_le hselected a b I hposition
  · rcases lt_or_gt_of_ne
        (D.largeSelectedPosition_ne_common c).symm with hbefore | hafter
    · exact D.weakAligned_common_before_coordinate
        hselected a b i hi c hposition hbefore
    · exact D.weakAligned_common_after_coordinate
        hselected a b i hi c hposition hafter

/-- Complete Section 5.4 order certificate for aligned insertion positions,
including both possible endpoint collisions. -/
theorem weakAligned_orderCertificate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence where
  coordinate i hi := D.weakAligned_coordinate hselected a b i hi

end Lattice.Beli2019Lemma51Data

end Bong
