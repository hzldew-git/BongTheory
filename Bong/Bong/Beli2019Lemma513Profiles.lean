/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanProfilePrefixSum
import Bong.Bong.Beli2019AlmostJordanWeakAligned
import Bong.Bong.Beli2019AlmostJordanWeakUnaryShiftEntries
import Bong.Bong.Beli2019SectionFiveReducedRange

/-!
# Weak Jordan profile input for Beli (2019), Lemma 5.13(ii)

The paper's prefix-parity calculation only uses complete-component volumes
before the current component and an even local boundary in that component.
This file packages that argument independently of the scalar-approximation
construction in Lemma 5.13(i).
-/

open scoped BigOperators

namespace Bong

open Dyadic
open Module

namespace BONG.WeakJordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n t : Nat}

/-- If two weak Jordan profiles have aligned current coordinates, equal
ranks and scales on all complete preceding components, and ordered effective
norms at the current component, a one-step jump at the current BONG order
forces equality of the preceding global prefix sums. -/
theorem prefixSum_eq_of_current_succ
    (a : BONG.GoodBONG q L n) (b : BONG.GoodBONG q M n)
    {W : Lattice.WeakJordanDecomposition q L t}
    {H : Lattice.WeakJordanDecomposition q M t}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (y : WeakJordanOrderProfileWitness b.toBONG H)
    (hW : W.HasImproperEvenRank) (hH : H.HasImproperEvenRank)
    (I : Fin n)
    (hcoordinates :
      (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
        (x.indexEquiv I).2.val = (y.indexEquiv I).2.val)
    (hRankBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      finrank K (W.component k).carrier =
        finrank K (H.component k).carrier)
    (hScaleBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      ordUnit K (W.scaleGenerator k) = ordUnit K (H.scaleGenerator k))
    (hCurrentScale :
      ordUnit K (W.scaleGenerator (x.indexEquiv I).1) =
        ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
    (hEffective :
      W.effectiveNormOrderAt (x.indexEquiv I).1
          (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) ≤
        H.effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (H.scaleGenerator (y.indexEquiv I).1)))
    (hcurrent : b.order I = a.order I + 1) :
    a.orderSequence.prefixSum I.val =
      b.orderSequence.prefixSum I.val := by
  let p := (x.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (W.scaleGenerator p)
  let sourceEffective := W.effectiveNormOrderAt p scale
  let targetEffective := H.effectiveNormOrderAt (y.indexEquiv I).1
    (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
  change scale = ordUnit K (H.scaleGenerator (y.indexEquiv I).1)
    at hCurrentScale
  change sourceEffective ≤ targetEffective at hEffective
  have hyPosition : (y.indexEquiv I).1 = p := hcoordinates.1.symm
  have hyLocal : (y.indexEquiv I).2.val = localIndex := hcoordinates.2.symm
  have htargetScaleAtP : ordUnit K (H.scaleGenerator p) = scale := by
    rw [← hyPosition]
    exact hCurrentScale.symm
  have htargetEffectiveAtP :
      H.effectiveNormOrderAt p (ordUnit K (H.scaleGenerator p)) =
        targetEffective := by
    rw [← hyPosition]
  have hsourceScale : scale ≤ sourceEffective :=
    W.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    calc
      scale = ordUnit K (H.scaleGenerator (y.indexEquiv I).1) :=
        hCurrentScale
      _ ≤ targetEffective :=
        H.targetScale_le_effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex =
        JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 := by
    have hsource := x.order_eq I
    have htarget := y.order_eq I
    simp only [BONG.weakJordanExpectedOrder] at hsource htarget
    change a.order I = JordanProfileOrder.localOrder scale sourceEffective localIndex
      at hsource
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
      targetEffective (y.indexEquiv I).2.val at htarget
    rw [← hCurrentScale, hyLocal] at htarget
    omega
  rw [x.prefixSum_eq_componentPrefix_add_localPrefix a I,
    y.prefixSum_eq_componentPrefix_add_localPrefix b I]
  simp only [hyPosition, hyLocal]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [W.localPrefixSum_componentRank_eq hW k,
      H.localPrefixSum_componentRank_eq hH k,
      ← hRankBefore k hk, ← hScaleBefore k hk]
  · rw [htargetEffectiveAtP, htargetScaleAtP]
    change JordanProfileOrder.localPrefixSum scale sourceEffective localIndex =
      JordanProfileOrder.localPrefixSum scale targetEffective localIndex
    exact JordanProfileOrder.localPrefixSum_eq_of_effective_le_of_current_succ
      hsourceScale htargetScale hEffective hlocalCurrent

/-- If two aligned weak Jordan coordinates have the same component scale
and the same current order, then their effective norm parameters agree.
Consequently the global prefix sums through the current coordinate agree.
This is the local-profile core of Lemma 5.17(ii). -/
theorem prefixSum_succ_eq_of_current_eq
    (a : BONG.GoodBONG q L n) (b : BONG.GoodBONG q M n)
    {W : Lattice.WeakJordanDecomposition q L t}
    {H : Lattice.WeakJordanDecomposition q M t}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (y : WeakJordanOrderProfileWitness b.toBONG H)
    (hW : W.HasImproperEvenRank) (hH : H.HasImproperEvenRank)
    (I : Fin n)
    (hcoordinates :
      (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
        (x.indexEquiv I).2.val = (y.indexEquiv I).2.val)
    (hRankBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      finrank K (W.component k).carrier =
        finrank K (H.component k).carrier)
    (hScaleBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      ordUnit K (W.scaleGenerator k) = ordUnit K (H.scaleGenerator k))
    (hCurrentScale :
      ordUnit K (W.scaleGenerator (x.indexEquiv I).1) =
        ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
    (hcurrent : a.order I = b.order I) :
    a.orderSequence.prefixSum (I.val + 1) =
      b.orderSequence.prefixSum (I.val + 1) := by
  let p := (x.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (W.scaleGenerator p)
  let sourceEffective := W.effectiveNormOrderAt p scale
  let targetEffective := H.effectiveNormOrderAt (y.indexEquiv I).1
    (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
  change scale = ordUnit K (H.scaleGenerator (y.indexEquiv I).1)
    at hCurrentScale
  have hyPosition : (y.indexEquiv I).1 = p := hcoordinates.1.symm
  have hyLocal : (y.indexEquiv I).2.val = localIndex := hcoordinates.2.symm
  have htargetScaleAtP : ordUnit K (H.scaleGenerator p) = scale := by
    rw [← hyPosition]
    exact hCurrentScale.symm
  have htargetEffectiveAtP :
      H.effectiveNormOrderAt p (ordUnit K (H.scaleGenerator p)) =
        targetEffective := by
    rw [← hyPosition]
  have hsourceScale : scale ≤ sourceEffective :=
    W.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    calc
      scale = ordUnit K (H.scaleGenerator (y.indexEquiv I).1) :=
        hCurrentScale
      _ ≤ targetEffective :=
        H.targetScale_le_effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    have hsource := x.order_eq I
    have htarget := y.order_eq I
    simp only [BONG.weakJordanExpectedOrder] at hsource htarget
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsource
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (H.scaleGenerator (y.indexEquiv I).1))
      targetEffective (y.indexEquiv I).2.val at htarget
    rw [← hCurrentScale, hyLocal] at htarget
    omega
  have heffective : sourceEffective = targetEffective :=
    JordanProfileOrder.effective_eq_of_localOrder_eq
      hsourceScale htargetScale hlocalCurrent
  have hprefix :
      a.orderSequence.prefixSum I.val =
        b.orderSequence.prefixSum I.val := by
    rw [x.prefixSum_eq_componentPrefix_add_localPrefix a I,
      y.prefixSum_eq_componentPrefix_add_localPrefix b I]
    simp only [hyPosition, hyLocal]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [W.localPrefixSum_componentRank_eq hW k,
        H.localPrefixSum_componentRank_eq hH k,
        ← hRankBefore k hk, ← hScaleBefore k hk]
    · change JordanProfileOrder.localPrefixSum scale sourceEffective localIndex =
        JordanProfileOrder.localPrefixSum
          (ordUnit K (H.scaleGenerator p))
          (H.effectiveNormOrderAt p (ordUnit K (H.scaleGenerator p)))
          localIndex
      rw [htargetEffectiveAtP, htargetScaleAtP, heffective]
  have hentry :
      a.orderSequence.entryOrZero I.val =
        b.orderSequence.entryOrZero I.val := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence I.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence I.isLt]
    simpa only [BONG.GoodBONG.orderSequence_at] using hcurrent
  rw [a.orderSequence.prefixSum_succ, b.orderSequence.prefixSum_succ,
    hprefix, hentry]

/-- At the first local coordinate, equality of all complete preceding
component volumes already gives equality of the global prefixes; no relation
between the current component scales is needed. -/
theorem prefixSum_eq_of_local_zero
    (a : BONG.GoodBONG q L n) (b : BONG.GoodBONG q M n)
    {W : Lattice.WeakJordanDecomposition q L t}
    {H : Lattice.WeakJordanDecomposition q M t}
    (x : WeakJordanOrderProfileWitness a.toBONG W)
    (y : WeakJordanOrderProfileWitness b.toBONG H)
    (hW : W.HasImproperEvenRank) (hH : H.HasImproperEvenRank)
    (I : Fin n)
    (hPosition : (x.indexEquiv I).1 = (y.indexEquiv I).1)
    (hxLocal : (x.indexEquiv I).2.val = 0)
    (hyLocal : (y.indexEquiv I).2.val = 0)
    (hRankBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      finrank K (W.component k).carrier =
        finrank K (H.component k).carrier)
    (hScaleBefore : ∀ k ∈ Finset.Iio (x.indexEquiv I).1,
      ordUnit K (W.scaleGenerator k) = ordUnit K (H.scaleGenerator k)) :
    a.orderSequence.prefixSum I.val =
      b.orderSequence.prefixSum I.val := by
  rw [x.prefixSum_eq_componentPrefix_add_localPrefix a I,
    y.prefixSum_eq_componentPrefix_add_localPrefix b I]
  simp only [← hPosition, hxLocal, hyLocal,
    JordanProfileOrder.localPrefixSum_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [W.localPrefixSum_componentRank_eq hW k,
    H.localPrefixSum_componentRank_eq hH k,
    ← hRankBefore k hk, ← hScaleBefore k hk]

end BONG.WeakJordanOrderProfileWitness

namespace JordanProfileOrder

/-- Consecutive entries of an alternating local Jordan profile whose
effective norm is at most one above its scale never differ by exactly one
in the increasing direction. -/
theorem localOrder_ne_pred_add_one_of_effective_le_add_one
    (scale effective : Int) (hscale : scale ≤ effective)
    (heffective : effective ≤ scale + 1) (j : Nat) (hj : 0 < j) :
    localOrder scale effective j ≠
      localOrder scale effective (j - 1) + 1 := by
  intro h
  by_cases heven : Even j
  · have hoddPrevious : ¬Even (j - 1) := by
      rcases heven with ⟨k, hk⟩
      intro hprevious
      rcases hprevious with ⟨ell, hell⟩
      omega
    rw [localOrder_even_of_scale_le hscale heven,
      localOrder_odd_of_scale_le hscale hoddPrevious] at h
    omega
  · have hevenPrevious : Even (j - 1) := by
      rcases Nat.not_even_iff_odd.mp heven with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    rw [localOrder_odd_of_scale_le hscale heven,
      localOrder_even_of_scale_le hscale hevenPrevious] at h
    omega

end JordanProfileOrder

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Before two aligned distinguished components, the two weak
almost-Jordan decompositions have the same scale at every position. -/
theorem weakAligned_scaleOrder_eq_before_selected
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) := by
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨c, hposition⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hcommon := D.commonPositions_eq_of_selectedPositions_eq hselected c
    rw [D.largeAlmostJordan_scaleGenerator_common, ← hcommon,
      D.smallAlmostJordan_scaleGenerator_common]

/-- At a common component before aligned distinguished components, the
larger-lattice effective norm order is at most the smaller-lattice one. -/
theorem weakAligned_effectiveNormOrderAt_le_before_selected
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.smallAlmostJordan.scaleGenerator p)) := by
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨c, hposition⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hcommon := D.commonPositions_eq_of_selectedPositions_eq hselected c
    have hsmallBefore :
        D.smallCommonPosition c < D.smallSelectedPosition := by
      rw [hcommon, hselected]
      exact hp
    have hscaleLt :
        ordUnit K (D.complementStrictWeak.scaleGenerator c) <
          ordUnit K D.input.block.scaleGenerator :=
      D.smallCommon_scale_lt_selected_of_position_lt c hsmallBefore
    have heffective := D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c)
      (ordUnit K (D.complementStrictWeak.scaleGenerator c)) hscaleLt
    have hsmallScaleAtLarge :
        ordUnit K
            (D.smallAlmostJordan.scaleGenerator (D.largeCommonPosition c)) =
          ordUnit K (D.complementStrictWeak.scaleGenerator c) := by
      rw [← hcommon, D.smallAlmostJordan_scaleGenerator_common]
    simpa only [D.largeAlmostJordan_scaleGenerator_common,
      hcommon, hsmallScaleAtLarge] using heffective

/-- Lemma 5.13(ii) on a coordinate strictly before aligned distinguished
components.  The current one-step order jump forces equality of the global
prefixes ending immediately before that coordinate. -/
theorem weakAligned_previousPrefixSum_eq_of_current_succ_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hcurrent : b.order I = a.order I + 1) :
    a.orderSequence.prefixSum I.val =
      b.orderSequence.prefixSum I.val := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  apply x.prefixSum_eq_of_current_succ a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hcoordinates
  · intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  · intro k hk
    exact D.weakAligned_scaleOrder_eq_before_selected hselected k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · rw [← hcoordinates.1]
    exact D.weakAligned_scaleOrder_eq_before_selected hselected
      (x.indexEquiv I).1 hbefore
  · rw [← hcoordinates.1]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected (x.indexEquiv I).1 hbefore
  · exact hcurrent

/-- On a coordinate before aligned distinguished components, equality of
the current orders forces equality of the global prefixes through that
coordinate. -/
theorem weakAligned_prefixSum_succ_eq_of_current_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hcurrent : a.order I = b.order I) :
    a.orderSequence.prefixSum (I.val + 1) =
      b.orderSequence.prefixSum (I.val + 1) := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  apply x.prefixSum_succ_eq_of_current_eq a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hcoordinates
  · intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  · intro k hk
    exact D.weakAligned_scaleOrder_eq_before_selected hselected k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · rw [← hcoordinates.1]
    exact D.weakAligned_scaleOrder_eq_before_selected hselected
      (x.indexEquiv I).1 hbefore
  · exact hcurrent

/-- At the first local coordinate of aligned distinguished components, the
preceding global prefixes agree.  This is the endpoint used when the
distinguished block is binary. -/
theorem weakAligned_previousPrefixSum_eq_at_selected_local_zero
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv I).2.val = 0) :
    a.orderSequence.prefixSum I.val =
      b.orderSequence.prefixSum I.val := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  apply x.prefixSum_eq_of_local_zero a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hcoordinates.1 hlocal
    (hcoordinates.2.symm.trans hlocal)
  · intro k hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  · intro k hk
    apply D.weakAligned_scaleOrder_eq_before_selected hselected k
    have hk' := Finset.mem_Iio.mp hk
    rw [hposition] at hk'
    exact hk'

/-- With aligned insertion positions, the rank prefix of the larger weak
profile at the distinguished component is the reduced-range start defined
from the smaller profile. -/
theorem weakAligned_largeSelectedStart_eq_smallSelectedStart
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition) :
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) =
      D.smallSelectedStart := by
  classical
  rw [smallSelectedStart, hselected]
  apply Finset.sum_congr rfl
  intro p _hp
  exact congrFun (D.almostJordan_componentRank_eq hselected) p

/-- A coordinate in the exact range `n_{k₁} + a - 1` of Lemma 5.17
is either strictly before the distinguished component or is its first local
coordinate.  This statement uses the larger profile and therefore remains
valid in the unary-transposition case. -/
theorem lemma517Range_large_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i) :
    let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
    let x := D.largeWeakProfileWitness a
    (x.indexEquiv I).1 < D.largeSelectedPosition ∨
      ((x.indexEquiv I).1 = D.largeSelectedPosition ∧
        (x.indexEquiv I).2.val = 0) := by
  classical
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  let x := D.largeWeakProfileWitness a
  let p := (x.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  change p < D.largeSelectedPosition ∨
    (p = D.largeSelectedPosition ∧ localIndex = 0)
  change i.val ≤ D.largeSelectedStart +
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1 at hi
  have hglobal := x.index_val_eq_componentStart_add_local I
  change i.val - 1 =
    (∑ k ∈ Finset.Iio p,
      finrank K (D.largeAlmostJordan.component k).carrier) + localIndex
    at hglobal
  let selectedRank := finrank K D.input.block.component.carrier
  have hselectedRankPos : 0 < selectedRank := by
    rcases D.rank_one_or_two with h | h <;>
      dsimp only [selectedRank] <;> omega
  have hselectedRankLe : selectedRank ≤ 2 := by
    rcases D.rank_one_or_two with h | h <;>
      dsimp only [selectedRank] <;> omega
  rw [D.largeAlmostJordan_finrank_selected] at hi
  change i.val ≤ D.largeSelectedStart + selectedRank - 1 at hi
  by_cases hbefore : p < D.largeSelectedPosition
  · exact Or.inl hbefore
  · right
    have hselectedLe : D.largeSelectedPosition ≤ p := le_of_not_gt hbefore
    by_cases hposition : p = D.largeSelectedPosition
    · refine ⟨hposition, ?_⟩
      have hlocalBound := (x.indexEquiv I).2.isLt
      change localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier at hlocalBound
      rw [hposition, D.largeAlmostJordan_finrank_selected] at hlocalBound
      change localIndex < selectedRank at hlocalBound
      rw [hposition] at hglobal
      change i.val - 1 = D.largeSelectedStart + localIndex at hglobal
      omega
    · have hselectedLt : D.largeSelectedPosition < p :=
        lt_of_le_of_ne hselectedLe (Ne.symm hposition)
      have hsubset : Finset.Iic D.largeSelectedPosition ⊆ Finset.Iio p := by
        intro k hk
        exact Finset.mem_Iio.mpr
          ((Finset.mem_Iic.mp hk).trans_lt hselectedLt)
      have hsumLe :
          (∑ k ∈ Finset.Iic D.largeSelectedPosition,
              finrank K (D.largeAlmostJordan.component k).carrier) ≤
            ∑ k ∈ Finset.Iio p,
              finrank K (D.largeAlmostJordan.component k).carrier :=
        Finset.sum_le_sum_of_subset hsubset
      rw [sum_Iic_eq_sum_Iio_add,
        D.largeAlmostJordan_finrank_selected] at hsumLe
      change D.largeSelectedStart + selectedRank ≤ _ at hsumLe
      omega

/-- On the direct range of Lemma 5.13, an aligned weak-profile coordinate
is either strictly before the distinguished component or is its first local
coordinate.  The unary distinguished component is therefore never reached
on this one-based boundary range. -/
theorem weakAligned_reducedRange_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (i : RepresentationIndex n n) (hi : D.DefectReducedRange i) :
    let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
    let x := D.largeWeakProfileWitness a
    (x.indexEquiv I).1 < D.largeSelectedPosition ∨
      ((x.indexEquiv I).1 = D.largeSelectedPosition ∧
        (x.indexEquiv I).2.val = 0) := by
  classical
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  let x := D.largeWeakProfileWitness a
  let p := (x.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  change p < D.largeSelectedPosition ∨
    (p = D.largeSelectedPosition ∧ localIndex = 0)
  change i.val ≤ D.smallSelectedStart +
    finrank K
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1 at hi
  have hglobal := x.index_val_eq_componentStart_add_local I
  change i.val - 1 =
    (∑ k ∈ Finset.Iio p,
      finrank K (D.largeAlmostJordan.component k).carrier) + localIndex
    at hglobal
  have hstart :=
    D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
  let selectedRank := finrank K D.input.block.component.carrier
  have hselectedRankPos : 0 < selectedRank := by
    rcases D.rank_one_or_two with h | h <;>
      dsimp only [selectedRank] <;> omega
  have hselectedRankLe : selectedRank ≤ 2 := by
    rcases D.rank_one_or_two with h | h <;>
      dsimp only [selectedRank] <;> omega
  rw [D.smallAlmostJordan_finrank_selected] at hi
  change i.val ≤ D.smallSelectedStart + selectedRank - 1 at hi
  by_cases hbefore : p < D.largeSelectedPosition
  · exact Or.inl hbefore
  · right
    have hselectedLe : D.largeSelectedPosition ≤ p := le_of_not_gt hbefore
    by_cases hposition : p = D.largeSelectedPosition
    · refine ⟨hposition, ?_⟩
      have hlocalBound := (x.indexEquiv I).2.isLt
      change localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier at hlocalBound
      rw [hposition, D.largeAlmostJordan_finrank_selected] at hlocalBound
      change localIndex < selectedRank at hlocalBound
      rw [hposition, hstart] at hglobal
      omega
    · have hselectedLt : D.largeSelectedPosition < p :=
        lt_of_le_of_ne hselectedLe (Ne.symm hposition)
      have hsubset : Finset.Iic D.largeSelectedPosition ⊆ Finset.Iio p := by
        intro k hk
        exact Finset.mem_Iio.mpr
          ((Finset.mem_Iic.mp hk).trans_lt hselectedLt)
      have hsumLe :
          (∑ k ∈ Finset.Iic D.largeSelectedPosition,
              finrank K (D.largeAlmostJordan.component k).carrier) ≤
            ∑ k ∈ Finset.Iio p,
              finrank K (D.largeAlmostJordan.component k).carrier :=
        Finset.sum_le_sum_of_subset hsubset
      rw [sum_Iic_eq_sum_Iio_add,
        D.largeAlmostJordan_finrank_selected, hstart] at hsumLe
      change D.smallSelectedStart + selectedRank ≤ _ at hsumLe
      omega

/-- Lemma 5.13(ii) for the direct reduced range in the aligned insertion
case, stated with the paper's one-based representation boundary. -/
theorem weakAligned_previousPrefixSum_eq_of_current_succ_reduced
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.DefectReducedRange i)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.orderSequence.prefixSum (i.val - 1) =
      b.orderSequence.prefixSum (i.val - 1) := by
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hcurrent' : b.order I = a.order I + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega)] at hcurrent
    simpa only [I, BONG.GoodBONG.orderSequence_at] using hcurrent
  rcases D.weakAligned_reducedRange_coordinate hselected a i hi with
    hbefore | ⟨hposition, hlocal⟩
  · exact D.weakAligned_previousPrefixSum_eq_of_current_succ_before_selected
      hselected a b I hbefore hcurrent'
  · exact D.weakAligned_previousPrefixSum_eq_at_selected_local_zero
      hselected a b I hposition hlocal

/-- Before the exceptional interval of the unary adjacent transposition,
the two weak almost-Jordan profiles have equal scales positionwise. -/
theorem weakUnaryShift_scaleOrder_eq_before_selected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) := by
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨c, hposition⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hne : c ≠ i₀ := by
      intro h
      subst c
      have hright :=
        D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      have hrightVal := congrArg Fin.val hright
      change (D.largeCommonPosition i₀).val <
        D.largeSelectedPosition.val at hp
      omega
    have hcommon :=
      D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
    rw [D.largeAlmostJordan_scaleGenerator_common, ← hcommon,
      D.smallAlmostJordan_scaleGenerator_common]

/-- Before the unary exceptional interval, the effective norm order has
the same direction as in the aligned common-component calculation. -/
theorem weakUnaryShift_effectiveNormOrderAt_le_before_selected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.smallAlmostJordan.scaleGenerator p)) := by
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨c, hposition⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hne : c ≠ i₀ := by
      intro h
      subst c
      have hright :=
        D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      have hrightVal := congrArg Fin.val hright
      change (D.largeCommonPosition i₀).val <
        D.largeSelectedPosition.val at hp
      omega
    have hcommon :=
      D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
    have hsmallBefore :
        D.smallCommonPosition c < D.smallSelectedPosition := by
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      rw [hcommon]
      change (D.largeCommonPosition c).val < D.smallSelectedPosition.val
      omega
    have hscaleLt :
        ordUnit K (D.complementStrictWeak.scaleGenerator c) <
          ordUnit K D.input.block.scaleGenerator :=
      D.smallCommon_scale_lt_selected_of_position_lt c hsmallBefore
    have heffective := D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c)
      (ordUnit K (D.complementStrictWeak.scaleGenerator c)) hscaleLt
    have hsmallScaleAtLarge :
        ordUnit K
            (D.smallAlmostJordan.scaleGenerator (D.largeCommonPosition c)) =
          ordUnit K (D.complementStrictWeak.scaleGenerator c) := by
      rw [← hcommon, D.smallAlmostJordan_scaleGenerator_common]
    simpa only [D.largeAlmostJordan_scaleGenerator_common,
      hcommon, hsmallScaleAtLarge] using heffective

/-- Lemma 5.13(ii) at every coordinate strictly before the unary
exceptional interval. -/
theorem weakUnaryShift_previousPrefixSum_eq_of_current_succ_before_interval
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hcurrent : b.order I = a.order I + 1) :
    a.orderSequence.prefixSum I.val =
      b.orderSequence.prefixSum I.val := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_before
    hfin i₀ hi₀ a b I hbefore
  apply x.prefixSum_eq_of_current_succ a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hcoordinates
  · intro k hk
    exact D.weakUnaryShift_componentRank_eq_before hfin i₀ hi₀ k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · intro k hk
    exact D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · rw [← hcoordinates.1]
    exact D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀
      (x.indexEquiv I).1 hbefore
  · rw [← hcoordinates.1]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  · exact hcurrent

/-- Equality of the current orders before the unary exceptional interval
forces equality of the global prefixes through that coordinate. -/
theorem weakUnaryShift_prefixSum_succ_eq_of_current_eq_before_interval
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hcurrent : a.order I = b.order I) :
    a.orderSequence.prefixSum (I.val + 1) =
      b.orderSequence.prefixSum (I.val + 1) := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_before
    hfin i₀ hi₀ a b I hbefore
  apply x.prefixSum_succ_eq_of_current_eq a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hcoordinates
  · intro k hk
    exact D.weakUnaryShift_componentRank_eq_before hfin i₀ hi₀ k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · intro k hk
    exact D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ k
      ((Finset.mem_Iio.mp hk).trans hbefore)
  · rw [← hcoordinates.1]
    exact D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀
      (x.indexEquiv I).1 hbefore
  · exact hcurrent

/-- The reduced-range start on the smaller side is the end of the
intermediate common component in the unary adjacent-transposition case. -/
theorem weakUnaryShift_smallSelectedStart_eq_intervalEnd
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.smallSelectedStart =
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) +
          finrank K (D.complementStrictWeak.component i₀).carrier := by
  simpa only [smallSelectedStart] using
    D.weakUnaryShift_smallPrefixRank_at_smallSelected hfin i₀ hi₀

/-- At the first coordinate of the unary exceptional interval, both weak
profiles have empty local prefix and equal complete preceding volumes. -/
theorem weakUnaryShift_previousPrefixSum_eq_at_intervalStart
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier
    a.orderSequence.prefixSum start = b.orderSequence.prefixSum start := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let commonRank := finrank K (D.complementStrictWeak.component i₀).carrier
  have hcommonRankPos : 0 < commonRank := by
    exact D.complementStrictWeak.component_finrank_pos i₀
  have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
  let I : Fin n := ⟨start, by
    dsimp only [start, commonRank] at hbound ⊢
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hlargeRank := D.weakUnaryShift_largeComponentRank_selected hfin
  let largeZero : Fin
      (finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier) :=
    ⟨0, by rw [hlargeRank]; omega⟩
  have hxI : I =
      x.indexEquiv.symm ⟨D.largeSelectedPosition, largeZero⟩ := by
    apply Fin.ext
    exact (x.inverse_index_val D.largeSelectedPosition largeZero).symm
  have hxCoordinates :
      x.indexEquiv I = ⟨D.largeSelectedPosition, largeZero⟩ := by
    rw [hxI, x.indexEquiv.apply_symm_apply]
  have hsmallRank :=
    D.weakUnaryShift_smallComponentRank_at_largeSelected hfin i₀ hi₀
  let smallZero : Fin
      (finrank K
        (D.smallAlmostJordan.component D.largeSelectedPosition).carrier) :=
    ⟨0, by rw [hsmallRank]; exact hcommonRankPos⟩
  have hprefix := D.weakUnaryShift_prefixRank_eq hfin i₀ hi₀
  have hyI : I =
      y.indexEquiv.symm ⟨D.largeSelectedPosition, smallZero⟩ := by
    apply Fin.ext
    have hinverse := y.inverse_index_val D.largeSelectedPosition smallZero
    dsimp only [I, start, smallZero, Fin.val_mk] at hinverse ⊢
    rw [hinverse, ← hprefix]
    omega
  have hyCoordinates :
      y.indexEquiv I = ⟨D.largeSelectedPosition, smallZero⟩ := by
    rw [hyI, y.indexEquiv.apply_symm_apply]
  apply x.prefixSum_eq_of_local_zero a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I
  · rw [hxCoordinates, hyCoordinates]
  · rw [hxCoordinates]
  · rw [hyCoordinates]
  · intro k hk
    apply D.weakUnaryShift_componentRank_eq_before hfin i₀ hi₀ k
    rw [hxCoordinates] at hk
    exact Finset.mem_Iio.mp hk
  · intro k hk
    apply D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ k
    rw [hxCoordinates] at hk
    exact Finset.mem_Iio.mp hk

/-- Lemma 5.13(ii) on the direct reduced range in the unique unary
adjacent-transposition case.  Inside the exceptional interval, a current
one-step jump can only occur at its first coordinate; all later consecutive
local-profile entries differ by zero or two. -/
theorem weakUnaryShift_previousPrefixSum_eq_of_current_succ_reduced
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.DefectReducedRange i)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.orderSequence.prefixSum (i.val - 1) =
      b.orderSequence.prefixSum (i.val - 1) := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let commonRank := finrank K (D.complementStrictWeak.component i₀).carrier
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hcurrent' : b.order I = a.order I + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega)] at hcurrent
    simpa only [I, BONG.GoodBONG.orderSequence_at] using hcurrent
  have hcommonRankPos : 0 < commonRank := by
    exact D.complementStrictWeak.component_finrank_pos i₀
  have hstartEnd :=
    D.weakUnaryShift_smallSelectedStart_eq_intervalEnd hfin i₀ hi₀
  change D.smallSelectedStart = start + commonRank at hstartEnd
  have hiEnd : i.val ≤ start + commonRank := by
    change i.val ≤ D.smallSelectedStart +
      finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      at hi
    rw [hstartEnd, D.smallAlmostJordan_finrank_selected, hfin] at hi
    omega
  change a.orderSequence.prefixSum I.val =
    b.orderSequence.prefixSum I.val
  by_cases hbeforeIndex : I.val < start
  · have hbeforeComponent :=
      D.weakUnaryShift_component_before_of_index_lt_start a I hbeforeIndex
    exact D.weakUnaryShift_previousPrefixSum_eq_of_current_succ_before_interval
      hfin i₀ hi₀ a b I hbeforeComponent hcurrent'
  · have hstartLe : start ≤ I.val := le_of_not_gt hbeforeIndex
    by_cases hstartEq : I.val = start
    · rw [hstartEq]
      simpa only [start] using
        D.weakUnaryShift_previousPrefixSum_eq_at_intervalStart
          hfin i₀ hi₀ a b
    · have hstartLt : start < I.val :=
        lt_of_le_of_ne hstartLe (Ne.symm hstartEq)
      have hindexLtEnd : I.val < start + commonRank := by
        dsimp only [I, Fin.val_mk] at hstartLt ⊢
        omega
      let j := I.val - start
      have hjPos : 0 < j := by
        dsimp only [j]
        omega
      have hjLt : j < commonRank := by
        dsimp only [j]
        omega
      have hjPredLt : j - 1 < commonRank := by omega
      let scale := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
      let effective := D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀) scale
      have hlargeIndex : I.val = start + ((j - 1) + 1) := by
        dsimp only [j]
        omega
      have hsmallIndex : I.val = start + j := by
        dsimp only [j]
        omega
      have hlargeCurrent : a.order I =
          JordanProfileOrder.localOrder scale effective (j - 1) := by
        have h := D.weakUnaryShift_largeCommon_entry
          hfin i₀ hi₀ a (j - 1) hjPredLt
        calc
          a.order I = a.orderSequence.entry I.val I.isLt := rfl
          _ = a.orderSequence.entry (start + ((j - 1) + 1))
                (by have := I.isLt; omega) :=
            weakOrderSequence_entry_eq_of_index_eq a.orderSequence
              I.val (start + ((j - 1) + 1)) I.isLt
                (by have := I.isLt; omega) hlargeIndex
          _ = JordanProfileOrder.localOrder scale effective (j - 1) := by
            simpa only [start, scale, effective] using h
      have hsmallCurrent : b.order I =
          JordanProfileOrder.localOrder scale effective j := by
        have h := D.weakUnaryShift_smallCommon_entry
          hfin i₀ hi₀ a b j hjLt
        calc
          b.order I = b.orderSequence.entry I.val I.isLt := rfl
          _ = b.orderSequence.entry (start + j)
                (by have := I.isLt; omega) :=
            weakOrderSequence_entry_eq_of_index_eq b.orderSequence
              I.val (start + j) I.isLt
                (by have := I.isLt; omega) hsmallIndex
          _ = JordanProfileOrder.localOrder scale effective j := by
            simpa only [start, scale, effective] using h
      have heffectiveBounds :=
        D.unaryShift_commonEffectiveNormOrder_bounds hfin i₀ hi₀
      change scale ≤ effective ∧ effective ≤ scale + 1
        at heffectiveBounds
      exact ((JordanProfileOrder.localOrder_ne_pred_add_one_of_effective_le_add_one
        scale effective heffectiveBounds.1 heffectiveBounds.2 j hjPos) (by
          rw [hlargeCurrent, hsmallCurrent] at hcurrent'
          exact hcurrent')).elim

/-- Lemma 5.17(ii)'s prefix-sum assertion in the aligned case.  The exact
`n_{k₁} + a - 1` range ensures that only a component before the selected
block or the selected block's first coordinate can occur. -/
theorem weakAligned_prefixSum_eq_of_current_eq_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.orderSequence.prefixSum i.val =
      b.orderSequence.prefixSum i.val := by
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hcurrent' : a.order I = b.order I := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega)] at hcurrent
    simpa only [I, BONG.GoodBONG.orderSequence_at] using hcurrent
  have hthrough :
      a.orderSequence.prefixSum (I.val + 1) =
        b.orderSequence.prefixSum (I.val + 1) := by
    rcases D.lemma517Range_large_coordinate a i hi with
      hbefore | ⟨hposition, hlocal⟩
    · exact D.weakAligned_prefixSum_succ_eq_of_current_eq_before_selected
        hselected a b I hbefore hcurrent'
    · have hprevious :=
        D.weakAligned_previousPrefixSum_eq_at_selected_local_zero
          hselected a b I hposition hlocal
      have hentry :
          a.orderSequence.entryOrZero I.val =
            b.orderSequence.entryOrZero I.val := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence I.isLt,
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence I.isLt]
        simpa only [BONG.GoodBONG.orderSequence_at] using hcurrent'
      rw [a.orderSequence.prefixSum_succ,
        b.orderSequence.prefixSum_succ, hprevious, hentry]
  have hindex : I.val + 1 = i.val := by
    dsimp only [I, Fin.val_mk]
    have := i.pos
    omega
  simpa only [hindex] using hthrough

/-- Lemma 5.17(ii)'s prefix-sum assertion in the exceptional unary case.
Unlike the broader Lemma 5.13 range, the Lemma 5.17 cutoff stops before the
transposed interval, so the ordinary aligned-profile calculation applies. -/
theorem weakUnaryShift_prefixSum_eq_of_current_eq_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.orderSequence.prefixSum i.val =
      b.orderSequence.prefixSum i.val := by
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hcurrent' : a.order I = b.order I := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega)] at hcurrent
    simpa only [I, BONG.GoodBONG.orderSequence_at] using hcurrent
  have hbeforeIndex : I.val < D.largeSelectedStart := by
    change i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hi
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hi
    dsimp only [I, Fin.val_mk]
    have := i.pos
    omega
  have hbefore :=
    D.weakUnaryShift_component_before_of_index_lt_start a I (by
      simpa only [largeSelectedStart] using hbeforeIndex)
  have hthrough :=
    D.weakUnaryShift_prefixSum_succ_eq_of_current_eq_before_interval
      hfin i₀ hi₀ a b I hbefore hcurrent'
  have hindex : I.val + 1 = i.val := by
    dsimp only [I, Fin.val_mk]
    have := i.pos
    omega
  simpa only [hindex] using hthrough

/-- Weak-profile proof of the prefix-sum part of Beli (2019), Lemma
5.17(ii), uniformly for distinguished blocks of rank one or two. -/
theorem weakAllRanks_prefixSum_eq_of_current_eq_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.orderSequence.prefixSum i.val =
      b.orderSequence.prefixSum i.val := by
  rcases D.rank_one_or_two with hOne | hTwo
  · rcases D.selectedPositions_unary_alternative hOne with
      hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
    · exact D.weakAligned_prefixSum_eq_of_current_eq_lemma517Range
        hselected a b i hi hcurrent
    · exact D.weakUnaryShift_prefixSum_eq_of_current_eq_lemma517Range
        hOne i₀ hi₀ a b i hi hcurrent
  · exact D.weakAligned_prefixSum_eq_of_current_eq_lemma517Range
      (D.selectedPositions_eq_of_rank_two hTwo) a b i hi hcurrent

/-- Complete weak-profile proof of Beli (2019), Lemma 5.13(ii), on the
direct reduced range.  This combines the binary/aligned case, the aligned
unary case, and the unique unary adjacent transposition. -/
theorem weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.DefectReducedRange i)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.orderSequence.prefixSum (i.val - 1) =
      b.orderSequence.prefixSum (i.val - 1) := by
  rcases D.rank_one_or_two with hOne | hTwo
  · rcases D.selectedPositions_unary_alternative hOne with
      hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
    · exact D.weakAligned_previousPrefixSum_eq_of_current_succ_reduced
        hselected a b i hi hcurrent
    · exact D.weakUnaryShift_previousPrefixSum_eq_of_current_succ_reduced
        hOne i₀ hi₀ a b i hi hcurrent
  · exact D.weakAligned_previousPrefixSum_eq_of_current_succ_reduced
      (D.selectedPositions_eq_of_rank_two hTwo) a b i hi hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
