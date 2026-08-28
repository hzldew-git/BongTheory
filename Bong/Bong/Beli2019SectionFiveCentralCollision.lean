/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralSelected

/-!
# Beli (2019), Section 5: the selected binary collision branch

This file constructs the strict collision resolution at the selected binary
component.  The prescribed norm generator is supported in the old selected
summand of the merged component.  Resolved Lemma 3.7(iii) then supplies the
central approximation model, including the terminal Jordan-component case.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

private noncomputable def equalComponentIsometry
    (C E : Lattice.QuadraticSublattice q) (h : C = E) :
    Lattice.Isometry C.space E.space C.lattice E.lattice := by
  subst E
  exact Lattice.Isometry.refl C.space C.lattice

@[simp]
private theorem equalComponentIsometry_coe
    (C E : Lattice.QuadraticSublattice q) (h : C = E) (z : C.carrier) :
    ((equalComponentIsometry C E h).toLinearEquiv z : V) =
      (z : V) := by
  subst E
  rfl

/-- The explicit strict resolution of a coordinate in the selected member
of the unique large-side collision pair. -/
noncomputable def largeCollisionSelectedCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition) :
    BONG.StrictCoordinateResolution a.toBONG D.largeAlmostJordan
      (D.largeWeakProfileWitness a) I := by
  classical
  let x := D.largeWeakProfileWitness a
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      D.largeAlmostJordan k heq
        (D.largeOnlyScaleCollisionAt c hscale k hk)
  let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
    Classical.choice (a.toBONG.beliLemma47_profile a.good
      (S.toJordan hstrict))
  have hright : (x.indexEquiv I).1 = k.succ :=
    hposition.trans hk.2.symm
  have hcoordinates := x.strict_coordinates_of_right
    D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
  refine
    { componentCount := D.complementComponentCount
      strictWeak := S
      scaleOrder_strict := hstrict
      hasImproperEvenRank :=
        D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
          D.largeAlmostJordan k heq
      profile := P
      localCoordinateOffset :=
        finrank K (D.largeAlmostJordan.component k.castSucc).carrier
      localCoordinate_eq := hcoordinates.2
      component_val_eq_of_offset_zero := by
        intro hoffset
        have hpos := D.largeAlmostJordan.component_finrank_pos k.castSucc
        omega
      prefixComponent_eq := by
        intro j hj
        refine ⟨j.castSucc, rfl, ?_⟩
        apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
        rw [hcoordinates.1] at hj
        exact hj
      scaleOrder_eq := ?_
      effectiveNormOrder_eq := ?_ }
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      hcoordinates.1,
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
    have hskip : k.succ.succAbove k = k.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
    rw [hskip, hright]
    exact heq
  · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
      hcoordinates.1]
    exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
      k heq k (x.indexEquiv I).1 _

theorem largeCollisionSelectedCoordinateResolution_component_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition) :
    (D.largeCollisionSelectedCoordinateResolution c hscale a I
      hposition).component =
        Classical.choose (D.largeCollision_adjacent c hscale) := by
  classical
  let x := D.largeWeakProfileWitness a
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      D.largeAlmostJordan k heq
        (D.largeOnlyScaleCollisionAt c hscale k hk)
  let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
    Classical.choice (a.toBONG.beliLemma47_profile a.good
      (S.toJordan hstrict))
  have hright : (x.indexEquiv I).1 = k.succ :=
    hposition.trans hk.2.symm
  have hcoordinates := x.strict_coordinates_of_right
    D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
  change (P.indexEquiv I).1 = k
  exact hcoordinates.1

theorem largeCollisionSelectedCoordinateResolution_strictWeak_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition) :
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    let hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
    let heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
        rw [hk.1, hk.2]
        simpa only [D.largeAlmostJordan_scaleGenerator_selected,
          D.largeAlmostJordan_scaleGenerator_common] using hscale
    (D.largeCollisionSelectedCoordinateResolution c hscale a I
      hposition).strictWeak = D.largeAlmostJordan.mergeAdjacentAt k heq := by
  classical
  rfl

set_option maxHeartbeats 0 in
theorem largeCollision_selected_effective_eq_norm
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0) :
    let ITarget : Fin (n + 2) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let R := D.largeCollisionSelectedCoordinateResolution
      c hscale a ITarget hposition
    BONG.jordanEffectiveNormOrder R.jordan R.component =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
  classical
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  let R := D.largeCollisionSelectedCoordinateResolution
    c hscale a ITarget hposition
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using hposition
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget] using hlocal
  have htargetCoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have htargetCoordinates' :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using htargetCoordinates
  have htargetSmallZero : (y.indexEquiv ITarget).2.val = 0 := by
    omega
  have hadjacentLarge :=
    x.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetZero
  have hadjacentSmall :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetSmallZero
  have hsourceCoordinates := D.weakProfile_coordinates_eq
    hselected a b ISource
  have hsourceCoordinates' :
      (x.indexEquiv ISource).1 = (y.indexEquiv ISource).1 ∧
        (x.indexEquiv ISource).2.val =
          (y.indexEquiv ISource).2.val := by
    simpa only [x, y] using hsourceCoordinates
  let pPrev := (x.indexEquiv ISource).1
  let pSmallPrev := (y.indexEquiv ISource).1
  have hpPrevSmall : pPrev = pSmallPrev := by
    simpa only [pPrev, pSmallPrev] using hsourceCoordinates'.1
  have hpPrev : pPrev = k.castSucc := by
    apply Fin.ext
    have hsucc := hadjacentLarge.1
    have htargetK : (x.indexEquiv ITarget).1 = k.succ :=
      htargetPosition.trans hk.2.symm
    have htargetKVal := congrArg Fin.val htargetK
    change pPrev.val + 1 = (x.indexEquiv ITarget).1.val at hsucc
    change (x.indexEquiv ITarget).1.val = k.val + 1 at htargetKVal
    change pPrev.val = k.val
    omega
  have hpSmall : pSmallPrev = D.smallCommonPosition c := by
    calc
      pSmallPrev = pPrev := hpPrevSmall.symm
      _ = k.castSucc := hpPrev
      _ = D.largeCommonPosition c := hk.1
      _ = D.smallCommonPosition c :=
        (D.commonPositions_eq_of_selectedPositions_eq hselected c).symm
  let scale := ordUnit K D.input.block.enlargedScaleGenerator
  let largeEffectivePrev :=
    D.largeAlmostJordan.effectiveNormOrderAt pPrev scale
  let smallEffectivePrev :=
    D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev scale
  let largeEffectiveSelected :=
    D.largeAlmostJordan.effectiveNormOrderAt
      D.largeSelectedPosition scale
  let selectedNorm := ordUnit K
    (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
  have hlargePrevScale : ordUnit K
      (D.largeAlmostJordan.scaleGenerator pPrev) = scale := by
    rw [hpPrev, hk.1, D.largeAlmostJordan_scaleGenerator_common]
    simpa only [scale] using hscale
  have hsmallPrevScale : ordUnit K
      (D.smallAlmostJordan.scaleGenerator pSmallPrev) = scale := by
    rw [hpSmall, D.smallAlmostJordan_scaleGenerator_common]
    simpa only [scale] using hscale
  have hlargePreviousOrder : a.order ISource =
      2 * scale - largeEffectivePrev := by
    rw [D.largeWeak_order_eq_localOrder a ISource]
    change JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev))
      (D.largeAlmostJordan.effectiveNormOrderAt pPrev
        (ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)))
      (x.indexEquiv ISource).2.val = _
    rw [hlargePrevScale]
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pPrev
    have hlocalLast : (x.indexEquiv ISource).2.val =
        finrank K (D.largeAlmostJordan.component pPrev).carrier - 1 := by
      have hterminal := hadjacentLarge.2
      change (x.indexEquiv ISource).2.val + 1 =
        finrank K (D.largeAlmostJordan.component pPrev).carrier at hterminal
      omega
    rw [hlargePrevScale] at hlast
    simpa only [hlocalLast, largeEffectivePrev] using hlast
  have hsmallPreviousOrder : b.order ISource =
      2 * scale - smallEffectivePrev := by
    rw [D.smallWeak_order_eq_localOrder b ISource]
    change JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev))
      (D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev
        (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev)))
      (y.indexEquiv ISource).2.val = _
    rw [hsmallPrevScale]
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pSmallPrev
    have hlocalLast : (y.indexEquiv ISource).2.val =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier - 1 := by
      have hterminal := hadjacentSmall.2
      change (y.indexEquiv ISource).2.val + 1 =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier at hterminal
      omega
    rw [hsmallPrevScale] at hlast
    simpa only [hlocalLast, smallEffectivePrev] using hlast
  have hcomponent : R.component = k := by
    exact D.largeCollisionSelectedCoordinateResolution_component_eq
      c hscale a ITarget htargetPosition
  have hoffset : R.localCoordinateOffset =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier := by
    rfl
  have hlocalResolved : (R.profile.indexEquiv ITarget).2.val =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier := by
    rw [R.localCoordinate_eq, hoffset, htargetZero, add_zero]
  have hrank : R.jordan.componentRank R.component =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 2 := by
    change finrank K (R.strictWeak.component R.component).carrier = _
    rw [D.largeCollisionSelectedCoordinateResolution_strictWeak_eq
      c hscale a ITarget htargetPosition, hcomponent]
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    rw [D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq,
      hk.2, D.largeAlmostJordan_finrank_selected, hfin]
  have hindexResolved := R.index_val_eq_coordinates_start_add_local
  rw [hlocalResolved] at hindexResolved
  have hpenultimate : ITarget.val + 2 = R.coordinates.stop := by
    have hstop : R.coordinates.stop = R.coordinates.start +
        R.jordan.componentRank R.component := rfl
    rw [hstop, hrank]
    omega
  have hcommonRankPositive : 0 <
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier :=
    D.largeAlmostJordan.component_finrank_pos k.castSucc
  have hsourceStart : R.coordinates.start ≤ ISource.val := by
    dsimp only [ISource, ITarget, Fin.val_mk] at hindexResolved ⊢
    omega
  have hsourceInside : ISource.val + 2 < R.coordinates.stop := by
    dsimp only [ISource, ITarget, Fin.val_mk] at hpenultimate ⊢
    have := i.one_lt
    omega
  have hperiod := R.coordinates.order_add_two_eq ISource.val
    hsourceStart hsourceInside
  have hiOne := i.one_lt
  have houter : a.order ISource = a.order INext := by
    convert hperiod using 1 <;> apply congrArg a.order <;>
      apply Fin.ext <;>
        simp only [BONG.GoodBONG.JordanBlockCoordinates.index_val] <;>
          dsimp only [ISource, INext, Fin.val_mk] <;> omega
  have heffectiveStrict : largeEffectivePrev < smallEffectivePrev := by
    have htriggerOrder : b.order ISource < a.order INext := by
      simpa only [ISource, INext] using htrigger.1
    rw [← houter, hsmallPreviousOrder, hlargePreviousOrder] at htriggerOrder
    omega
  have hselectedEffective : largeEffectiveSelected = selectedNorm := by
    exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
      pPrev pSmallPrev D.largeSelectedPosition scale scale le_rfl
        le_rfl heffectiveStrict
  have hresolvedEffective :
      BONG.jordanEffectiveNormOrderAt R.jordan R.component
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv ITarget).1)) =
        D.largeAlmostJordan.effectiveNormOrderAt
          (x.indexEquiv ITarget).1
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv ITarget).1)) := by
    exact R.effectiveNormOrder_eq
  have hresolvedScale :
      ordUnit K (R.jordan.scaleGenerator R.component) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator
          (x.indexEquiv ITarget).1) := by
    simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder] using
      (show R.jordan.fundamentalScaleOrder R.component =
          ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv ITarget).1) by
        simpa only [BONG.StrictCoordinateResolution.component, x] using
          R.scaleOrder_eq)
  change BONG.jordanEffectiveNormOrder R.jordan R.component = _
  unfold BONG.jordanEffectiveNormOrder
  rw [hresolvedScale]
  exact hresolvedEffective.trans (by
    simpa only [x, ITarget, htargetPosition, scale,
      D.largeAlmostJordan_scaleGenerator_selected,
      largeEffectiveSelected, selectedNorm] using hselectedEffective)

set_option maxHeartbeats 0 in
/-- In the collision amalgamation, a norm-generator vector supported in the
old selected binary summand remains a norm generator of the merged strict
component and attains its intrinsic effective norm. -/
theorem largeCollision_selectedGenerator
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0) :
    let ITarget : Fin (n + 2) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let R := D.largeCollisionSelectedCoordinateResolution
      c hscale a ITarget hposition
    ∃ v : (R.jordan.component R.component).carrier,
      Lattice.IsNormGenerator (R.jordan.component R.component).space
          (R.jordan.component R.component).lattice v ∧
        BONG.jordanEffectiveNormOrder R.jordan R.component =
          ordUnit K (R.jordan.normGenerator R.component) ∧
        (v : V) =
          (D.largeAlmostJordan.normGeneratorVector
            D.largeSelectedPosition : V) := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using hposition
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  let R := D.largeCollisionSelectedCoordinateResolution
    c hscale a ITarget hposition
  have hcomponent : R.component = k :=
    D.largeCollisionSelectedCoordinateResolution_component_eq
      c hscale a ITarget htargetPosition
  have hstrictWeak : R.strictWeak = S := by
    exact D.largeCollisionSelectedCoordinateResolution_strictWeak_eq
      c hscale a ITarget htargetPosition
  have heffectiveR : BONG.jordanEffectiveNormOrder R.jordan R.component =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) :=
    D.largeCollision_selected_effective_eq_norm hselected c hscale
      a b i htrigger hfin hposition hlocal
  have heffectiveOld :
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            D.largeSelectedPosition)) =
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) := by
    have h := heffectiveR
    unfold BONG.jordanEffectiveNormOrder at h
    have hresolvedScale :
        ordUnit K (R.jordan.scaleGenerator R.component) =
          ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv ITarget).1) := by
      simpa only [Lattice.JordanDecomposition.fundamentalScaleOrder,
        BONG.StrictCoordinateResolution.component, x] using R.scaleOrder_eq
    rw [hresolvedScale] at h
    have hresolvedEffective :
        BONG.jordanEffectiveNormOrderAt R.jordan R.component
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv ITarget).1)) =
          D.largeAlmostJordan.effectiveNormOrderAt
            (x.indexEquiv ITarget).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv ITarget).1)) := by
      exact R.effectiveNormOrder_eq
    have hold := hresolvedEffective.symm.trans h
    simpa only [x, ITarget, htargetPosition] using hold
  have hselectedLeCommonNorm :
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) ≤
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit k.castSucc) := by
    calc
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) =
          D.largeAlmostJordan.effectiveNormOrderAt
            D.largeSelectedPosition
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              D.largeSelectedPosition)) := heffectiveOld.symm
      _ = D.largeAlmostJordan.effectiveNormOrderAt k.castSucc
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              D.largeSelectedPosition)) :=
        D.largeAlmostJordan.effectiveNormOrderAt_anchor_irrel
          D.largeSelectedPosition k.castSucc _
      _ = D.largeAlmostJordan.effectiveNormOrderAt k.castSucc
            (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc)) := by
        have hselectedScale : ordUnit K
              (D.largeAlmostJordan.scaleGenerator D.largeSelectedPosition) =
            ordUnit K
              (D.largeAlmostJordan.scaleGenerator k.castSucc) := by
          calc
            ordUnit K (D.largeAlmostJordan.scaleGenerator
                D.largeSelectedPosition) =
                ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) :=
              congrArg (fun p ↦ ordUnit K
                (D.largeAlmostJordan.scaleGenerator p)) hk.2.symm
            _ = _ := heq.symm
        exact congrArg
          (D.largeAlmostJordan.effectiveNormOrderAt k.castSucc)
            hselectedScale
      _ ≤ ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit k.castSucc) :=
        D.largeAlmostJordan.effectiveNormOrderAt_scale_le_normOrder
          k.castSucc
  have hcommonNormLeSelectedNorm :
      Lattice.normIdeal
          (D.largeAlmostJordan.component k.castSucc).space
          (D.largeAlmostJordan.component k.castSucc).lattice ≤
        Lattice.normIdeal
          (D.largeAlmostJordan.component k.succ).space
          (D.largeAlmostJordan.component k.succ).lattice := by
    rw [D.largeAlmostJordan.normIdeal_eq_normGeneratorUnit,
      D.largeAlmostJordan.normIdeal_eq_normGeneratorUnit]
    apply (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero (D.largeAlmostJordan.normGeneratorUnit k.castSucc))
      (Units.ne_zero (D.largeAlmostJordan.normGeneratorUnit k.succ))).2
    rw [← coe_ordUnit K
        (D.largeAlmostJordan.normGeneratorUnit k.succ),
      ← coe_ordUnit K
        (D.largeAlmostJordan.normGeneratorUnit k.castSucc)]
    exact_mod_cast (show ordUnit K
        (D.largeAlmostJordan.normGeneratorUnit k.succ) ≤
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit k.castSucc) from by
      calc
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit k.succ) =
          ordUnit K (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) :=
        congrArg (fun p ↦ ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit p)) hk.2
      _ ≤ _ := hselectedLeCommonNorm)
  let oldVector := D.largeAlmostJordan.normGeneratorVector k.succ
  have holdGenerator : Lattice.IsNormGenerator
      (D.largeAlmostJordan.component k.succ).space
      (D.largeAlmostJordan.component k.succ).lattice oldVector :=
    (D.largeAlmostJordan.normGeneratorVector_spec k.succ).1
  let productVector :
      (D.largeAlmostJordan.component k.castSucc).carrier ×
        (D.largeAlmostJordan.component k.succ).carrier := (0, oldVector)
  have hproductGenerator : Lattice.IsNormGenerator
      ((D.largeAlmostJordan.component k.castSucc).space.orthogonalSum
        (D.largeAlmostJordan.component k.succ).space)
      (Lattice.product
        (D.largeAlmostJordan.component k.castSucc).lattice
        (D.largeAlmostJordan.component k.succ).lattice) productVector := by
    simpa only [productVector] using
      holdGenerator.orthogonalProduct_right hcommonNormLeSelectedNorm
  let mergeIsometry :=
    D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      k.castSucc_lt_succ.ne
  let rawVector := mergeIsometry.toLinearEquiv productVector
  have hrawGenerator : Lattice.IsNormGenerator
      (D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne).space
      (D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne).lattice rawVector := by
    exact hproductGenerator.mapLatticeIsometry mergeIsometry
  have hcomponentEq : R.jordan.component R.component =
      D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne := by
    change R.strictWeak.component R.component = _
    rw [hstrictWeak, hcomponent]
    exact D.largeAlmostJordan.mergeAdjacentAt_component_self k heq
  let identify := equalComponentIsometry
    (D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSup
      k.castSucc_lt_succ.ne)
    (R.jordan.component R.component) hcomponentEq.symm
  let v := identify.toLinearEquiv rawVector
  have hvGenerator : Lattice.IsNormGenerator
      (R.jordan.component R.component).space
      (R.jordan.component R.component).lattice v :=
    hrawGenerator.mapLatticeIsometry identify
  have hrawCoe : (rawVector : V) = (oldVector : V) := by
    change
      (D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSupEquiv
        k.castSucc_lt_succ.ne productVector : V) = (oldVector : V)
    rw [D.largeAlmostJordan.toOrthogonalDecomposition.coe_orthogonalSupEquiv]
    simp [productVector]
  have hvCoe : (v : V) =
      (D.largeAlmostJordan.normGeneratorVector
        D.largeSelectedPosition : V) := by
    calc
      (v : V) = (rawVector : V) := by
        exact equalComponentIsometry_coe
          (C := D.largeAlmostJordan.toOrthogonalDecomposition.orthogonalSup
            k.castSucc_lt_succ.ne)
          (E := R.jordan.component R.component) hcomponentEq.symm rawVector
      _ = (oldVector : V) := hrawCoe
      _ = (D.largeAlmostJordan.normGeneratorVector
          D.largeSelectedPosition : V) :=
        congrArg (fun p ↦
          (D.largeAlmostJordan.normGeneratorVector p : V)) hk.2
  have hmergedNorm : ordUnit K (R.jordan.normGenerator R.component) =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
    have hmergedNormS : ordUnit K (S.normGeneratorUnit k) =
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) := by
      dsimp only [S]
      rw [D.largeAlmostJordan.ordUnit_normGeneratorUnit_mergeAdjacentAt_self]
      have hselectedOrderK : ordUnit K
            (D.largeAlmostJordan.normGeneratorUnit k.succ) =
          ordUnit K (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) :=
        congrArg (fun p ↦ ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit p)) hk.2
      have hselectedLeCommonK : ordUnit K
            (D.largeAlmostJordan.normGeneratorUnit k.succ) ≤
          ordUnit K (D.largeAlmostJordan.normGeneratorUnit k.castSucc) :=
        hselectedOrderK.trans_le hselectedLeCommonNorm
      rw [min_eq_right hselectedLeCommonK, hselectedOrderK]
    change ordUnit K (R.strictWeak.normGeneratorUnit R.component) = _
    calc
      ordUnit K (R.strictWeak.normGeneratorUnit R.component) =
          ordUnit K (R.strictWeak.normGeneratorUnit k) :=
        congrArg (fun p ↦ ordUnit K
          (R.strictWeak.normGeneratorUnit p)) hcomponent
      _ = ordUnit K (S.normGeneratorUnit k) :=
        congrArg (fun W : Lattice.WeakJordanDecomposition q M
          D.complementComponentCount ↦ ordUnit K (W.normGeneratorUnit k))
            hstrictWeak
      _ = _ := hmergedNormS
  exact ⟨v, hvGenerator, heffectiveR.trans hmergedNorm.symm, hvCoe⟩

set_option maxHeartbeats 0 in
/-- Terminal form of resolved Lemma 3.7(iii).  When the penultimate
coordinate lies in the final strict Jordan component, the canonical model is
the orthogonal complement of the prescribed represented fundamental
generator in the whole ambient space. -/
theorem exists_spaceModel_iii_of_penultimate_terminal_with_generator
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 1 < R.jordan.componentRank R.component)
    (hcomponentLast : R.component.val + 1 = R.componentCount)
    (G : BONG.RepresentedFundamentalNormGenerator R.jordan R.component)
    (v : (R.jordan.component R.component).carrier)
    (hv : (R.jordan.component R.component).space.quadratic v =
      (G.value : K))
    (houter : a.order
        ⟨g.val - 1, by have := g.isLt; omega⟩ =
      a.order ⟨g.val + 1, by have := g.isLt; omega⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      ∀ y : V,
        y ∈ R.jordan.toOrthogonalDecomposition.prefixCarrier
            (R.component.val + 1) →
          q.bilin y (v : V) = 0 →
          y ∈ model.carrier := by
  classical
  letI : Module.Finite K V := L.moduleFinite
  let p := R.component
  let strictProfile := BONG.WeakJordanOrderProfileWitness.ofStrict
    R.strictWeak R.scaleOrder_strict R.profile
  have hUniv : (Finset.univ : Finset (Fin R.componentCount)) =
      insert p (Finset.Iio p) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio,
      true_iff]
    by_cases heq : j = p
    · exact Or.inl heq
    · exact Or.inr (by
        have hj := j.isLt
        have hpLast := hcomponentLast
        have hneVal : j.val ≠ p.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega)
  have hsum := strictProfile.sum_componentRank_eq_length
  change (∑ j, finrank K (R.strictWeak.component j).carrier) = n + 2
    at hsum
  rw [hUniv, Finset.sum_insert (by simp)] at hsum
  have hstopFull : R.coordinates.stop = n + 2 := by
    have hstop : R.coordinates.stop = R.coordinates.start +
        R.jordan.componentRank R.component := rfl
    rw [hstop]
    change (∑ j ∈ Finset.Iio p,
        finrank K (R.strictWeak.component j).carrier) +
      finrank K (R.strictWeak.component p).carrier = n + 2
    omega
  have hterminal : I.val + 2 = n + 2 := hpenultimate.trans hstopFull
  have hIval : I.val = g.val := congrArg Fin.val hI
  have hgLast : g.val + 2 = n + 2 := by omega
  let xv : V := v
  have hvAmbient : q.quadratic xv = (G.value : K) := by
    change q.quadratic (v : V) = (G.value : K)
    exact hv
  have hx : q.IsAnisotropic xv := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hvAmbient]
    exact Units.ne_zero G.value
  let Qc := q.orthogonalSpace xv hx
  have hambientRank : n + 2 = finrank K V :=
    a.toBONG.length_eq_finrank
  have horthRank := q.finrank_vectorOrthogonal hx
  have hcomplementRank : g.val + 1 = finrank K (q.vectorOrthogonal xv) := by
    omega
  let e : Fin (g.val + 1) ≃ Fin (finrank K (q.vectorOrthogonal xv)) :=
    finCongr hcomplementRank
  let units : Fin (g.val + 1) → Kˣ := Qc.diagonalUnits ∘ e
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients Qc.diagonalUnits)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero Qc.diagonalUnits) e
  let complementIso : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)) Qc := by
    have hraw := reindex.symm.trans Qc.diagonalizationIsometry.symm
    change QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (Qc.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (Qc.diagonalUnits (e i)))) Qc
    simpa only [reindex, units, Qc, QuadraticSpace.diagonalModel,
      diagonalUnitCoefficients, Function.comp_apply] using hraw
  let splitIso : QuadraticSpace.Isometry
      ((QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients units)
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero units))
        |>.orthogonalSum (QuadraticSpace.scaledLine G.value)) q :=
    (complementIso.orthogonalSum
        (QuadraticSpace.Isometry.refl (QuadraticSpace.scaledLine G.value)))
      |>.trans (QuadraticSpace.orthogonalSumSwap Qc
        (QuadraticSpace.scaledLine G.value))
      |>.trans (QuadraticSpace.scaledLineOrthogonalIsometry
        q xv G.value hx hvAmbient)
  let dP : Kˣ :=
    (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
      (p.val + 1)).refinedDeterminantUnit
  have hbaseRaw :=
    BONG.WeakJordanOrderProfileWitness.corollary33_prescribedPrefixApproximation
      a R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile
        p G.value G.fundamental (by
          change 2 ≤ R.jordan.componentRank R.component
          omega)
  have hbase : a.IsPrefixApproximation (g.val + 1) (G.value * dP) := by
    change a.IsPrefixApproximation (R.coordinates.stop - 1)
      (G.value * dP) at hbaseRaw
    rw [hstopFull] at hbaseRaw
    have hindex : n + 2 - 1 = g.val + 1 := by omega
    simpa only [dP, hindex] using hbaseRaw
  let fullIndexEquiv : Fin (g.val + 2) ≃ Fin (n + 2) := finCongr hgLast
  let targetUnits : Fin (g.val + 2) → Kˣ :=
    a.valueUnit ∘ fullIndexEquiv
  let targetReindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients a.valueUnit)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero a.valueUnit)
    fullIndexEquiv
  have hdiagRep : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc units G.value))
      (diagonalUnitCoefficients targetUnits) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.snoc units G.value) targetUnits).1
    let splitDiagonal :=
      QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
        units G.value
    let fullIso := splitDiagonal.symm.trans splitIso |>.trans
      a.toBONG.exactDiagonalizationIsometry |>.trans targetReindex
    exact ⟨fullIso.toRepresentation⟩
  obtain ⟨r, hr⟩ :=
    DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hdiagRep
  have hsnocDetRaw : diagonalUnitDeterminant (Fin.snoc units G.value) =
      diagonalUnitDeterminant targetUnits * r ^ 2 := by
    apply Units.ext
    change Units.coeHom K
        (∏ j, ((Fin.snoc units G.value :
          Fin (g.val + 2) → Kˣ) j)) =
      Units.coeHom K (∏ j, targetUnits j) * (r : K) ^ 2
    rw [map_prod (Units.coeHom K)
        (Fin.snoc units G.value : Fin (g.val + 2) → Kˣ) Finset.univ,
      map_prod (Units.coeHom K) targetUnits Finset.univ]
    exact hr
  have htargetDet : diagonalUnitDeterminant targetUnits =
      diagonalUnitDeterminant a.valueUnit := by
    exact fullIndexEquiv.prod_comp a.valueUnit
  have hsnocDet : diagonalUnitDeterminant (Fin.snoc units G.value) =
      diagonalUnitDeterminant a.valueUnit * r ^ 2 := by
    rw [hsnocDetRaw, htargetDet]
  have hvalueDet : diagonalUnitDeterminant a.valueUnit =
      a.toBONG.valueProduct := by
    apply Units.ext
    change Units.coeHom K (∏ j, a.valueUnit j) =
      (a.toBONG.valueProduct : K)
    rw [map_prod (Units.coeHom K) a.valueUnit Finset.univ,
      BONG.coe_valueProduct]
    rfl
  have hfullClassRaw :=
    Lattice.determinantClass_eq_of_isometry
      R.jordan.toOrthogonalDecomposition.fullPrefixLatticeIsometry
  have hfullClass : unitSquareClass K dP =
      Lattice.determinantClass q L := by
    change Lattice.determinantClass
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (p.val + 1)).space
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (p.val + 1)).lattice =
      Lattice.determinantClass q L
    rw [show p.val + 1 = R.componentCount by
      simpa only [p] using hcomponentLast]
    exact hfullClassRaw
  have hvalueClass := a.toBONG.determinantClass_eq_valueProduct
  have hclass : unitSquareClass K a.toBONG.valueProduct =
      unitSquareClass K dP := by
    calc
      unitSquareClass K a.toBONG.valueProduct =
          Lattice.determinantClass q L := hvalueClass.symm
      _ = unitSquareClass K dP := hfullClass.symm
  obtain ⟨s, hs⟩ :=
    BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
      a.toBONG.valueProduct dP hclass
  have hdetSquare : ∃ u : Kˣ,
      diagonalUnitDeterminant units = (G.value * dP) * u ^ 2 := by
    refine ⟨G.value⁻¹ * r * s⁻¹, ?_⟩
    rw [← hs]
    calc
      diagonalUnitDeterminant units =
          diagonalUnitDeterminant (Fin.snoc units G.value) *
            G.value⁻¹ := by
        rw [diagonalUnitDeterminant_snoc]
        group
      _ = (diagonalUnitDeterminant a.valueUnit * r ^ 2) *
            G.value⁻¹ := by rw [hsnocDet]
      _ = (G.value * (a.toBONG.valueProduct * s ^ 2)) *
          (G.value⁻¹ * r * s⁻¹) ^ 2 := by
        rw [hvalueDet]
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val,
          Units.val_inv_eq_inv_val]
        field_simp
  have hdet : a.IsPrefixApproximation (g.val + 1)
      (diagonalUnitDeterminant units) := by
    rcases hdetSquare with ⟨u, hu⟩
    rw [hu]
    exact (a.isPrefixApproximation_mul_square_iff
      (g.val + 1) (G.value * dP) u).2 hbase
  have hspace : q.Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)) := by
    exact ⟨splitIso.toRepresentation.trans
      (QuadraticSpace.Representation.orthogonalSumInl _
        (QuadraticSpace.scaledLine G.value))⟩
  have hdiagonalSpace : a.toBONG.exactDiagonalSpace.Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)) := by
    exact ⟨a.toBONG.exactDiagonalizationIsometry.toRepresentation.trans
      (Classical.choice hspace)⟩
  have hdiagFull : DiagonalRepresents
      (diagonalUnitCoefficients units)
      (diagonalUnitCoefficients a.valueUnit) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      units a.valueUnit).1
    unfold BONG.exactDiagonalSpace at hdiagonalSpace
    convert hdiagonalSpace using 1 <;> rfl
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients units)
      (a.prefixValues (n + 2) (by omega)) := by
    have htarget : a.prefixValues (n + 2) (by omega) =
        diagonalUnitCoefficients a.valueUnit := by
      funext j
      rfl
    rw [htarget]
    exact hdiagFull
  have hright : DiagonalRepresents
      (diagonalUnitCoefficients units)
      (a.prefixValues (g.val + 2) (by omega)) := by
    exact BONG.GoodBONG.targetPrefixRepresents_cast
      (diagonalUnitCoefficients units) a hgLast.symm hfull
  have hnotLeft :=
    a.not_leftApproximationTrigger_of_twoStepOrder_eq g
      (by omega) houter
  have happroximation : a.IsSpaceApproximation g units :=
    ⟨⟨hdet, fun htrigger ↦ (hnotLeft htrigger).elim⟩,
      ⟨hdet, fun _ ↦ hright⟩⟩
  let model : BONG.GoodBONG.SpaceApproximationModel a g :=
    { carrier := q.vectorOrthogonal xv
      nondegenerate := Qc.nondegenerate
      units := units
      approximation := happroximation
      presentation := complementIso }
  refine ⟨model, ?_⟩
  intro y _hyPrefix hyOrthogonal
  change y ∈ q.vectorOrthogonal xv
  rw [q.mem_vectorOrthogonal_iff]
  change q.bilin xv y = 0
  rw [q.isSymm.eq]
  exact hyOrthogonal

set_option maxHeartbeats 0 in
/-- The selected-binary central branch in the unique large-side collision,
including both a nonterminal merged strict component and the final-component
endpoint. -/
theorem weakAligned_centralCertificate_of_targetSelected_rank_two_of_collision
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let ISource : Fin (n + 2) := gSource.castSucc
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  let Rtarget := D.largeCollisionSelectedCoordinateResolution
    c hscale a ITarget hposition
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hlocal
  have htargetCoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have htargetCoordinates' :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using htargetCoordinates
  have hsmallTargetZero : (y.indexEquiv ITarget).2.val = 0 := by
    omega
  have hsourceBoundary :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsmallTargetZero
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have hcomponentEq := congrArg Fin.val htargetCoordinates'.1
    have hpositionVal := congrArg Fin.val htargetPosition
    have hselectedVal := congrArg Fin.val hselected
    change (y.indexEquiv ISource).1.val < D.smallSelectedPosition.val
    omega
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [y, ISource] using hsourceBoundary.2)
  have hweakNext : Rsource.weakNext.val =
      (x.indexEquiv ITarget).1.val := by
    rw [Rsource.weakNext_val]
    have hsourceSucc : (y.indexEquiv ISource).1.val + 1 =
        (x.indexEquiv ITarget).1.val := by
      calc
        (y.indexEquiv ISource).1.val + 1 =
            (y.indexEquiv ITarget).1.val := hsourceBoundary.1
        _ = (x.indexEquiv ITarget).1.val :=
          congrArg Fin.val htargetCoordinates'.1 |>.symm
    simpa only [y, ISource, gSource] using hsourceSucc
  have hcomponent : Rtarget.component = k :=
    D.largeCollisionSelectedCoordinateResolution_component_eq
      c hscale a ITarget htargetPosition
  have hstrictWeak : Rtarget.strictWeak = S :=
    D.largeCollisionSelectedCoordinateResolution_strictWeak_eq
      c hscale a ITarget htargetPosition
  have hoffset : Rtarget.localCoordinateOffset =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier := by
    rfl
  have hlocalResolved : (Rtarget.profile.indexEquiv ITarget).2.val =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier := by
    rw [Rtarget.localCoordinate_eq, hoffset, htargetZero, add_zero]
  have hrank : Rtarget.jordan.componentRank Rtarget.component =
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 2 := by
    change finrank K
      (Rtarget.strictWeak.component Rtarget.component).carrier = _
    rw [hstrictWeak, hcomponent]
    dsimp only [S]
    rw [D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq,
      hk.2, D.largeAlmostJordan_finrank_selected, hfin]
  have hindexResolved := Rtarget.index_val_eq_coordinates_start_add_local
  rw [hlocalResolved] at hindexResolved
  have hpenultimate : ITarget.val + 2 = Rtarget.coordinates.stop := by
    have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
        Rtarget.jordan.componentRank Rtarget.component := rfl
    rw [hstop, hrank]
    omega
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    omega
  have hsourceStart : Rtarget.coordinates.start ≤ ISource.val := by
    have hcommonPositive :=
      D.largeAlmostJordan.component_finrank_pos k.castSucc
    dsimp only [ISource, ITarget, gSource, gTarget,
      Fin.castSucc_mk, Fin.val_mk] at hindexResolved ⊢
    omega
  have hsourceInside : ISource.val + 2 < Rtarget.coordinates.stop := by
    dsimp only [ISource, ITarget, gSource, gTarget,
      Fin.castSucc_mk, Fin.val_mk] at hpenultimate ⊢
    have := i.one_lt
    omega
  have hperiod := Rtarget.coordinates.order_add_two_eq ISource.val
    hsourceStart hsourceInside
  have houterRaw : a.order ISource = a.order INext := by
    have hiOne := i.one_lt
    convert hperiod using 1 <;> apply congrArg a.order <;>
      apply Fin.ext <;>
        simp only [BONG.GoodBONG.JordanBlockCoordinates.index_val] <;>
          dsimp only [ISource, INext, gSource, Fin.castSucc_mk,
            Fin.val_mk] <;> omega
  have houter : a.order
        ⟨gTarget.val - 1, by have := gTarget.isLt; omega⟩ =
      a.order ⟨gTarget.val + 1, by have := gTarget.isLt; omega⟩ := by
    have hleft :
        (⟨gTarget.val - 1, by have := gTarget.isLt; omega⟩ :
          Fin (n + 2)) = ISource := by
      apply Fin.ext
      dsimp only [gTarget, ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega
    have hright :
        (⟨gTarget.val + 1, by have := gTarget.isLt; omega⟩ :
          Fin (n + 2)) = INext := by
      apply Fin.ext
      dsimp only [gTarget, INext, Fin.val_mk]
      have := i.one_lt
      omega
    rw [hleft, hright]
    exact houterRaw
  obtain ⟨v, hvGenerator, heffective, hvCoe⟩ :=
    D.largeCollision_selectedGenerator hselected c hscale
      a b i htrigger hfin hposition hlocal
  let G := BONG.RepresentedFundamentalNormGenerator.ofComponentNormGenerator
    Rtarget.strictWeak Rtarget.scaleOrder_strict Rtarget.component
      v hvGenerator heffective
  have hv : (Rtarget.jordan.component Rtarget.component).space.quadratic v =
      (G.value : K) := by
    rfl
  obtain ⟨target, htargetMem⟩ :
      ∃ target : BONG.GoodBONG.SpaceApproximationModel a gTarget,
        ∀ z : V,
          z ∈ Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
              (Rtarget.component.val + 1) →
            q.bilin z (v : V) = 0 →
            z ∈ target.carrier := by
    by_cases hcomponentNext :
        Rtarget.component.val + 1 < Rtarget.componentCount
    · exact Rtarget.exists_spaceModel_iii_of_penultimate_with_generator
        gTarget rfl htargetPositive hpenultimate (by rw [hrank]; omega)
          hcomponentNext G v hv houter
    · have hcomponentLast :
          Rtarget.component.val + 1 = Rtarget.componentCount := by
        have := Rtarget.component.isLt
        omega
      exact exists_spaceModel_iii_of_penultimate_terminal_with_generator
        Rtarget gTarget rfl htargetPositive hpenultimate (by rw [hrank]; omega)
          hcomponentLast G v hv houter
  have htargetComplete :
      Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          (Rtarget.component.val + 1) =
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (k.val + 2) := by
    have hmerged :=
      D.largeAlmostJordan.mergeAdjacentAt_prefixCarrier_eq_of_pair_le
        k heq (k.val + 2) (by omega) (by
          have hkBound := k.isLt
          omega)
    change Rtarget.strictWeak.toOrthogonalDecomposition.prefixCarrier
        (Rtarget.component.val + 1) = _
    calc
      Rtarget.strictWeak.toOrthogonalDecomposition.prefixCarrier
          (Rtarget.component.val + 1) =
          Rtarget.strictWeak.toOrthogonalDecomposition.prefixCarrier
            (k.val + 1) := by rw [hcomponent]
      _ = S.toOrthogonalDecomposition.prefixCarrier (k.val + 1) :=
        congrArg (fun W : Lattice.WeakJordanDecomposition q M
          D.complementComponentCount ↦
            W.toOrthogonalDecomposition.prefixCarrier (k.val + 1))
              hstrictWeak
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (k.val + 2) := by
        have hcut : k.val + 2 - 1 = k.val + 1 := by omega
        simpa only [S, hcut] using hmerged
  have htargetWeakVal : (x.indexEquiv ITarget).1.val = k.val + 1 := by
    have htargetK : (x.indexEquiv ITarget).1 = k.succ :=
      htargetPosition.trans hk.2.symm
    exact congrArg Fin.val htargetK
  let oldVector := D.largeAlmostJordan.normGeneratorVector k.succ
  have hselectedVector :
      (D.largeAlmostJordan.normGeneratorVector
          D.largeSelectedPosition : V) = (oldVector : V) :=
    congrArg (fun p ↦
      (D.largeAlmostJordan.normGeneratorVector p : V)) hk.2.symm
  have hsourceToTarget : Rsource.lemma37Model_i.carrier ≤
      target.carrier := by
    intro z hz
    have hzSmall := hz
    rw [Rsource.lemma37Model_i_carrier_eq, hweakNext] at hzSmall
    have hzLarge : z ∈
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val := by
      rw [D.aligned_prefixCarrier_eq hselected]
      exact hzSmall
    have hzBefore : z ∈
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (k.val + 1) := by
      simpa only [htargetWeakVal] using hzLarge
    have hzOldComplete : z ∈
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (k.val + 2) :=
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono
        (by omega) hzBefore
    have hzComplete : z ∈
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          (Rtarget.component.val + 1) := by
      rw [htargetComplete]
      exact hzOldComplete
    apply htargetMem z hzComplete
    let z' :
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.succ.val).carrier :=
      ⟨z, by
        change z ∈ D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          k.succ.val
        simpa only [Fin.val_succ] using hzBefore⟩
    have horth :=
      D.largeAlmostJordan.toOrthogonalDecomposition.prefix_orthogonal_component
        k.succ z' oldVector
    rw [hvCoe, hselectedVector]
    exact horth
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger target Rsource.lemma37Model_i hsourceToTarget)

set_option maxHeartbeats 0 in
/-- Complete selected-binary branch.  A large-side scale collision is resolved
by amalgamating the unique adjacent pair; otherwise the unmerged strict
resolution from `Beli2019SectionFiveCentralSelected` applies. -/
theorem weakAligned_centralCertificate_of_targetSelected_rank_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  by_cases hcollision : D.LargeScaleCollision
  · obtain ⟨c, hscale⟩ := hcollision
    exact D.weakAligned_centralCertificate_of_targetSelected_rank_two_of_collision
      hselected c hscale a b hdefect i htrigger hfin hposition hlocal
  · exact D.weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision
      hcollision hselected a b hdefect i htrigger hfin hposition hlocal

end Lattice.Beli2019Lemma51Data

end Bong
