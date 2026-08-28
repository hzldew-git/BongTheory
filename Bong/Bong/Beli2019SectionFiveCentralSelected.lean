/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralOrdinary

/-!
# Selected-block central representation cases in Beli (2019), Section 5

This file treats central target coordinates lying in the selected block.
The unary case is a boundary on the large side even when the preceding
common component has the same scale and is amalgamated with it.
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

set_option maxHeartbeats 0 in
/-- If the central target is the first coordinate of a selected unary
component, both relevant approximation spaces are complete resolved
boundaries.  Their weak prefix carriers are nested across the aligned
decompositions, including after a collision amalgamation. -/
theorem weakAligned_centralCertificate_of_targetSelected_rank_one
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
    (hfin : finrank K D.input.block.component.carrier = 1)
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
  have hposition' : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have hlocal' : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hlocal
  have htargetLast : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    have hrank : finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier = 1 := by
      calc
        finrank K (D.largeAlmostJordan.component
            (x.indexEquiv ITarget).1).carrier =
            finrank K (D.largeAlmostJordan.component
              D.largeSelectedPosition).carrier := congrArg
                (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier)
                hposition'
        _ = 1 := by rw [D.largeAlmostJordan_finrank_selected, hfin]
    omega
  have htargetNext := x.indexEquiv_global_succ_of_terminal
    ITarget INext (by
      dsimp only [ITarget, INext, gTarget, Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega) htargetLast
  have hselectedNext : D.largeSelectedPosition.val <
      D.complementComponentCount := by
    have hnextBound := (x.indexEquiv INext).1.isLt
    have hnextComponent := htargetNext.1
    have hpositionVal := congrArg Fin.val hposition'
    change (x.indexEquiv INext).1.val <
      D.complementComponentCount + 1 at hnextBound
    omega
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hcoordinatesRaw
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
    have hcomponentEq := congrArg Fin.val hcoordinates.1
    have hpositionVal := congrArg Fin.val hposition'
    have hselectedVal := congrArg Fin.val hselected
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val
    omega
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [y, ISource] using hsourceBoundary.2)
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution_afterSelected
    a gTarget (by
      change D.largeSelectedPosition ≤ (x.indexEquiv ITarget).1
      exact hposition'.ge)
      (by simpa only [x, ITarget] using htargetLast)
      (by
        have hp : ((D.largeWeakProfileWitness a).indexEquiv
            gTarget.castSucc).1 = D.largeSelectedPosition := by
          simpa only [x, ITarget] using hposition'
        rw [hp]
        exact hselectedNext)
  have hsourceNext : Rsource.weakNext.val =
      D.largeSelectedPosition.val := by
    rw [Rsource.weakNext_val]
    have hsourceSucc : (y.indexEquiv ISource).1.val + 1 =
        D.largeSelectedPosition.val := by
      calc
        (y.indexEquiv ISource).1.val + 1 =
            (y.indexEquiv ITarget).1.val := hsourceBoundary.1
        _ = (x.indexEquiv ITarget).1.val :=
          congrArg Fin.val hcoordinates.1 |>.symm
        _ = D.largeSelectedPosition.val := congrArg Fin.val hposition'
    simpa only [y, ISource, gSource] using hsourceSucc
  have htargetNext' : Rtarget.weakNext.val =
      D.largeSelectedPosition.val + 1 := by
    rw [Rtarget.weakNext_val]
    have hp : ((D.largeWeakProfileWitness a).indexEquiv
        gTarget.castSucc).1.val = D.largeSelectedPosition.val := by
      simpa only [x, ITarget] using congrArg Fin.val hposition'
    omega
  have hcarrier : Rsource.lemma37Model_i.carrier ≤
      Rtarget.lemma37Model_i.carrier := by
    rw [Rsource.lemma37Model_i_carrier_eq,
      Rtarget.lemma37Model_i_carrier_eq, hsourceNext, htargetNext',
      ← D.aligned_prefixCarrier_eq hselected D.largeSelectedPosition.val]
    exact D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono
      (by omega)
  exact centralCertificate_of_sourceModel_to_boundary
    a b hdefect i htrigger Rtarget Rsource.lemma37Model_i hcarrier

noncomputable def largeNoCollisionCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬ D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n) :
    BONG.StrictCoordinateResolution a.toBONG D.largeAlmostJordan
      (D.largeWeakProfileWitness a) I := by
  let x := D.largeWeakProfileWitness a
  let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge
  let P := D.largeNoCollisionProfileWitness hlarge a
  have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
  refine
    { componentCount := D.complementComponentCount + 1
      strictWeak := D.largeAlmostJordan
      scaleOrder_strict := hstrict
      hasImproperEvenRank := D.largeAlmostJordan_hasImproperEvenRank
      profile := P
      localCoordinateOffset := 0
      localCoordinate_eq := by
        simpa only [Nat.zero_add] using
          (congrArg (fun z ↦ z.2.val) hcoordinates).symm
      component_val_eq_of_offset_zero := by
        intro _
        exact congrArg Fin.val (congrArg Sigma.fst hcoordinates).symm
      prefixComponent_eq := by
        intro j _hj
        exact ⟨j, rfl, rfl⟩
      scaleOrder_eq := ?_
      effectiveNormOrder_eq := ?_ }
  · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
    rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
    exact congrArg (fun p ↦ ordUnit K
      (D.largeAlmostJordan.scaleGenerator p))
        (congrArg Sigma.fst hcoordinates).symm
  · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan]
    exact D.largeAlmostJordan.effectiveNormOrderAt_anchor_irrel
      (P.indexEquiv I).1 (x.indexEquiv I).1 _

set_option maxHeartbeats 0 in
theorem weakAligned_selected_rank_two_noCollision_leftOuter_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬ D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
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
    a.order (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2)) <
      a.order ⟨i.val, i.lt_large⟩ := by
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
  let pCurrent := (x.indexEquiv ITarget).1
  have hpPrevSmall : pPrev = pSmallPrev := by
    simpa only [pPrev, pSmallPrev] using hsourceCoordinates'.1
  have hpPrevCurrent : pPrev < pCurrent := by
    change (x.indexEquiv ISource).1.val < (x.indexEquiv ITarget).1.val
    omega
  have hpCurrentSelected : pCurrent = D.largeSelectedPosition := by
    simpa only [pCurrent] using htargetPosition
  have hpPrevSelected : pPrev < D.largeSelectedPosition := by
    rw [← hpCurrentSelected]
    exact hpPrevCurrent
  let prevScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
  let currentScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pCurrent)
  let selectedScale := ordUnit K D.input.block.enlargedScaleGenerator
  let largeEffectivePrev :=
    D.largeAlmostJordan.effectiveNormOrderAt pPrev prevScale
  let smallEffectivePrev :=
    D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev prevScale
  let largeEffectiveCurrent :=
    D.largeAlmostJordan.effectiveNormOrderAt pCurrent currentScale
  let selectedNorm := ordUnit K
    (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
  have hscaleAligned : ordUnit K
        (D.smallAlmostJordan.scaleGenerator pSmallPrev) = prevScale := by
    rw [← hpPrevSmall, ← D.aligned_scaleOrder_eq_of_lt
      hselected pPrev hpPrevSelected]
  have hlargePreviousOrder : a.order ISource =
      2 * prevScale - largeEffectivePrev := by
    rw [D.largeWeak_order_eq_localOrder a ISource]
    change JordanProfileOrder.localOrder prevScale largeEffectivePrev
        (x.indexEquiv ISource).2.val = _
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pPrev
    have hlocalLast : (x.indexEquiv ISource).2.val =
        finrank K (D.largeAlmostJordan.component pPrev).carrier - 1 := by
      have hterminal := hadjacentLarge.2
      change (x.indexEquiv ISource).2.val + 1 =
        finrank K (D.largeAlmostJordan.component pPrev).carrier at hterminal
      omega
    simpa only [hlocalLast, prevScale, largeEffectivePrev] using hlast
  have hsmallPreviousOrder : b.order ISource =
      2 * prevScale - smallEffectivePrev := by
    rw [D.smallWeak_order_eq_localOrder b ISource]
    change JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev))
        (D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev
          (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev)))
        (y.indexEquiv ISource).2.val = _
    rw [hscaleAligned]
    change JordanProfileOrder.localOrder prevScale smallEffectivePrev
        (y.indexEquiv ISource).2.val = _
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pSmallPrev
    have hlocalLast : (y.indexEquiv ISource).2.val =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier - 1 := by
      have hterminal := hadjacentSmall.2
      change (y.indexEquiv ISource).2.val + 1 =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier at hterminal
      omega
    simpa only [hlocalLast, prevScale, smallEffectivePrev,
      hscaleAligned] using hlast
  have houterLe : a.order ISource ≤ a.order INext := by
    have hbound : ISource.val + 2 < n + 2 := by
      dsimp only [ISource, Fin.val_mk]
      have hi := i.one_lt
      have hibound := i.lt_large
      omega
    have hgood := a.good ISource hbound
    calc
      a.order ISource ≤ a.order ⟨ISource.val + 2, hbound⟩ := hgood
      _ = a.order INext := by
        apply congrArg a.order
        apply Fin.ext
        dsimp only [ISource, INext, Fin.val_mk]
        have hi := i.one_lt
        omega
  refine lt_of_le_of_ne houterLe ?_
  intro houterEq
  have heffectiveStrict : largeEffectivePrev < smallEffectivePrev := by
    have htriggerOrder : b.order ISource < a.order INext := by
      simpa only [ISource, INext] using htrigger.1
    rw [← houterEq, hsmallPreviousOrder, hlargePreviousOrder]
      at htriggerOrder
    omega
  have hprevScaleLtCurrent : prevScale < currentScale := by
    have hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hlarge
    simpa only [prevScale, currentScale] using hstrict hpPrevCurrent
  have hcurrentScaleEqSelected : currentScale = selectedScale := by
    simpa only [currentScale, selectedScale, hpCurrentSelected,
      D.largeAlmostJordan_scaleGenerator_selected]
  have hlargeEffectivePrev : largeEffectivePrev = selectedNorm := by
    exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
      pPrev pSmallPrev pPrev prevScale prevScale le_rfl
        (hprevScaleLtCurrent.le.trans_eq hcurrentScaleEqSelected)
          heffectiveStrict
  have hlargeEffectiveCurrent : largeEffectiveCurrent = selectedNorm := by
    exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
      pPrev pSmallPrev pCurrent prevScale currentScale
        hprevScaleLtCurrent.le hcurrentScaleEqSelected.le heffectiveStrict
  have hlocalSucc : (x.indexEquiv ITarget).2.val + 1 <
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    rw [htargetZero, htargetPosition,
      D.largeAlmostJordan_finrank_selected, hfin]
    omega
  have hnextCoordinates := x.indexEquiv_global_succ_eq_local_succ
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) hlocalSucc
  have hlargeNextOrder : a.order INext =
      2 * currentScale - largeEffectiveCurrent := by
    rw [D.largeWeak_order_eq_localOrder a INext, hnextCoordinates]
    change JordanProfileOrder.localOrder currentScale largeEffectiveCurrent
        ((x.indexEquiv ITarget).2.val + 1) = _
    rw [htargetZero]
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pCurrent
    have htargetRank : finrank K
        (D.largeAlmostJordan.component pCurrent).carrier = 2 := by
      rw [hpCurrentSelected, D.largeAlmostJordan_finrank_selected, hfin]
    rw [htargetRank] at hlast
    simpa only [Nat.reduceSubDiff, currentScale,
      largeEffectiveCurrent] using hlast
  rw [hlargePreviousOrder, hlargeNextOrder,
    hlargeEffectivePrev, hlargeEffectiveCurrent] at houterEq
  omega

set_option maxHeartbeats 0 in
theorem weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision_nonterminal
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬ D.LargeScaleCollision)
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
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0)
    (hcomponentNext :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let Rtarget := D.largeNoCollisionCoordinateResolution
        hlarge a ITarget
      Rtarget.component.val + 1 < Rtarget.componentCount) :
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
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rtarget := D.largeNoCollisionCoordinateResolution
    hlarge a ITarget
  change Rtarget.component.val + 1 < Rtarget.componentCount at hcomponentNext
  have hprofileCoordinates := D.largeWeak_noCollision_coordinates_eq
    hlarge a ITarget
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hlocal
  have hresolvedPosition : Rtarget.component =
      D.largeSelectedPosition := by
    change ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
      ITarget).1 = D.largeSelectedPosition
    exact hprofileCoordinates.1.symm.trans htargetPosition
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    change ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
      ITarget).2.val = 0
    exact hprofileCoordinates.2.symm.trans htargetZero
  have hfirst : ITarget.val = Rtarget.coordinates.start := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have hrank : Rtarget.jordan.componentRank Rtarget.component = 2 := by
    change finrank K
      (D.largeAlmostJordan.component Rtarget.component).carrier = 2
    rw [hresolvedPosition, D.largeAlmostJordan_finrank_selected, hfin]
  have hpenultimate : ITarget.val + 2 = Rtarget.coordinates.stop := by
    have hstopFormula : Rtarget.coordinates.stop =
        Rtarget.coordinates.start +
          Rtarget.jordan.componentRank Rtarget.component := by
      rfl
    omega
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    omega
  have hcomponentPositive : 0 < Rtarget.component.val :=
    Rtarget.component_pos_of_first_of_positive htargetPositive hfirst
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
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero rfl
  have hsourceCarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.weakNext.val := by
    rw [← Rsource.jordan_eq]
    exact Rsource.prefixCarrier_eq
  have haligned := D.aligned_prefixCarrier_eq hselected
    (x.indexEquiv ITarget).1.val
  have hcarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
    calc
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val := hsourceCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := by rw [hweakNext]
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := haligned.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := htargetCarrier.symm
  have hleftOuter := D.weakAligned_selected_rank_two_noCollision_leftOuter_lt
    hlarge hselected a b i htrigger hfin hposition hlocal
  have hrightBound : ITarget.val + 2 < n + 2 := by
    rw [hpenultimate]
    exact Rtarget.coordinates_stop_lt_of_component_succ hcomponentNext
  have hleftOuter' : a.order ⟨ITarget.val - 1, by omega⟩ <
      a.order ⟨ITarget.val + 1, by omega⟩ := by
    have hleftIndex :
        (⟨ITarget.val - 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega
    have hrightIndex :
        (⟨ITarget.val + 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega
    rw [hleftIndex, hrightIndex]
    exact hleftOuter
  have hrightLe : a.order ITarget ≤
      a.order ⟨ITarget.val + 2, hrightBound⟩ :=
    a.good ITarget hrightBound
  rcases lt_or_eq_of_le hrightLe with hrightOuter | hrightOuter
  · rcases Rtarget.exists_leftSpaceModel_iv_of_binary_penultimate
        gTarget rfl htargetPositive hpenultimate hrank hcomponentPositive
          hcomponentNext hrightBound hleftOuter' hrightOuter
      with ⟨target, htargetLower, _htargetUpper⟩
    have hsourceToTarget : Rsource.lemma37Model_i.carrier ≤
        target.carrier := by
      rw [Rsource.lemma37Model_i_carrier_eq]
      calc
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              Rsource.weakNext.val =
            (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
              (Rsource.boundary.val + 1) := hsourceCarrier.symm
        _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
              Rtarget.component.val := hcarrier
        _ ≤ target.carrier := htargetLower
    exact .represented
      (BONG.GoodBONG.centralRepresentation_of_approximationModels
        a b hdefect i htrigger target Rsource.lemma37Model_i
          hsourceToTarget)
  · let C :=
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixQuadraticSublattice
        (Rsource.boundary.val + 1)
    let E := Rtarget.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
      Rtarget.component.val
    have hprefix : QuadraticSpace.Isometry C.space E.space :=
      C.spaceIsometryOfCarrierEq E hcarrier
    have hinternal : gTarget.val + 1 < n + 1 := by
      dsimp only [gTarget, Fin.val_mk]
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
        at hrightBound
      omega
    have houter : a.order gTarget.castSucc =
        a.order (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
      have hrightIndex :
          (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ =
            ⟨ITarget.val + 2, hrightBound⟩ := by
        apply Fin.ext
        rfl
      rw [show gTarget.castSucc = ITarget by rfl, hrightIndex]
      exact hrightOuter
    rcases Rtarget.exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first_with_outer
        gTarget rfl htargetPositive hfirst (by omega) hinternal houter
          Rsource.strictProfile Rsource.boundary (by
            simpa only [C, E] using hprefix)
      with ⟨target, hrep⟩
    let sourceBase :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
        b Rsource.strictWeak Rsource.hasImproperEvenRank
          Rsource.scaleOrder_strict Rsource.strictProfile Rsource.boundary
    let sourceSpace : BONG.GoodBONG.SpaceApproximationModel b gSource :=
      sourceBase.castIndex Rsource.strictProfile_boundaryIndex_eq
    let source := sourceSpace.toDiagonal
    have hmodels : DiagonalRepresents
        (diagonalUnitCoefficients source.units)
        (diagonalUnitCoefficients target.units) :=
      sourceBase.castIndex_diagonalRepresents
        Rsource.strictProfile_boundaryIndex_eq hrep
    exact .represented
      (target.centralRepresentation a b hdefect i htrigger source hmodels)

set_option maxHeartbeats 0 in
theorem weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision_terminal
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬ D.LargeScaleCollision)
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
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val = 0)
    (hcomponentLast :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let Rtarget := D.largeNoCollisionCoordinateResolution
        hlarge a ITarget
      Rtarget.component.val + 1 = Rtarget.componentCount) :
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
  let Rtarget := D.largeNoCollisionCoordinateResolution
    hlarge a ITarget
  change Rtarget.component.val + 1 = Rtarget.componentCount at hcomponentLast
  have hprofileCoordinates := D.largeWeak_noCollision_coordinates_eq
    hlarge a ITarget
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hlocal
  have hresolvedPosition : Rtarget.component =
      D.largeSelectedPosition := by
    change ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
      ITarget).1 = D.largeSelectedPosition
    exact hprofileCoordinates.1.symm.trans htargetPosition
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    change ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
      ITarget).2.val = 0
    exact hprofileCoordinates.2.symm.trans htargetZero
  have hfirst : ITarget.val = Rtarget.coordinates.start := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have hrank : Rtarget.jordan.componentRank Rtarget.component = 2 := by
    change finrank K
      (D.largeAlmostJordan.component Rtarget.component).carrier = 2
    rw [hresolvedPosition, D.largeAlmostJordan_finrank_selected, hfin]
  have hpenultimate : ITarget.val + 2 = Rtarget.coordinates.stop := by
    have hstopFormula : Rtarget.coordinates.stop =
        Rtarget.coordinates.start +
          Rtarget.jordan.componentRank Rtarget.component := by
      rfl
    omega
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    omega
  have hcomponentPositive : 0 < Rtarget.component.val :=
    Rtarget.component_pos_of_first_of_positive htargetPositive hfirst
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
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero rfl
  have hsourceCarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.weakNext.val := by
    rw [← Rsource.jordan_eq]
    exact Rsource.prefixCarrier_eq
  have haligned := D.aligned_prefixCarrier_eq hselected
    (x.indexEquiv ITarget).1.val
  have hcarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
    calc
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val := hsourceCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := by rw [hweakNext]
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := haligned.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := htargetCarrier.symm
  have hleftOuter := D.weakAligned_selected_rank_two_noCollision_leftOuter_lt
    hlarge hselected a b i htrigger hfin hposition hlocal
  let p := Rtarget.component
  let pPrev : Fin Rtarget.componentCount := ⟨p.val - 1, by
    have hp := p.isLt
    have hppos := hcomponentPositive
    omega⟩
  have hpPrevSucc : pPrev.val + 1 = p.val := by
    dsimp only [pPrev]
    omega
  have hIio : Finset.Iio p = insert pPrev (Finset.Iio pPrev) := by
    ext z
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change z.val < p.val ↔ z = pPrev ∨ z.val < pPrev.val
    constructor
    · intro hz
      by_cases heq : z.val = pPrev.val
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
    · rintro (rfl | hz) <;> omega
  have hstartSum :
      (∑ z ∈ Finset.Iio p, Rtarget.jordan.componentRank z) =
        ITarget.val := by
    change Rtarget.coordinates.start = ITarget.val
    exact hfirst.symm
  have hprevRankPositive : 0 < Rtarget.jordan.componentRank pPrev :=
    Rtarget.jordan.component_finrank_pos pPrev
  have hprevRankPositiveStrict :
      0 < (Rtarget.strictWeak.toJordan
        Rtarget.scaleOrder_strict).componentRank pPrev := by
    simpa only [BONG.StrictCoordinateResolution.jordan] using
      hprevRankPositive
  have hstartSumStrict :
      (∑ z ∈ Finset.Iio p,
          (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).componentRank z) =
        ITarget.val := by
    simpa only [BONG.StrictCoordinateResolution.jordan] using hstartSum
  have hprevLast : Rtarget.profile.profileComponentLastIndex pPrev =
      ISource := by
    apply Fin.ext
    rw [BONG.JordanOrderProfileWitness.profileComponentLastIndex_val]
    rw [hIio, Finset.sum_insert (by simp)] at hstartSumStrict
    dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk,
      ITarget, gTarget] at hstartSumStrict ⊢
    have := i.one_lt
    have := hprevRankPositiveStrict
    omega
  have hrankStrict :
      (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).componentRank p = 2 := by
    simpa only [p, BONG.StrictCoordinateResolution.jordan] using hrank
  have hsecond : Rtarget.profile.profileComponentSecondIndex p (by
      rw [hrankStrict]
      omega) = INext := by
    apply Fin.ext
    rw [BONG.JordanOrderProfileWitness.profileComponentSecondIndex_val]
    dsimp only [INext, Fin.val_mk]
    rw [hstartSum]
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    omega
  have hleftProfile : ∀ _hp : 0 < p.val,
      a.order (Rtarget.profile.profileComponentLastIndex
        ⟨p.val - 1, by omega⟩) <
        a.order (Rtarget.profile.profileComponentSecondIndex p (by
          rw [hrankStrict]
          omega)) := by
    intro _hp
    have hprevEq : (⟨p.val - 1, by omega⟩ :
        Fin Rtarget.componentCount) = pPrev := by
      apply Fin.ext
      rfl
    rw [hprevEq, hprevLast, hsecond]
    have hsourceIndex : ISource =
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hsourceIndex]
    simpa only [INext] using hleftOuter
  have hrightProfile : ∀ hp : p.val + 1 < Rtarget.componentCount,
      a.order (Rtarget.profile.profileComponentFirstIndex p) <
      a.order (Rtarget.profile.profileComponentFirstIndex
        ⟨p.val + 1, hp⟩) := by
    intro hp
    omega
  have heffectiveP := Rtarget.profile.beli2019Lemma36
    Rtarget.strictWeak Rtarget.hasImproperEvenRank
      Rtarget.scaleOrder_strict p hrankStrict
        hleftProfile hrightProfile
  change Rtarget.strictWeak.effectiveNormOrderAt p
      (ordUnit K (Rtarget.strictWeak.scaleGenerator p)) =
    ordUnit K (Rtarget.strictWeak.normGeneratorUnit p) at heffectiveP
  have hmin : JordanProfileOrder.adjustedAt
      Rtarget.strictWeak.scaleOrderFamily
      Rtarget.strictWeak.normOrderFamily
        (ordUnit K (Rtarget.strictWeak.scaleGenerator p)) p =
      Rtarget.strictWeak.effectiveNormOrderAt p
        (ordUnit K (Rtarget.strictWeak.scaleGenerator p)) := by
    calc
      JordanProfileOrder.adjustedAt Rtarget.strictWeak.scaleOrderFamily
          Rtarget.strictWeak.normOrderFamily
            (ordUnit K (Rtarget.strictWeak.scaleGenerator p)) p =
          ordUnit K (Rtarget.strictWeak.normGeneratorUnit p) := by
            simp [JordanProfileOrder.adjustedAt,
              Lattice.WeakJordanDecomposition.scaleOrderFamily,
              Lattice.WeakJordanDecomposition.normOrderFamily]
      _ = _ := heffectiveP.symm
  let G := BONG.RepresentedFundamentalNormGenerator.ofComponentMinimum
    Rtarget.strictWeak Rtarget.scaleOrder_strict p hmin
  have hpLast : p.val + 1 = Rtarget.componentCount := by
    simpa only [p] using hcomponentLast
  let zLeft : Fin D.complementComponentCount :=
    ⟨p.val - 1, by
      have hpBound := p.isLt
      change p.val < D.complementComponentCount + 1 at hpBound
      omega⟩
  rcases BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_iv_last_nonsingleton
      a Rtarget.strictWeak Rtarget.hasImproperEvenRank
        Rtarget.scaleOrder_strict Rtarget.profile p hcomponentPositive hpLast
          G.value G.fundamental G.componentValue hrankStrict hleftProfile
    with ⟨_A', hleftRankRaw, _hA', _hterminal, happroximationRaw, _hright⟩
  have hpPositive : 0 < p.val := by
    simpa only [p] using hcomponentPositive
  have hzCut : zLeft.val + 1 = p.val := by
    dsimp only [zLeft]
    omega
  have hcomponentZ :
      Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
    apply Fin.ext
    change zLeft.val + 1 = p.val
    exact hzCut
  have hleftRank : 1 <
      (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
    rw [hcomponentZ, hrankStrict]
    omega
  have happroximation : a.IsSpaceApproximation
      (Rtarget.profile.boundaryOneAfterIndex zLeft hleftRank)
      (Rtarget.profile.boundaryOneAfterDiagonalUnits zLeft G.value) := by
    simpa only [zLeft, Rtarget,
      largeNoCollisionCoordinateResolution,
      BONG.JordanOrderProfileWitness.boundaryOneAfterIndex,
      BONG.JordanOrderProfileWitness.boundaryOneAfterDiagonalUnits]
      using happroximationRaw
  have htargetIndex :
      Rtarget.profile.boundaryOneAfterIndex zLeft hleftRank = gTarget := by
    apply Fin.ext
    have hb :=
      Rtarget.profile.boundaryIndex_succ_val_eq_componentRankPrefix zLeft
    have hsumBoundary :
        (∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex zLeft),
          (Rtarget.strictWeak.toJordan
            Rtarget.scaleOrder_strict).componentRank k) = ITarget.val := by
      rw [hcomponentZ]
      exact hstartSumStrict
    have hb' := hb.trans hsumBoundary
    simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex,
      Fin.val_mk]
    dsimp only [gTarget, ITarget, Fin.castSucc_mk, Fin.val_mk]
      at hb' ⊢
    omega
  have horth : ∀ y :
      ((Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (zLeft.val + 1)).carrier,
      q.bilin (y : V) (G.vector : V) = 0 := by
    intro y
    let y' :
        ((Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice p.val).carrier :=
      ⟨(y : V), by simpa only [hzCut] using y.property⟩
    simpa only [y'] using G.prefix_orthogonal_vector y'
  let targetBase : BONG.GoodBONG.SpaceApproximationModel a
      (Rtarget.profile.boundaryOneAfterIndex zLeft hleftRank) :=
    BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneAfter_ofOrthogonalVector
      a (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict)
        Rtarget.profile zLeft G.value hleftRank (G.vector : V)
          G.quadratic_ambientVector horth happroximation
  let target := targetBase.castIndex htargetIndex
  have htargetLower :
      (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
          (zLeft.val + 1) ≤ targetBase.carrier := by
    exact BONG.JordanOrderProfileWitness.PrescribedJordanComparison.prefixCarrier_le_spaceApproximationModel_oneAfter_ofOrthogonalVector
      a (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict)
        Rtarget.profile zLeft G.value hleftRank (G.vector : V)
          G.quadratic_ambientVector horth happroximation
  have hsourceToTarget : Rsource.lemma37Model_i.carrier ≤
      target.carrier := by
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier,
      Rsource.lemma37Model_i_carrier_eq]
    calc
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val =
          (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) := hsourceCarrier.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := hcarrier
      _ = (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (zLeft.val + 1) := by
              simpa only [p, hzCut,
                BONG.StrictCoordinateResolution.jordan]
      _ ≤ targetBase.carrier := htargetLower
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger target Rsource.lemma37Model_i hsourceToTarget)

set_option maxHeartbeats 0 in
theorem weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬ D.LargeScaleCollision)
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
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let Rtarget := D.largeNoCollisionCoordinateResolution
    hlarge a ITarget
  by_cases hnext : Rtarget.component.val + 1 < Rtarget.componentCount
  · apply D.weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision_nonterminal
      hlarge hselected a b hdefect i htrigger hfin hposition hlocal
    simpa only [ITarget, Rtarget] using hnext
  · have hlast : Rtarget.component.val + 1 = Rtarget.componentCount := by
      have hp := Rtarget.component.isLt
      omega
    apply D.weakAligned_centralCertificate_of_targetSelected_rank_two_of_noCollision_terminal
      hlarge hselected a b hdefect i htrigger hfin hposition hlocal
    simpa only [ITarget, Rtarget] using hlast


end Lattice.Beli2019Lemma51Data

end Bong
