/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralAligned
import Bong.Bong.Beli2019SectionFiveUnaryImproper

/-!
# Adjacent-unary central representations in Beli (2019), Section 5

This file treats condition 2.1(iii) when the selected unary component crosses
the unique common component of the next scale.  The first theorem is the
terminal boundary `i = n_{k₂} + 1` from the last paragraph of Section 5.14.
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
/-- Section 5.14 at `i = n_{k₂} + 1` in the adjacent-unary case.  The
source model is the complete prefix through the intermediate common
component on the small side.  The target model is the complete prefix through
both exchanged components on the large side, so their carriers are nested. -/
theorem weakUnaryShift_centralCertificate_at_finalBoundary
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = D.smallSelectedStart + 1) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let commonRank := finrank K (D.complementStrictWeak.component i₀).carrier
  have hcommonPos : 0 < commonRank := by
    exact D.complementStrictWeak.component_finrank_pos i₀
  have hstart := D.weakUnaryShift_smallSelectedStart_eq_intervalEnd
    hfin i₀ hi₀
  change D.smallSelectedStart = D.largeSelectedStart + commonRank at hstart
  have hlargeCoordinates : x.indexEquiv gTarget.castSucc =
      ⟨D.smallSelectedPosition,
        ⟨commonRank - 1, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          exact Nat.sub_lt hcommonPos Nat.zero_lt_one⟩⟩ := by
    have hraw := D.weakUnaryShift_largeCommon_indexEquiv
      hfin i₀ hi₀ a (commonRank - 1)
        (Nat.sub_lt hcommonPos Nat.zero_lt_one)
    have hinputEq : gTarget.castSucc =
        (⟨D.largeSelectedStart + ((commonRank - 1) + 1), by
          have hbound := gTarget.castSucc.isLt
          dsimp only [gTarget, Fin.castSucc_mk, Fin.val_mk] at hbound
          omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      dsimp only [gTarget, Fin.castSucc_mk, Fin.val_mk]
      omega
    rw [hinputEq]
    simpa only [x] using hraw
  have hsmallCoordinates : y.indexEquiv gSource.castSucc =
      ⟨D.largeSelectedPosition,
        ⟨commonRank - 1, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact Nat.sub_lt hcommonPos Nat.zero_lt_one⟩⟩ := by
    have hraw := D.weakUnaryShift_smallCommon_indexEquiv
      hfin i₀ hi₀ a b (commonRank - 1)
        (Nat.sub_lt hcommonPos Nat.zero_lt_one)
    have hinputEq : gSource.castSucc =
        (⟨D.largeSelectedStart + (commonRank - 1), by
          have hbound := gSource.castSucc.isLt
          dsimp only [gSource, Fin.castSucc_mk, Fin.val_mk] at hbound
          omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      dsimp only [gSource, Fin.castSucc_mk, Fin.val_mk]
      omega
    rw [hinputEq]
    simpa only [y] using hraw
  have hlargeLast : (x.indexEquiv gTarget.castSucc).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv gTarget.castSucc).1).carrier := by
    rw [hlargeCoordinates]
    dsimp only [Fin.val_mk]
    rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
      hfin i₀ hi₀]
    omega
  have hsmallLast : (y.indexEquiv gSource.castSucc).2.val + 1 =
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv gSource.castSucc).1).carrier := by
    rw [hsmallCoordinates]
    dsimp only [Fin.val_mk]
    rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
      hfin i₀ hi₀]
    omega
  have hlargeSelectedLe : D.largeSelectedPosition ≤
      (x.indexEquiv gTarget.castSucc).1 := by
    rw [hlargeCoordinates]
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val ≤ D.smallSelectedPosition.val
    omega
  have hlargeNext : (x.indexEquiv gTarget.castSucc).1.val <
      D.complementComponentCount := by
    have hcomponentNext :=
      x.component_succ_lt_of_terminal_with_global_succ gTarget.castSucc
        hlargeLast (by
          dsimp only [gTarget, Fin.castSucc_mk, Fin.val_mk]
          have := i.lt_large
          omega)
    omega
  have hsmallBefore : (y.indexEquiv gSource.castSucc).1 <
      D.smallSelectedPosition := by
    rw [hsmallCoordinates]
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val < D.smallSelectedPosition.val
    omega
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution_afterSelected
    a gTarget (by simpa only [x] using hlargeSelectedLe)
      (by simpa only [x] using hlargeLast)
      (by simpa only [x] using hlargeNext)
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y] using hsmallBefore)
      (by simpa only [y] using hsmallLast)
  have hsourceNext : Rsource.weakNext.val =
      D.smallSelectedPosition.val := by
    rw [Rsource.weakNext_val]
    have hsourcePosition := congrArg (fun z ↦ z.1) hsmallCoordinates
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change (y.indexEquiv gSource.castSucc).1.val + 1 =
      D.smallSelectedPosition.val
    change (y.indexEquiv gSource.castSucc).1 =
      D.largeSelectedPosition at hsourcePosition
    have hpositionVal := congrArg Fin.val hsourcePosition
    omega
  have htargetNext : Rtarget.weakNext.val =
      D.smallSelectedPosition.val + 1 := by
    rw [Rtarget.weakNext_val]
    have htargetPosition := congrArg (fun z ↦ z.1) hlargeCoordinates
    change (x.indexEquiv gTarget.castSucc).1.val + 1 =
      D.smallSelectedPosition.val + 1
    exact congrArg (· + 1) (congrArg Fin.val htargetPosition)
  have hcut : Rsource.weakNext.val ≤ Rtarget.weakNext.val := by
    omega
  have hafter : D.smallSelectedPosition.val < Rtarget.weakNext.val := by
    omega
  have hcarrier : Rsource.lemma37Model_i.carrier ≤
      Rtarget.lemma37Model_i.carrier := by
    rw [Rsource.lemma37Model_i_carrier_eq,
      Rtarget.lemma37Model_i_carrier_eq]
    calc
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val ≤
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val :=
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono hcut
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val :=
        (D.unaryShift_prefixCarrier_eq_after hfin i₀ hi₀
          Rtarget.weakNext.val hafter).symm
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger Rtarget.lemma37Model_i
        Rsource.lemma37Model_i hcarrier)

set_option maxHeartbeats 0 in
/-- Section 5.14 at the first boundary of the adjacent-unary interval.  The
target is the selected unary component on the large side, while the same
global coordinate is the first coordinate of the intermediate common
component on the small side. -/
theorem weakUnaryShift_centralCertificate_at_intervalStart
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
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
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have htargetLocal : (x.indexEquiv ITarget).2.val = 0 := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hlocal
  have htargetGlobal := x.index_val_eq_componentStart_add_local ITarget
  change ITarget.val = x.componentStart (x.indexEquiv ITarget).1 +
      (x.indexEquiv ITarget).2.val at htargetGlobal
  have htargetStart : x.componentStart (x.indexEquiv ITarget).1 =
      D.largeSelectedStart := by
    rw [htargetPosition]
    rfl
  have htargetVal : ITarget.val = D.largeSelectedStart := by
    omega
  have hindex : i.val = D.largeSelectedStart + 1 := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk] at htargetVal
    have := i.one_lt
    omega
  have hcommonPos : 0 <
      finrank K (D.complementStrictWeak.component i₀).carrier :=
    D.complementStrictWeak.component_finrank_pos i₀
  have hsmallTargetCoordinates : y.indexEquiv ITarget =
      ⟨D.largeSelectedPosition,
        ⟨0, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact hcommonPos⟩⟩ := by
    have hraw := D.weakUnaryShift_smallCommon_indexEquiv
      hfin i₀ hi₀ a b 0 hcommonPos
    have hinputEq : ITarget =
        (⟨D.largeSelectedStart + 0, by
          have hbound := ITarget.isLt
          dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk] at hbound
          omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      omega
    rw [hinputEq]
    simpa only [y] using hraw
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
                htargetPosition
        _ = 1 := by rw [D.largeAlmostJordan_finrank_selected, hfin]
    omega
  have htargetNext : (x.indexEquiv ITarget).1.val <
      D.complementComponentCount := by
    have hcomponentNext :=
      x.component_succ_lt_of_terminal_with_global_succ ITarget htargetLast (by
        dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
        have := i.lt_large
        omega)
    omega
  have hsmallTargetZero : (y.indexEquiv ITarget).2.val = 0 := by
    rw [hsmallTargetCoordinates]
  have hsourceTerminal :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsmallTargetZero
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have htargetPositionSmall := congrArg (fun z ↦ z.1)
      hsmallTargetCoordinates
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change (y.indexEquiv ISource).1.val < D.smallSelectedPosition.val
    have hsourceSucc := hsourceTerminal.1
    change (y.indexEquiv ISource).1.val + 1 =
      (y.indexEquiv ITarget).1.val at hsourceSucc
    change (y.indexEquiv ITarget).1 =
      D.largeSelectedPosition at htargetPositionSmall
    have htargetPositionVal := congrArg Fin.val htargetPositionSmall
    omega
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [y, ISource] using hsourceTerminal.2)
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution_afterSelected
    a gTarget (by
      simpa only [x, ITarget] using htargetPosition.symm.le)
      (by simpa only [x, ITarget] using htargetLast)
      (by simpa only [x, ITarget] using htargetNext)
  have hsourceSuccVal :
      (y.indexEquiv gSource.castSucc).1.val + 1 =
        (y.indexEquiv gTarget.castSucc).1.val := by
    simpa only [ISource, ITarget] using hsourceTerminal.1
  have hsmallTargetPositionVal :
      (y.indexEquiv gTarget.castSucc).1.val =
        D.largeSelectedPosition.val := by
    have hpositionSmall := congrArg (fun z ↦ z.1)
      hsmallTargetCoordinates
    exact congrArg Fin.val (by
      simpa only [ITarget] using hpositionSmall)
  have hlargeTargetPositionVal :
      (x.indexEquiv gTarget.castSucc).1.val =
        D.largeSelectedPosition.val := by
    exact congrArg Fin.val (by
      simpa only [ITarget] using htargetPosition)
  have hsourceCut : Rsource.weakNext.val ≤
      D.largeSelectedPosition.val := by
    rw [Rsource.weakNext_val]
    change (y.indexEquiv gSource.castSucc).1.val + 1 ≤
      D.largeSelectedPosition.val
    omega
  have hcut : Rsource.weakNext.val ≤ Rtarget.weakNext.val := by
    rw [Rsource.weakNext_val, Rtarget.weakNext_val]
    change (y.indexEquiv gSource.castSucc).1.val + 1 ≤
      (x.indexEquiv gTarget.castSucc).1.val + 1
    omega
  have hcarrier : Rsource.lemma37Model_i.carrier ≤
      Rtarget.lemma37Model_i.carrier := by
    rw [Rsource.lemma37Model_i_carrier_eq,
      Rtarget.lemma37Model_i_carrier_eq,
      ← D.unaryShift_prefixCarrier_eq_before hfin i₀ hi₀
        Rsource.weakNext.val hsourceCut]
    exact D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono hcut
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger Rtarget.lemma37Model_i
        Rsource.lemma37Model_i hcarrier)

/-- If the central target coordinate is before the large selected component,
the preceding source coordinate is before the small selected component in the
adjacent-unary ordering. -/
theorem weakUnaryShift_central_source_before_of_target_before
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition) :
    ((D.smallWeakProfileWitness b).indexEquiv
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
        D.smallSelectedPosition := by
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  have hsucc : ISource < ITarget := by
    change ISource.val < ITarget.val
    dsimp only [ISource, ITarget, Fin.val_mk]
    have := i.one_lt
    omega
  have hlex := (x.order_iff ISource ITarget).mp hsucc
  change Sigma.Lex (fun p q : Fin (D.complementComponentCount + 1) ↦ p < q)
      (fun _ j k ↦ j < k) (x.indexEquiv ISource)
        (x.indexEquiv ITarget) at hlex
  rw [Sigma.lex_iff] at hlex
  have hsourceLargeBefore : (x.indexEquiv ISource).1 <
      D.largeSelectedPosition := by
    rcases hlex with hcomponent | ⟨hcomponent, _hlocal⟩
    · exact hcomponent.trans (by simpa only [x, ITarget] using htargetBefore)
    · exact hcomponent.trans_lt (by simpa only [x, ITarget] using htargetBefore)
  exact D.weakUnaryDirect_small_before hfin i₀ hi₀ a b ISource
    hsourceLargeBefore

set_option maxHeartbeats 0 in
/-- Before the adjacent-unary interval, collision-safe strict resolutions of
the two consecutive central coordinates have the same three possible endpoint
patterns as in the aligned case. -/
theorem weakUnaryShift_central_endpoint_pair_trichotomy_before
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    let ITarget : Fin (n + 2) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let ISource : Fin (n + 2) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    let x := D.largeWeakProfileWitness a
    let y := D.smallWeakProfileWitness b
    let hsourceBefore := D.weakUnaryShift_central_source_before_of_target_before
      hfin i₀ hi₀ a b i htargetBefore
    let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
    let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
    ((ISource.val + 2 = Rsource.coordinates.stop ∧
        ITarget.val + 1 = Rtarget.coordinates.stop) ∨
      (ISource.val + 1 = Rsource.coordinates.stop ∧
        ITarget.val = Rtarget.coordinates.start) ∨
      (ISource.val = Rsource.coordinates.start ∧
        ITarget.val + 2 = Rtarget.coordinates.stop ∧
        (y.indexEquiv ISource).1 = (y.indexEquiv ITarget).1 ∧
        Rsource.jordan.componentRank Rsource.component = 3 ∧
        Rtarget.jordan.componentRank Rtarget.component = 3)) := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let hsourceBefore := D.weakUnaryShift_central_source_before_of_target_before
    hfin i₀ hi₀ a b i htargetBefore
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hsourceBefore' : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    simpa only [y, ISource] using hsourceBefore
  have hsourceOffset : Rsource.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b ISource hsourceBefore.le
  have hsourceComponent : Rsource.strictWeak.component Rsource.component =
      D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
    simpa only [Rsource, y] using
      D.smallStrictCoordinateResolution_component_eq_of_lt
        b ISource hsourceBefore.le hsourceBefore'
  have hsourceCoordinates :=
    Rsource.coordinates_eq_weak_of_offset_zero_of_component_eq
      hsourceOffset hsourceComponent
  have hsourceStart : Rsource.coordinates.start =
      y.componentStart (y.indexEquiv ISource).1 := by
    simpa only [y] using hsourceCoordinates.1
  have hsourceStop : Rsource.coordinates.stop =
      y.componentStop (y.indexEquiv ISource).1 := by
    simpa only [y] using hsourceCoordinates.2
  have htargetOffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore'
  have htargetComponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le htargetBefore' (by
          simpa only [x, ITarget] using hnotCollisionLeft)
  have htargetCoordinatesX :=
    Rtarget.coordinates_eq_weak_of_offset_zero_of_component_eq
      htargetOffset htargetComponent
  have hxyTarget := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have htargetStartXY :
      x.componentStart (x.indexEquiv ITarget).1 =
        y.componentStart (y.indexEquiv ITarget).1 := by
    rw [hxyTarget.1]
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k hk
    have hkTarget : k < (x.indexEquiv ITarget).1 := by
      rw [hxyTarget.1]
      simpa only [Finset.mem_Iio] using hk
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ k
      (hkTarget.trans htargetBefore')
  have htargetRankXY :
      finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ITarget).1).carrier := by
    calc
      finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
          finrank K (D.smallAlmostJordan.component
            (x.indexEquiv ITarget).1).carrier :=
        D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀
          (x.indexEquiv ITarget).1 htargetBefore'
      _ = finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ITarget).1).carrier := by rw [hxyTarget.1]
  have htargetStopXY :
      x.componentStop (x.indexEquiv ITarget).1 =
        y.componentStop (y.indexEquiv ITarget).1 := by
    change x.componentStart (x.indexEquiv ITarget).1 +
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
      y.componentStart (y.indexEquiv ITarget).1 +
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ITarget).1).carrier
    rw [htargetStartXY, htargetRankXY]
  have htargetCoordinates :
      Rtarget.coordinates.start =
          y.componentStart (y.indexEquiv ITarget).1 ∧
        Rtarget.coordinates.stop =
          y.componentStop (y.indexEquiv ITarget).1 :=
    ⟨htargetCoordinatesX.1.trans htargetStartXY,
      htargetCoordinatesX.2.trans htargetStopXY⟩
  have hsourceGlobal := y.index_val_eq_componentStart_add_local ISource
  change ISource.val = y.componentStart (y.indexEquiv ISource).1 +
    (y.indexEquiv ISource).2.val at hsourceGlobal
  have hsourceStopFormula : y.componentStop (y.indexEquiv ISource).1 =
      y.componentStart (y.indexEquiv ISource).1 +
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ISource).1).carrier := by
    rfl
  have htargetGlobal := y.index_val_eq_componentStart_add_local ITarget
  change ITarget.val = y.componentStart (y.indexEquiv ITarget).1 +
    (y.indexEquiv ITarget).2.val at htargetGlobal
  have hsucc : ITarget.val = ISource.val + 1 := by
    dsimp only [ITarget, ISource, Fin.val_mk]
    have := i.one_lt
    omega
  have htargetEndpoints := a.centralTrigger_targetResolvedEndpointTrichotomy
    hdefect i htrigger ITarget (by rfl) Rtarget
  have hsourceEndpoints := a.centralTrigger_sourceResolvedEndpointTrichotomy
    hdefect i htrigger ISource (by rfl) Rsource
  by_cases hinternal : (y.indexEquiv ISource).2.val + 1 <
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv ISource).1).carrier
  · have hnext := y.indexEquiv_global_succ_eq_local_succ
      ISource ITarget hsucc hinternal
    have hcomponentST : (y.indexEquiv ITarget).1 =
        (y.indexEquiv ISource).1 := by
      simpa only using congrArg Sigma.fst hnext
    have hstartST : y.componentStart (y.indexEquiv ITarget).1 =
        y.componentStart (y.indexEquiv ISource).1 := by rw [hcomponentST]
    have hstopST : y.componentStop (y.indexEquiv ITarget).1 =
        y.componentStop (y.indexEquiv ISource).1 := by rw [hcomponentST]
    have hresolvedStartEq : Rtarget.coordinates.start =
        Rsource.coordinates.start :=
      htargetCoordinates.1.trans (hstartST.trans hsourceStart.symm)
    have hresolvedStopEq : Rtarget.coordinates.stop =
        Rsource.coordinates.stop :=
      htargetCoordinates.2.trans (hstopST.trans hsourceStop.symm)
    rcases hsourceEndpoints with hsourceFirst | hsourceLast | hsourcePenultimate
    · rcases htargetEndpoints with htargetFirst | htargetLast |
          htargetPenultimate
      · exfalso
        omega
      · left
        refine ⟨?_, htargetLast⟩
        calc
          ISource.val + 2 = ITarget.val + 1 := by omega
          _ = Rtarget.coordinates.stop := htargetLast
          _ = Rsource.coordinates.stop := hresolvedStopEq
      · have hsourceRank :
            Rsource.jordan.componentRank Rsource.component = 3 := by
          have hstopFormula : Rsource.coordinates.stop =
              Rsource.coordinates.start +
                Rsource.jordan.componentRank Rsource.component := rfl
          omega
        have htargetRank :
            Rtarget.jordan.componentRank Rtarget.component = 3 := by
          have hstopFormula : Rtarget.coordinates.stop =
              Rtarget.coordinates.start +
                Rtarget.jordan.componentRank Rtarget.component := rfl
          omega
        exact Or.inr (Or.inr
          ⟨hsourceFirst, htargetPenultimate, hcomponentST.symm,
            hsourceRank, htargetRank⟩)
    · exfalso
      rw [hsourceStop, hsourceStopFormula] at hsourceLast
      omega
    · left
      refine ⟨hsourcePenultimate, ?_⟩
      calc
        ITarget.val + 1 = ISource.val + 2 := by omega
        _ = Rsource.coordinates.stop := hsourcePenultimate
        _ = Rtarget.coordinates.stop := hresolvedStopEq.symm
  · have hsourceTerminal : (y.indexEquiv ISource).2.val + 1 =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ISource).1).carrier := by
      have hbound := (y.indexEquiv ISource).2.isLt
      omega
    have hnext := y.indexEquiv_global_succ_of_terminal
      ISource ITarget hsucc hsourceTerminal
    right
    left
    constructor
    · rw [hsourceStop, hsourceStopFormula]
      omega
    · rw [htargetCoordinates.1]
      rw [htargetGlobal, hnext.2, Nat.add_zero]

set_option maxHeartbeats 0 in
/-- The collision-left central branch before the adjacent unary
transposition.  The representation argument is shared with the aligned
case; the only inputs supplied here are the local coordinate equality,
common-component position equality, and prefix-carrier equality valid
strictly before the exchanged pair. -/
theorem weakUnaryShift_centralCertificate_of_collisionLeft
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have hsourceBefore :=
    D.weakUnaryShift_central_source_before_of_target_before
      hfin i₀ hi₀ a b i htargetBefore
  have hprefix := D.unaryShift_prefixCarrier_eq_before
    hfin i₀ hi₀ (x.indexEquiv ITarget).1.val (by
      change (x.indexEquiv ITarget).1.val ≤ D.largeSelectedPosition.val
      exact htargetBefore'.le)
  have hcne : c ≠ i₀ := by
    intro hc
    subst c
    rw [hi₀] at hscale
    omega
  have hcommonPosition : D.largeCommonPosition c =
      D.smallCommonPosition c :=
    (D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hcne).symm
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeCommonPosition c := by
    simpa only [x, ITarget] using hposition
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget htargetPosition
  have hendpoints := a.centralTrigger_targetResolvedEndpointTrichotomy
    hdefect i htrigger ITarget (by rfl) Rtarget
  let commonRank := finrank K (D.complementStrictWeak.component c).carrier
  have hcommonRankPos : 0 < commonRank :=
    D.complementStrictWeak.component_finrank_pos c
  have hlocalLt : (x.indexEquiv ITarget).2.val < commonRank := by
    have hraw := (x.indexEquiv ITarget).2.isLt
    have htargetWeakRank : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier =
          commonRank := by
      rw [htargetPosition, D.largeAlmostJordan_finrank_common]
    omega
  have hindex := Rtarget.index_val_eq_coordinates_start_add_local
  have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
      Rtarget.jordan.componentRank Rtarget.component := rfl
  have hresolvedLocal : (Rtarget.profile.indexEquiv ITarget).2.val =
      (x.indexEquiv ITarget).2.val := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal
  have hindexX : ITarget.val = Rtarget.coordinates.start +
      (x.indexEquiv ITarget).2.val := by
    calc
      ITarget.val = Rtarget.coordinates.start +
          (Rtarget.profile.indexEquiv ITarget).2.val := hindex
      _ = Rtarget.coordinates.start +
          (x.indexEquiv ITarget).2.val := by rw [hresolvedLocal]
  rcases D.rank_one_or_two with hOne | hTwo
  · have hrank : Rtarget.jordan.componentRank Rtarget.component =
        commonRank + 1 := by
      simpa only [commonRank, hOne, Nat.add_comm] using
        D.largeCollisionLeftCoordinateResolution_rank
          c hscale a ITarget htargetPosition
    rcases hendpoints with hfirst | hlast | hpenultimate
    · by_cases hrankTwo :
          Rtarget.jordan.componentRank Rtarget.component = 2
      · exact D.centralCertificate_of_collisionLeft_targetFirst_rank_two_of_prefixAlignment
          c hscale a b hdefect i htrigger hOne
            (by simpa only [x, y, ITarget] using hcoordinates)
            (by simpa only [y, ISource] using hsourceBefore)
            (by simpa only [x, ITarget] using hprefix)
            hposition hfirst hrankTwo
      · have hrankHigh : 2 <
            Rtarget.jordan.componentRank Rtarget.component := by omega
        exact D.centralCertificate_of_collisionLeft_targetFirst_highRank_of_prefixAlignment
          c hscale a b hdefect i htrigger htargetBefore
            (by simpa only [x, y, ITarget] using hcoordinates)
            (by simpa only [y, ISource] using hsourceBefore)
            (by simpa only [x, ITarget] using hprefix)
            hposition hfirst hrankHigh
    · exfalso
      omega
    · by_cases hfirst : ITarget.val = Rtarget.coordinates.start
      · have hrankTwo :
            Rtarget.jordan.componentRank Rtarget.component = 2 := by omega
        exact D.centralCertificate_of_collisionLeft_targetFirst_rank_two_of_prefixAlignment
          c hscale a b hdefect i htrigger hOne
            (by simpa only [x, y, ITarget] using hcoordinates)
            (by simpa only [y, ISource] using hsourceBefore)
            (by simpa only [x, ITarget] using hprefix)
            hposition hfirst hrankTwo
      · exact False.elim
          (D.collisionLeft_not_centralTrigger_of_targetPenultimate_notFirst_of_prefixAlignment
            c hscale a b i htrigger hOne
              (by simpa only [x, y, ITarget] using hcoordinates)
              hcommonPosition hposition hpenultimate hfirst)
  · have hrank : Rtarget.jordan.componentRank Rtarget.component =
        commonRank + 2 := by
      simpa only [commonRank, hTwo, Nat.add_comm] using
        D.largeCollisionLeftCoordinateResolution_rank
          c hscale a ITarget htargetPosition
    rcases hendpoints with hfirst | hlast | hpenultimate
    · have hrankHigh : 2 <
          Rtarget.jordan.componentRank Rtarget.component := by omega
      exact D.centralCertificate_of_collisionLeft_targetFirst_highRank_of_prefixAlignment
        c hscale a b hdefect i htrigger htargetBefore
          (by simpa only [x, y, ITarget] using hcoordinates)
          (by simpa only [y, ISource] using hsourceBefore)
          (by simpa only [x, ITarget] using hprefix)
          hposition hfirst hrankHigh
    · exfalso
      omega
    · exfalso
      omega

set_option maxHeartbeats 0 in
/-- The ordinary target-first high-rank branch before the unary
transposition. -/
theorem weakUnaryShift_centralCertificate_of_targetFirst_highRank
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      2 < R.jordan.componentRank R.component) :
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
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change 2 < Rtarget.jordan.componentRank Rtarget.component at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using htargetBefore
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have hsourceNextZero : (y.indexEquiv ITarget).2.val = 0 := by
    rw [← hcoordinates.2]
    exact htargetZero
  have hadjacent :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsourceNextZero
  have hsourceBefore :=
    D.weakUnaryShift_central_source_before_of_target_before
      hfin i₀ hi₀ a b i htargetBefore
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by
      simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore)
      (by simpa only [y, ISource, gSource, Fin.castSucc_mk] using hadjacent.2)
  have hweakNext : Rsource.weakNext.val =
      (x.indexEquiv ITarget).1.val := by
    rw [Rsource.weakNext_val]
    have hcomponentEq := congrArg Fin.val hcoordinates.1
    have hadjacentVal :
        ((D.smallWeakProfileWitness b).indexEquiv gSource.castSucc).1.val + 1 =
          (y.indexEquiv ITarget).1.val := by
      simpa only [y, ISource] using hadjacent.1
    change (x.indexEquiv ITarget).1.val =
      (y.indexEquiv ITarget).1.val at hcomponentEq
    exact hadjacentVal.trans hcomponentEq.symm
  have hprefix := D.unaryShift_prefixCarrier_eq_before
    hfin i₀ hi₀ (x.indexEquiv ITarget).1.val htargetBefore'.le
  exact D.centralCertificate_of_sourceBoundary_targetFirst_of_prefixAlignment
    a b hdefect i htrigger htargetBefore hfirst hrank Rsource
      (by simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hweakNext)
      (by simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hprefix)

set_option maxHeartbeats 0 in
/-- The source-last/target-first rank-one branch before the unary
transposition. -/
theorem weakUnaryShift_centralCertificate_of_sourceLast_targetFirst_rank_one
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hsourceLast :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 1 = R.coordinates.stop)
    (htargetFirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrankOne :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 1)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have htargetBefore' :
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 <
        D.largeSelectedPosition := by
    simpa only [ITarget] using htargetBefore
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  exact D.centralCertificate_of_sourceLast_targetFirst_rank_one_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore
      (by simpa only [ITarget] using hcoordinates)
      (fun k hk => D.unaryShift_prefixCarrier_eq_before hfin i₀ hi₀ k hk)
      hsourceLast htargetFirst hrankOne hnotCollisionLeft

set_option maxHeartbeats 0 in
/-- The ordinary binary target-first branch before the unary transposition. -/
theorem weakUnaryShift_centralCertificate_of_targetFirst_rank_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have htargetCoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  have hfirst' : ITarget.val = Rtarget.coordinates.start := by
    simpa only [ITarget, Rtarget] using hfirst
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hadjacentLarge :=
    x.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetZero
  have hsourceLargeBefore : (x.indexEquiv ISource).1 <
      D.largeSelectedPosition := by
    have hsucc := hadjacentLarge.1
    change (x.indexEquiv ISource).1.val + 1 =
      (x.indexEquiv ITarget).1.val at hsucc
    change (x.indexEquiv ISource).1.val <
      D.largeSelectedPosition.val
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBefore'
    omega
  have hsourceCoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ISource hsourceLargeBefore
  have hsourceBefore :=
    D.weakUnaryShift_central_source_before_of_target_before
      hfin i₀ hi₀ a b i htargetBefore
  have hprefix := D.unaryShift_prefixCarrier_eq_before hfin i₀ hi₀
    (x.indexEquiv ITarget).1.val htargetBefore'.le
  have hleftOuter :=
    D.targetFirst_rank_two_leftOuter_lt_of_notCollision_of_prefixAlignment
      a b i htrigger htargetBefore hfirst hrank hnotCollisionLeft
        (by simpa only [x, y, ITarget] using htargetCoordinates)
        (by simpa only [x, y, ISource] using hsourceCoordinates)
        (fun p hp =>
          (D.weakUnaryShift_scaleOrder_eq_before_selected
            hfin i₀ hi₀ p hp).symm)
  exact D.centralCertificate_of_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    a b hdefect i htrigger htargetBefore
      (by simpa only [x, y, ITarget] using htargetCoordinates)
      (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [x, ITarget] using hprefix)
      hfirst hrank hnotCollisionLeft hleftOuter

set_option maxHeartbeats 0 in
/-- At an even weak coordinate no later than the enlarged unary component,
the direct Section 5 order comparison points from the large-side BONG to
the small-side BONG. -/
theorem weakUnaryShift_order_le_of_component_le_selected_of_local_even
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2)) (hpositive : 0 < I.val)
    (hcomponent :
      ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
        D.largeSelectedPosition)
    (heven : Even
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val) :
    a.order I ≤ b.order I := by
  classical
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 ≤ D.largeSelectedPosition at hcomponent
  rcases lt_or_eq_of_le hcomponent with hbefore | hposition
  · rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
      hselected | ⟨c, hcommon⟩
    · exact False.elim ((ne_of_lt hbefore) hselected)
    · have hne : c ≠ i₀ := by
        have hcommonBefore : D.largeCommonPosition c <
            D.largeSelectedPosition := by
          rw [← hcommon]
          exact hbefore
        intro hc
        subst c
        have hright :=
          D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
            hfin i₀ hi₀
        have hadjacent :=
          D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
            hfin i₀ hi₀
        have hrightVal := congrArg Fin.val hright
        change (D.largeCommonPosition i₀).val <
          D.largeSelectedPosition.val at hcommonBefore
        omega
      have hcommonPositions :=
        D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
      have hsmallBefore : D.smallCommonPosition c <
          D.smallSelectedPosition := by
        have hcommonBefore : D.largeCommonPosition c <
            D.largeSelectedPosition := by
          rw [← hcommon]
          exact hbefore
        have hadjacent :=
          D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
            hfin i₀ hi₀
        rw [hcommonPositions]
        change (D.largeCommonPosition c).val <
          D.smallSelectedPosition.val
        change (D.largeCommonPosition c).val <
          D.largeSelectedPosition.val at hcommonBefore
        omega
      have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
        hfin i₀ hi₀ a b I hbefore
      exact D.weakAligned_common_before_even_order_le_of_alignment
        a b I.val I.isLt c
          (by simpa only [x] using hcommon)
          (by simpa only [x, y] using hcoordinates)
          hcommonPositions hsmallBefore (by simpa only [x] using heven)
  · have hposition' : (x.indexEquiv I).1 =
        D.largeSelectedPosition := hposition
    have hrankLarge : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 1 := by
      rw [hposition', D.weakUnaryShift_largeComponentRank_selected hfin]
    have hlocalZero : (x.indexEquiv I).2.val = 0 := by
      have hlt := (x.indexEquiv I).2.isLt
      omega
    let ri : RepresentationIndex (n + 2) (n + 2) := {
      val := I.val
      pos := hpositive
      lt_large := I.isLt
      le_small := I.isLt.le }
    have hsmallCoordinatesRaw :=
      D.weakUnaryDirect_small_coordinates_at_largeSelected
        hfin i₀ hi₀ a b ri (by
          simpa only [ri, x] using hposition') (by
          simpa only [ri, x] using hlocalZero)
    have hsmallPosition : (y.indexEquiv I).1 =
        D.largeSelectedPosition := by
      simpa only [ri, y] using hsmallCoordinatesRaw.1
    have hsmallZero : (y.indexEquiv I).2.val = 0 := by
      simpa only [ri, y] using hsmallCoordinatesRaw.2
    let selectedScale := ordUnit K D.input.block.enlargedScaleGenerator
    have hlargeScale : ordUnit K
        (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1) =
          selectedScale := by
      rw [hposition', D.largeAlmostJordan_scaleGenerator_selected]
    have hlargeEffective :
        D.largeAlmostJordan.effectiveNormOrderAt
            (x.indexEquiv I).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1)) = selectedScale := by
      rw [hposition', D.largeAlmostJordan_scaleGenerator_selected]
      exact D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hfin
    have hlargeOrder : a.order I = selectedScale := by
      rw [D.largeWeak_order_eq_localOrder a I]
      change JordanProfileOrder.localOrder
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv I).1))
          (D.largeAlmostJordan.effectiveNormOrderAt
            (x.indexEquiv I).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1)))
          (x.indexEquiv I).2.val = selectedScale
      rw [hlargeEffective, hlargeScale, hlocalZero,
        JordanProfileOrder.localOrder_of_proper]
    let middleScale :=
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
    let smallEffective := D.smallAlmostJordan.effectiveNormOrderAt
      (y.indexEquiv I).1 middleScale
    have hsmallScale : ordUnit K
        (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1) =
          middleScale := by
      rw [hsmallPosition,
        ← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
          hfin i₀ hi₀,
        D.smallAlmostJordan_scaleGenerator_common]
    have hscaleEffective : middleScale ≤ smallEffective := by
      exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
        (y.indexEquiv I).1 middleScale
    have hsmallOrder : b.order I = smallEffective := by
      rw [D.smallWeak_order_eq_localOrder b I]
      change JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1))
          (D.smallAlmostJordan.effectiveNormOrderAt
            (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator
              (y.indexEquiv I).1)))
          (y.indexEquiv I).2.val = smallEffective
      rw [hsmallScale, hsmallZero,
        JordanProfileOrder.localOrder_even_of_scale_le
          hscaleEffective Even.zero]
    rw [hlargeOrder, hsmallOrder]
    change selectedScale ≤ smallEffective
    change middleScale = selectedScale + 1 at hi₀
    omega

set_option maxHeartbeats 0 in
/-- In the source-penultimate/target-last endpoint pattern before the unary
transposition, the next large coordinate is local zero in the component
immediately following the target component.  Its direct order is therefore
bounded by the corresponding small order, and the first central-trigger
inequality gives the strict source two-step rise used in Lemma 3.7(iii)/(iv). -/
theorem weakUnaryShift_source_rightTwoStep_lt_of_targetLast
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (htargetLast :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 1 = R.coordinates.stop) :
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩ := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val + 1 = Rtarget.coordinates.stop at htargetLast
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore'
  have hcomponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le htargetBefore' (by
          simpa only [x, ITarget] using hnotCollisionLeft)
  have hcoordinates :=
    Rtarget.coordinates_eq_weak_of_offset_zero_of_component_eq
      hoffset hcomponent
  have hglobal := x.index_val_eq_componentStart_add_local ITarget
  change ITarget.val = x.componentStart (x.indexEquiv ITarget).1 +
    (x.indexEquiv ITarget).2.val at hglobal
  have hterminal : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    rw [hcoordinates.2] at htargetLast
    change ITarget.val + 1 =
      x.componentStart (x.indexEquiv ITarget).1 +
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier at htargetLast
    omega
  have hnext := x.indexEquiv_global_succ_of_terminal
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) hterminal
  have hnextLe : (x.indexEquiv INext).1 ≤
      D.largeSelectedPosition := by
    have hnextComponent := hnext.1
    change (x.indexEquiv INext).1.val ≤ D.largeSelectedPosition.val
    change (x.indexEquiv INext).1.val =
      (x.indexEquiv ITarget).1.val + 1 at hnextComponent
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBefore'
    omega
  have hnextEven : Even (x.indexEquiv INext).2.val := by
    rw [hnext.2]
    exact Even.zero
  have hdirect : a.order INext ≤ b.order INext :=
    D.weakUnaryShift_order_le_of_component_le_selected_of_local_even
      hfin i₀ hi₀ a b INext (by
        dsimp only [INext, Fin.val_mk]
        have := i.one_lt
        omega) hnextLe hnextEven
  unfold BONG.GoodBONG.centralAlphaTrigger at htrigger
  simpa only [INext] using htrigger.1.trans_le hdirect

set_option maxHeartbeats 0 in
/-- The ordinary source-penultimate branch before the adjacent-unary
transposition.  All data required by the common Section 5 proof are supplied
from the direct coordinate/rank agreement and the common carrier prefix
strictly before the exchanged pair. -/
theorem weakUnaryShift_centralCertificate_of_sourcePenultimate
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (htargetLast :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 1 = R.coordinates.stop)
    (hthreeIndex : 3 ≤ i.val)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have htargetRankEq : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier =
    finrank K
      (D.smallAlmostJordan.component (x.indexEquiv ITarget).1).carrier :=
    D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀
      (x.indexEquiv ITarget).1 htargetBefore'
  have hrightOuter :=
    D.weakUnaryShift_source_rightTwoStep_lt_of_targetLast
      hfin i₀ hi₀ a b i htrigger htargetBefore hnotCollisionLeft
        htargetLast
  have hsourceTargetLe : (y.indexEquiv ISource).1 ≤
      (y.indexEquiv ITarget).1 := by
    have hlt : ISource < ITarget := by
      change ISource.val < ITarget.val
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega
    have hlex := (y.order_iff ISource ITarget).mp hlt
    change Sigma.Lex
      (fun p q : Fin (D.complementComponentCount + 1) ↦ p < q)
      (fun _ j k ↦ j < k) (y.indexEquiv ISource)
        (y.indexEquiv ITarget) at hlex
    rw [Sigma.lex_iff] at hlex
    rcases hlex with hcomponent | ⟨hcomponent, _hlocal⟩
    · exact hcomponent.le
    · exact hcomponent.le
  have hcut : (y.indexEquiv ISource).1.val + 1 ≤
      D.largeSelectedPosition.val := by
    have htargetComponent := congrArg Fin.val hcoordinates.1
    change (x.indexEquiv ITarget).1.val =
      (y.indexEquiv ITarget).1.val at htargetComponent
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBefore'
    change (y.indexEquiv ISource).1.val ≤
      (y.indexEquiv ITarget).1.val at hsourceTargetLe
    omega
  have hprefix := D.unaryShift_prefixCarrier_eq_before
    hfin i₀ hi₀ ((y.indexEquiv ISource).1.val + 1) hcut
  exact D.centralCertificate_of_sourcePenultimate_of_notCollision_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore
      (by simpa only [x, y, ITarget] using hcoordinates)
      (by simpa only [x, ITarget] using htargetRankEq)
      hrightOuter (by simpa only [y, ISource] using hprefix)
      hpenultimate hthreeIndex hnotCollisionLeft

set_option maxHeartbeats 0 in
/-- The initial (`i = 2`) source-penultimate branch before the adjacent-unary
transposition. -/
theorem weakUnaryShift_centralCertificate_of_sourcePenultimate_at_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = 2)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (htargetLast :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 1 = R.coordinates.stop)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have htargetRankEq : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier =
    finrank K
      (D.smallAlmostJordan.component (x.indexEquiv ITarget).1).carrier :=
    D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀
      (x.indexEquiv ITarget).1 htargetBefore'
  have hrightOuter :=
    D.weakUnaryShift_source_rightTwoStep_lt_of_targetLast
      hfin i₀ hi₀ a b i htrigger htargetBefore hnotCollisionLeft
        htargetLast
  have hsourceTargetLe : (y.indexEquiv ISource).1 ≤
      (y.indexEquiv ITarget).1 := by
    have hlt : ISource < ITarget := by
      change ISource.val < ITarget.val
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega
    have hlex := (y.order_iff ISource ITarget).mp hlt
    change Sigma.Lex
      (fun p q : Fin (D.complementComponentCount + 1) ↦ p < q)
      (fun _ j k ↦ j < k) (y.indexEquiv ISource)
        (y.indexEquiv ITarget) at hlex
    rw [Sigma.lex_iff] at hlex
    rcases hlex with hcomponent | ⟨hcomponent, _hlocal⟩
    · exact hcomponent.le
    · exact hcomponent.le
  have hcut : (y.indexEquiv ISource).1.val + 1 ≤
      D.largeSelectedPosition.val := by
    have htargetComponent := congrArg Fin.val hcoordinates.1
    change (x.indexEquiv ITarget).1.val =
      (y.indexEquiv ITarget).1.val at htargetComponent
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBefore'
    change (y.indexEquiv ISource).1.val ≤
      (y.indexEquiv ITarget).1.val at hsourceTargetLe
    omega
  have hprefix := D.unaryShift_prefixCarrier_eq_before
    hfin i₀ hi₀ ((y.indexEquiv ISource).1.val + 1) hcut
  exact D.centralCertificate_of_sourcePenultimate_of_notCollision_at_two_of_prefixAlignment
    a b hdefect i htrigger hindex hsourceBefore htargetBefore
      (by simpa only [x, y, ITarget] using hcoordinates)
      (by simpa only [x, ITarget] using htargetRankEq)
      hrightOuter (by simpa only [y, ISource] using hprefix)
      hpenultimate hnotCollisionLeft

set_option maxHeartbeats 0 in
/-- The apparent global-zero proper-ternary endpoint before the unary
transposition is vacuous.  The target penultimate coordinate makes the next
coordinate local two in the same preselected component, so the unary direct
even-coordinate comparison contradicts the central trigger. -/
theorem weakUnaryShift_centralCertificate_of_sourceFirst_at_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hindex : i.val = 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (htargetPenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 2 = R.coordinates.stop)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3)
    (htargetRank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 3) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val + 2 = Rtarget.coordinates.stop at htargetPenultimate
  change Rtarget.jordan.componentRank Rtarget.component = 3 at htargetRank
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore'
  have hcomponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le htargetBefore' (by
          simpa only [x, ITarget] using hnotCollisionLeft)
  have hresolvedLocal :
      (Rtarget.profile.indexEquiv ITarget).2.val = 1 := by
    have hindexResolved := Rtarget.index_val_eq_coordinates_start_add_local
    have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
        Rtarget.jordan.componentRank Rtarget.component := rfl
    omega
  have htargetLocal : (x.indexEquiv ITarget).2.val = 1 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedLocal
  have htargetWeakRank : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier = 3 := by
    change finrank K
      (Rtarget.strictWeak.component Rtarget.component).carrier = 3 at htargetRank
    rw [hcomponent] at htargetRank
    exact htargetRank
  have hnext := x.indexEquiv_global_succ_eq_local_succ
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) (by omega)
  have hnextComponent : (x.indexEquiv INext).1 =
      (x.indexEquiv ITarget).1 := by
    simpa only using congrArg Sigma.fst hnext
  have hnextLocal : (x.indexEquiv INext).2.val = 2 := by
    have hlocal := congrArg (fun z ↦ z.2.val) hnext
    simpa only [Fin.val_mk, htargetLocal] using hlocal
  have hnextLe : (x.indexEquiv INext).1 ≤
      D.largeSelectedPosition := by
    rw [hnextComponent]
    exact htargetBefore'.le
  have hnextEven : Even (x.indexEquiv INext).2.val := by
    rw [hnextLocal]
    norm_num
  have hdirect : a.order INext ≤ b.order INext :=
    D.weakUnaryShift_order_le_of_component_le_selected_of_local_even
      hfin i₀ hi₀ a b INext (by
        dsimp only [INext, Fin.val_mk]
        have := i.one_lt
        omega) hnextLe hnextEven
  exact D.centralCertificate_of_sourceFirst_at_two_of_orderLe
    a b i htrigger hsourceBefore hindex hsourceFirst hsourceRank
      (by simpa only [INext] using hdirect)

set_option maxHeartbeats 0 in
/-- The proper ternary exceptional adjacency before the unary transposition.
The two decompositions have the same ternary component and preceding carrier
prefix there, so the common O'Meara 93:15 construction applies verbatim. -/
theorem weakUnaryShift_centralCertificate_of_sourceFirst_targetPenultimate_ternary
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hsourcePositive : 0 < i.val - 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (htargetPenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 2 = R.coordinates.stop)
    (hsameWeak :
      ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
        ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3)
    (htargetRank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 3) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have htargetCoordinates := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b ITarget htargetBefore'
  have hcomponentAlignment := D.unaryShift_component_eq_before
    hfin i₀ hi₀ (x.indexEquiv ITarget).1 htargetBefore'
  have hcut : (y.indexEquiv ISource).1.val ≤
      D.largeSelectedPosition.val := by
    have hsourceBefore' := hsourceBefore
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val at hsourceBefore'
    have hadjacent :=
      D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀
    omega
  have hprefixCarrier := D.unaryShift_prefixCarrier_eq_before
    hfin i₀ hi₀ (y.indexEquiv ISource).1.val hcut
  exact D.centralCertificate_of_sourceFirst_targetPenultimate_ternary_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore hnotCollisionLeft
      hsourcePositive hsourceFirst htargetPenultimate hsameWeak
      (by simpa only [x, y, ITarget] using htargetCoordinates.1)
      (by simpa only [x, ITarget] using hcomponentAlignment)
      (by simpa only [y, ISource] using hprefixCarrier)
      hsourceRank htargetRank

set_option maxHeartbeats 0 in
/-- Complete the ordinary target-before-selected range in the adjacent-unary
ordering, away from the unique left collision. -/
theorem weakUnaryShift_centralCertificate_before_of_notCollisionLeft
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let hsourceBefore :=
    D.weakUnaryShift_central_source_before_of_target_before
      hfin i₀ hi₀ a b i htargetBefore
  have htri := D.weakUnaryShift_central_endpoint_pair_trichotomy_before
    hfin i₀ hi₀ a b hdefect i htrigger htargetBefore hnotCollisionLeft
  rcases htri with hsourcePenultimate | htargetFirst | hternary
  · by_cases hindex : i.val = 2
    · exact D.weakUnaryShift_centralCertificate_of_sourcePenultimate_at_two
        hfin i₀ hi₀ a b hdefect i htrigger hindex hsourceBefore
          htargetBefore hsourcePenultimate.1 hsourcePenultimate.2
            hnotCollisionLeft
    · have hthree : 3 ≤ i.val := by
        have := i.one_lt
        omega
      exact D.weakUnaryShift_centralCertificate_of_sourcePenultimate
        hfin i₀ hi₀ a b hdefect i htrigger hsourceBefore htargetBefore
          hsourcePenultimate.1 hsourcePenultimate.2 hthree hnotCollisionLeft
  · let Rtarget :=
      D.largeStrictCoordinateResolution a ITarget htargetBefore.le
    have hrankPos : 0 < Rtarget.jordan.componentRank Rtarget.component :=
      Rtarget.jordan.component_finrank_pos Rtarget.component
    by_cases hrankOne : Rtarget.jordan.componentRank Rtarget.component = 1
    · exact D.weakUnaryShift_centralCertificate_of_sourceLast_targetFirst_rank_one
        hfin i₀ hi₀ a b hdefect i htrigger hsourceBefore htargetBefore
          htargetFirst.1 htargetFirst.2 (by
            simpa only [Rtarget, ITarget] using hrankOne) hnotCollisionLeft
    · by_cases hrankTwo : Rtarget.jordan.componentRank Rtarget.component = 2
      · exact D.weakUnaryShift_centralCertificate_of_targetFirst_rank_two
          hfin i₀ hi₀ a b hdefect i htrigger htargetBefore
            htargetFirst.2 (by simpa only [Rtarget, ITarget] using hrankTwo)
              hnotCollisionLeft
      · have hrankHigh : 2 <
            Rtarget.jordan.componentRank Rtarget.component := by omega
        exact D.weakUnaryShift_centralCertificate_of_targetFirst_highRank
          hfin i₀ hi₀ a b hdefect i htrigger htargetBefore
            htargetFirst.2 (by simpa only [Rtarget, ITarget] using hrankHigh)
  · by_cases hindex : i.val = 2
    · exact D.weakUnaryShift_centralCertificate_of_sourceFirst_at_two
        hfin i₀ hi₀ a b i htrigger hsourceBefore htargetBefore
          hnotCollisionLeft hindex hternary.1 hternary.2.1
            hternary.2.2.2.1 hternary.2.2.2.2
    · have hsourcePositive : 0 < i.val - 2 := by
        have := i.one_lt
        omega
      exact D.weakUnaryShift_centralCertificate_of_sourceFirst_targetPenultimate_ternary
        hfin i₀ hi₀ a b hdefect i htrigger hsourceBefore htargetBefore
          hnotCollisionLeft hsourcePositive hternary.1 hternary.2.1
            hternary.2.2.1 hternary.2.2.2.1 hternary.2.2.2.2

set_option maxHeartbeats 0 in
/-- Complete Section 5's direct central certificate in the adjacent-unary
ordering.  An active trigger is either before the exchanged interval, at its
initial boundary, or at the single final boundary. -/
theorem weakUnaryShift_centralCertificate
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i)
    (htrigger : a.centralAlphaTrigger b i) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  rcases D.weakUnaryShift_centralTrigger_direct_position
      hfin i₀ hi₀ a b hdefect i hrange htrigger with
    hbefore | hfinal
  · by_cases hstart : i.val = D.largeSelectedStart + 1
    · have htargetVal : ITarget.val = D.largeSelectedStart := by
        dsimp only [ITarget, Fin.val_mk]
        omega
      have hrank := D.weakUnaryShift_largeComponentRank_selected hfin
      let zero : Fin (finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier) :=
        ⟨0, by rw [hrank]; omega⟩
      have hinput : ITarget =
          x.indexEquiv.symm ⟨D.largeSelectedPosition, zero⟩ := by
        apply Fin.ext
        rw [htargetVal]
        exact (x.inverse_index_val D.largeSelectedPosition zero).symm
      have hcoordinates : x.indexEquiv ITarget =
          ⟨D.largeSelectedPosition, zero⟩ := by
        rw [hinput, x.indexEquiv.apply_symm_apply]
      exact D.weakUnaryShift_centralCertificate_at_intervalStart
        hfin i₀ hi₀ a b hdefect i htrigger
          (by
            have hposition := congrArg Sigma.fst hcoordinates
            simpa only [x, ITarget] using hposition)
          (by
            have hlocal := congrArg (fun z ↦ z.2.val) hcoordinates
            simpa only [x, ITarget, zero, Fin.val_mk] using hlocal)
    · have hstrictIndex : ITarget.val < D.largeSelectedStart := by
        dsimp only [ITarget, Fin.val_mk]
        have := i.one_lt
        omega
      have htargetBefore :
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 <
            D.largeSelectedPosition :=
        D.weakUnaryShift_component_before_of_index_lt_start
          a ITarget hstrictIndex
      by_cases hcollisionLeft : ∃ c : Fin D.complementComponentCount,
          ordUnit K (D.complementStrictWeak.scaleGenerator c) =
              ordUnit K D.input.block.enlargedScaleGenerator ∧
            ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
              D.largeCommonPosition c
      · obtain ⟨c, hscale, hposition⟩ := hcollisionLeft
        exact D.weakUnaryShift_centralCertificate_of_collisionLeft
          hfin i₀ hi₀ c hscale a b hdefect i htrigger
            (by simpa only [ITarget] using htargetBefore)
            (by simpa only [ITarget] using hposition)
      · exact D.weakUnaryShift_centralCertificate_before_of_notCollisionLeft
          hfin i₀ hi₀ a b hdefect i htrigger
            (by simpa only [ITarget] using htargetBefore)
            (by simpa only [ITarget] using hcollisionLeft)
  · exact D.weakUnaryShift_centralCertificate_at_finalBoundary
      hfin i₀ hi₀ a b hdefect i htrigger hfinal

end Lattice.Beli2019Lemma51Data

end Bong
