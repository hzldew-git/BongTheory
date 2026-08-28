/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveRepresentationRange
import Bong.Bong.Beli2019Lemma37ResolvedModels
import Bong.Bong.Beli2019SectionFiveCarrierGeometry
import Bong.Bong.Beli2019SectionFiveWeakUnaryShift

/-!
# Beli (2019), Section 5: the direct part of condition 2.1(iii)

This file closes the direct range `i \le n_{k_2}+1` of the central
representation condition.  The first layer below converts that numerical
range into collision-safe strict Jordan resolutions on both sides and then
applies Lemma 2.18 to obtain the three endpoint positions of Lemma 3.7.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- In the aligned direct range, the target approximation coordinate
`i-1` and the source approximation coordinate `i-2` both occur no later
than the selected weak component. -/
theorem weakAligned_central_component_bounds
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i) :
    let gTarget : Fin (n + 1) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let gSource : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    ((D.largeWeakProfileWitness a).indexEquiv gTarget.castSucc).1 ≤
        D.largeSelectedPosition ∧
      ((D.smallWeakProfileWitness b).indexEquiv gSource.castSucc).1 ≤
        D.smallSelectedPosition := by
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hstart :=
    D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
  have htargetVal : gTarget.castSucc.val ≤
      x.componentStart D.largeSelectedPosition := by
    change i.val - 1 ≤ D.largeSelectedStart
    change D.largeSelectedStart = D.smallSelectedStart at hstart
    change i.val ≤ D.smallSelectedStart + 1 at hrange
    omega
  have hsourceVal : gSource.castSucc.val ≤
      y.componentStart D.smallSelectedPosition := by
    change i.val - 2 ≤ D.smallSelectedStart
    change i.val ≤ D.smallSelectedStart + 1 at hrange
    have := i.one_lt
    omega
  exact ⟨
    x.component_le_of_index_val_le_componentStart
      gTarget.castSucc D.largeSelectedPosition htargetVal,
    y.component_le_of_index_val_le_componentStart
      gSource.castSucc D.smallSelectedPosition hsourceVal⟩

/-- On the aligned central direct range the source coordinate is strictly
before the selected component, while the target coordinate is either
strictly before it or is its first local coordinate. -/
theorem weakAligned_central_strict_source_and_target_position
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i) :
    let gTarget : Fin (n + 1) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let gSource : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    let x := D.largeWeakProfileWitness a
    let y := D.smallWeakProfileWitness b
    (y.indexEquiv gSource.castSucc).1 < D.smallSelectedPosition ∧
      ((x.indexEquiv gTarget.castSucc).1 < D.largeSelectedPosition ∨
        ((x.indexEquiv gTarget.castSucc).1 = D.largeSelectedPosition ∧
          (x.indexEquiv gTarget.castSucc).2.val = 0)) := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hbounds := D.weakAligned_central_component_bounds
    hselected a b i hrange
  have hsourceGlobal := y.index_val_eq_componentStart_add_local
    gSource.castSucc
  have htargetGlobal := x.index_val_eq_componentStart_add_local
    gTarget.castSucc
  change gSource.castSucc.val =
    y.componentStart (y.indexEquiv gSource.castSucc).1 +
      (y.indexEquiv gSource.castSucc).2.val at hsourceGlobal
  change gTarget.castSucc.val =
    x.componentStart (x.indexEquiv gTarget.castSucc).1 +
      (x.indexEquiv gTarget.castSucc).2.val at htargetGlobal
  have hsourceIndexLt : gSource.castSucc.val < D.smallSelectedStart := by
    change i.val - 2 < D.smallSelectedStart
    change i.val ≤ D.smallSelectedStart + 1 at hrange
    have hiOne := i.one_lt
    omega
  have hsourceStrict : (y.indexEquiv gSource.castSucc).1 <
      D.smallSelectedPosition := by
    apply lt_of_le_of_ne hbounds.2
    intro heq
    have hstartEq : y.componentStart (y.indexEquiv gSource.castSucc).1 =
        D.smallSelectedStart := by
      rw [heq]
      rfl
    rw [hstartEq] at hsourceGlobal
    omega
  refine ⟨hsourceStrict, ?_⟩
  by_cases htargetStrict : (x.indexEquiv gTarget.castSucc).1 <
      D.largeSelectedPosition
  · exact Or.inl htargetStrict
  · right
    have hcomponentEq : (x.indexEquiv gTarget.castSucc).1 =
        D.largeSelectedPosition :=
      le_antisymm hbounds.1 (le_of_not_gt htargetStrict)
    refine ⟨hcomponentEq, ?_⟩
    have hstart :=
      D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
    have htargetIndexLe : gTarget.castSucc.val ≤
        D.largeSelectedStart := by
      change i.val - 1 ≤ D.largeSelectedStart
      change i.val ≤ D.smallSelectedStart + 1 at hrange
      change D.largeSelectedStart = D.smallSelectedStart at hstart
      omega
    have hstartEq : x.componentStart (x.indexEquiv gTarget.castSucc).1 =
        D.largeSelectedStart := by
      rw [hcomponentEq]
      rfl
    rw [hstartEq] at htargetGlobal
    change (x.indexEquiv gTarget.castSucc).2.val = 0
    omega

/-- Collision-safe endpoint data forced by an active central trigger in the
aligned direct range.  Both resolutions are constructed, rather than stored
as laws, and both trichotomies are consequences of Lemma 2.18. -/
theorem weakAligned_central_resolved_endpoints
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i)
    (htrigger : a.centralAlphaTrigger b i) :
    let gTarget : Fin (n + 1) := ⟨i.val - 1, by
      have := i.lt_large
      omega⟩
    let gSource : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    let x := D.largeWeakProfileWitness a
    let y := D.smallWeakProfileWitness b
    ∃ (Rtarget : BONG.StrictCoordinateResolution a.toBONG
          D.largeAlmostJordan x gTarget.castSucc)
      (Rsource : BONG.StrictCoordinateResolution b.toBONG
          D.smallAlmostJordan y gSource.castSucc),
      (gTarget.castSucc.val = Rtarget.coordinates.start ∨
          gTarget.castSucc.val + 1 = Rtarget.coordinates.stop ∨
          gTarget.castSucc.val + 2 = Rtarget.coordinates.stop) ∧
        (gSource.castSucc.val = Rsource.coordinates.start ∨
          gSource.castSucc.val + 1 = Rsource.coordinates.stop ∨
          gSource.castSucc.val + 2 = Rsource.coordinates.stop) := by
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hbounds := D.weakAligned_central_component_bounds
    hselected a b i hrange
  let Rtarget := D.largeStrictCoordinateResolution
    a gTarget.castSucc hbounds.1
  let Rsource := D.smallStrictCoordinateResolution
    b gSource.castSucc hbounds.2
  refine ⟨Rtarget, Rsource, ?_, ?_⟩
  · exact a.centralTrigger_targetResolvedEndpointTrichotomy
      hdefect i htrigger gTarget.castSucc (by
        dsimp only [gTarget, Fin.castSucc_mk, Fin.val_mk]) Rtarget
  · exact a.centralTrigger_sourceResolvedEndpointTrichotomy
      hdefect i htrigger gSource.castSucc (by
        dsimp only [gSource, Fin.castSucc_mk, Fin.val_mk]) Rsource

set_option maxHeartbeats 0 in
/-- In the open interval crossed by the adjacent unary transposition, the
central trigger is impossible.  Lemma 2.18 first reduces the source local
coordinate to the first or penultimate place of the intermediate component.
The explicit weak-profile entries then show that the target order is no
larger than the source order: equality in the effective-proper case and the
opposite strict direction at the even endpoints in the effective-improper
case. -/
theorem weakUnaryShift_not_centralTrigger_in_middle
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
    (hleft : D.largeSelectedStart + 2 ≤ i.val)
    (hright : i.val ≤ D.smallSelectedStart) :
    ¬a.centralAlphaTrigger b i := by
  intro htrigger
  let start := D.largeSelectedStart
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let effective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition i₀) scale
  let j := i.val - 2 - start
  have hcPos : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hstartEnd :=
    D.weakUnaryShift_smallSelectedStart_eq_intervalEnd hfin i₀ hi₀
  change D.smallSelectedStart = start + c at hstartEnd
  have hij : i.val = start + j + 2 := by
    dsimp only [j, start]
    omega
  have hjLt : j < c := by omega
  have hjNextLt : j + 1 < c := by omega
  have hiLt : i.val < n + 2 := i.lt_large
  have hiSubTwoLt : i.val - 2 < n + 2 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hiLt
  have hiSubOneLt : i.val - 1 < n + 2 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hiLt
  have hstartJLt : start + j < n + 2 := by omega
  have hstartJOneLt : start + (j + 1) < n + 2 := by omega
  have hstartJTwoLt : start + (j + 2) < n + 2 := by omega
  have hsmallEntry (ell : Nat) (hell : ell < c)
      (hbound : start + ell < n + 2) :
      b.order ⟨start + ell, hbound⟩ =
        JordanProfileOrder.localOrder scale effective ell := by
    have hraw := D.weakUnaryShift_smallCommon_entry
      hfin i₀ hi₀ a b ell (by simpa only [c] using hell)
    simpa only [start, scale, effective, largeSelectedStart,
      BONG.GoodBONG.orderSequence_at] using hraw
  have hlargeEntry (ell : Nat) (hell : ell < c)
      (hbound : start + (ell + 1) < n + 2) :
      a.order ⟨start + (ell + 1), hbound⟩ =
        JordanProfileOrder.localOrder scale effective ell := by
    have hraw := D.weakUnaryShift_largeCommon_entry
      hfin i₀ hi₀ a ell (by simpa only [c] using hell)
    simpa only [start, scale, effective, largeSelectedStart,
      BONG.GoodBONG.orderSequence_at] using hraw
  have hendpoint : j = 0 ∨ j + 2 = c := by
    by_cases hjZero : j = 0
    · exact Or.inl hjZero
    · right
      by_contra hne
      have hjTwoLt : j + 2 < c := by omega
      have hjPos : 0 < j := Nat.pos_of_ne_zero hjZero
      have hiPrevious : 2 < i.val := by omega
      have hiSubThreeLt : i.val - 3 < n + 2 :=
        lt_of_le_of_lt (Nat.sub_le _ _) hiLt
      have hstartJPredLt : start + (j - 1) < n + 2 := by omega
      have htwoStep := a.centralTrigger_sourceLemma37TwoStepAlternative
        b hdefect i hiPrevious htrigger
      have hleftEq :
          b.order ⟨i.val - 3, hiSubThreeLt⟩ =
            b.order ⟨i.val - 1, hiSubOneLt⟩ := by
        calc
          b.order ⟨i.val - 3, hiSubThreeLt⟩ =
              b.order ⟨start + (j - 1), hstartJPredLt⟩ := by
                apply congrArg b.order
                apply Fin.ext
                change i.val - 3 = start + (j - 1)
                omega
          _ = JordanProfileOrder.localOrder scale effective (j - 1) :=
            hsmallEntry (j - 1) (by omega) hstartJPredLt
          _ = JordanProfileOrder.localOrder scale effective (j + 1) := by
            symm
            have hperiod := JordanProfileOrder.localOrder_add_two
              scale effective (j - 1)
            simpa only [show j - 1 + 2 = j + 1 by omega] using hperiod
          _ = b.order ⟨start + (j + 1), hstartJOneLt⟩ :=
            (hsmallEntry (j + 1) (by omega) hstartJOneLt).symm
          _ = b.order ⟨i.val - 1, hiSubOneLt⟩ := by
            apply congrArg b.order
            apply Fin.ext
            change start + (j + 1) = i.val - 1
            omega
      have hrightEq :
          b.order ⟨i.val - 2, hiSubTwoLt⟩ =
            b.order ⟨i.val, hiLt⟩ := by
        calc
          b.order ⟨i.val - 2, hiSubTwoLt⟩ =
              b.order ⟨start + j, hstartJLt⟩ := by
                apply congrArg b.order
                apply Fin.ext
                change i.val - 2 = start + j
                omega
          _ = JordanProfileOrder.localOrder scale effective j :=
            hsmallEntry j hjLt hstartJLt
          _ = JordanProfileOrder.localOrder scale effective (j + 2) := by
            symm
            exact JordanProfileOrder.localOrder_add_two scale effective j
          _ = b.order ⟨start + (j + 2), hstartJTwoLt⟩ :=
            (hsmallEntry (j + 2) hjTwoLt hstartJTwoLt).symm
          _ = b.order ⟨i.val, hiLt⟩ := by
            apply congrArg b.order
            apply Fin.ext
            change start + (j + 2) = i.val
            omega
      rcases htwoStep with hstrict | hstrict
      · exact (ne_of_lt hstrict hleftEq).elim
      · exact (ne_of_lt hstrict hrightEq).elim
  have hsourceOrder :
      b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ =
        JordanProfileOrder.localOrder scale effective j := by
    calc
      b.order ⟨i.val - 2, hiSubTwoLt⟩ =
          b.order ⟨start + j, hstartJLt⟩ := by
            apply congrArg b.order
            apply Fin.ext
            change i.val - 2 = start + j
            omega
      _ = JordanProfileOrder.localOrder scale effective j :=
        hsmallEntry j hjLt hstartJLt
  have htargetOrder :
      a.order ⟨i.val, i.lt_large⟩ =
        JordanProfileOrder.localOrder scale effective (j + 1) := by
    calc
      a.order ⟨i.val, hiLt⟩ =
          a.order ⟨start + ((j + 1) + 1), hstartJTwoLt⟩ := by
            apply congrArg a.order
            apply Fin.ext
            change i.val = start + ((j + 1) + 1)
            omega
      _ = JordanProfileOrder.localOrder scale effective (j + 1) :=
        hlargeEntry (j + 1) hjNextLt hstartJTwoLt
  have htargetLeSource :
      JordanProfileOrder.localOrder scale effective (j + 1) ≤
        JordanProfileOrder.localOrder scale effective j := by
    rcases D.unaryShift_commonEffectiveNormOrder_cases hfin i₀ hi₀ with
      hproper | himproper
    · change effective = scale at hproper
      rw [hproper, JordanProfileOrder.localOrder_of_proper,
        JordanProfileOrder.localOrder_of_proper]
    · change effective = scale + 1 at himproper
      have hcEven :=
        D.unaryShift_intermediateRank_even_of_effective_eq_add_one
          i₀ (by simpa only [effective, scale] using himproper)
      have hjEven : Even j := by
        rcases hendpoint with hjZero | hjEnd
        · rw [hjZero]
          exact Even.zero
        · rcases hcEven with ⟨k, hk⟩
          refine ⟨k - 1, ?_⟩
          dsimp only [c] at hjEnd hk
          omega
      have hjNextOdd : ¬Even (j + 1) := by
        intro hnext
        rcases hjEven with ⟨k, hk⟩
        rcases hnext with ⟨ell, hell⟩
        omega
      rw [JordanProfileOrder.localOrder_odd_of_scale_le (by omega) hjNextOdd,
        JordanProfileOrder.localOrder_even_of_scale_le (by omega) hjEven]
      omega
  unfold BONG.GoodBONG.centralAlphaTrigger at htrigger
  rw [hsourceOrder, htargetOrder] at htrigger
  exact (not_lt_of_ge htargetLeSource htrigger.1).elim

/-- Complete numerical location of an active central trigger in the
adjacent-unary direct range.  It lies before the exchanged interval, or at
the single boundary immediately after the intermediate common component. -/
theorem weakUnaryShift_centralTrigger_direct_position
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
    i.val ≤ D.largeSelectedStart + 1 ∨
      i.val = D.smallSelectedStart + 1 := by
  by_cases hbefore : i.val ≤ D.largeSelectedStart + 1
  · exact Or.inl hbefore
  · right
    have hleft : D.largeSelectedStart + 2 ≤ i.val := by omega
    change i.val ≤ D.smallSelectedStart + 1 at hrange
    by_cases hmiddle : i.val ≤ D.smallSelectedStart
    · exact (D.weakUnaryShift_not_centralTrigger_in_middle
        hfin i₀ hi₀ a b hdefect i hleft hmiddle htrigger).elim
    · omega

end Lattice.Beli2019Lemma51Data

end Bong
