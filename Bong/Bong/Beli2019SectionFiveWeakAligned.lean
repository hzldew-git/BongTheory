/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveOddBound
import Bong.Bong.Beli2019Lemma517CollisionProfiles
import Bong.Bong.Beli2019SectionFiveGapTwoAlpha
import Bong.Bong.Beli2019Lemma515
import Bong.Bong.BinaryModularInvariant
import Bong.Bong.Beli2019PrefixThroughApproximation

/-!
# Beli (2019), Section 5: the collision-safe weak-aligned range

This file closes the aligned branch of condition 2.1(ii), including equal
weak Jordan scales on either side of the distinguished component.  The final
binary boundary is reduced to Corollary 5.15; its half-gap and finite-defect
alternatives both imply that the representation alpha is nonpositive.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- The enlarged vector belongs to the canonical large scale truncation at
every common component preceding the selected block. -/
theorem enlargedVector_mem_largeScaleTruncation_before_selected
    (D : Beli2019Lemma51Data q M N)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) := by
  let r := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  have hscale : r ≤
      ordUnit K (D.largeAlmostJordan.scaleGenerator
        D.largeSelectedPosition) :=
    (D.largeAlmostJordan.scaleOrder_mono hp.le)
  let H := D.largeAlmostJordan.toOrthogonalDecomposition
  have hfactor :
      Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
        D.largeAlmostJordan.scaleGenerator r
          D.largeSelectedPosition = 1 := by
    unfold Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
      Lattice.positivePartUnit
    rw [if_neg]
    rw [ordUnit_mul, ordUnit_inv, Lattice.scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit]
    omega
  let T := H.modularScaleTruncationDecomposition
    D.largeAlmostJordan.scaleGenerator D.largeAlmostJordan.modular r
  have hcomponent : T.component D.largeSelectedPosition =
      D.largeAlmostJordan.component D.largeSelectedPosition := by
    change (D.largeAlmostJordan.component
      D.largeSelectedPosition).rescaleLattice
        (Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
          D.largeAlmostJordan.scaleGenerator r
            D.largeSelectedPosition) = _
    rw [hfactor]
    cases D.largeAlmostJordan.component D.largeSelectedPosition
    simp [QuadraticSublattice.rescaleLattice, Lattice.rescale_one]
  have hyEnlarged :
      ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
        D.input.enlargedComponent.ambientSubmodule :=
    ⟨D.input.enlargedVector, Lattice.mem_adjoinVector _ _, rfl⟩
  have hySelected :
      ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
        (D.largeAlmostJordan.component
          D.largeSelectedPosition).ambientSubmodule := by
    simpa only [D.largeAlmostJordan_component_selected] using hyEnlarged
  have hyComponent :
      ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
        (T.component D.largeSelectedPosition).ambientSubmodule := by
    rw [hcomponent]
    exact hySelected
  have hyTrunc := T.component_ambientSubmodule_le
    D.largeSelectedPosition hyComponent
  change ((D.input.enlargedVector :
      D.input.block.component.carrier) : V) ∈
    (Lattice.scaleTruncation q M
      (ordUnit K (D.largeAlmostJordan.scaleGenerator p))).toSubmodule
  simpa only [r, T] using hyTrunc

/-- At a common weak scale before the selected component, adjoining the
Lemma 5.1 enlarged vector to the small intrinsic truncation gives the large
intrinsic truncation.  This formulation is independent of any strict
resolution of the possible equal-scale pair. -/
theorem adjoin_enlargedVector_smallScaleTruncation_eq_large
    (D : Beli2019Lemma51Data q M N)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition)
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p)) :
    Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p)))
        (((D.input.enlargedVector :
          D.input.block.component.carrier) : V)) =
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) := by
  let r := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let y : V := ((D.input.enlargedVector :
    D.input.block.component.carrier) : V)
  have hbound : r ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hs := D.largeAlmostJordan.scaleOrder_mono hp.le
    simpa only [r, D.largeAlmostJordan_scaleGenerator_selected] using hs
  have hsmallLarge :
      Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p)) ≤
        Lattice.scaleTruncation q M r := by
    rw [← hscale]
    exact D.scaleTruncation_small_le_large r hbound
  have hyLarge : y ∈ Lattice.scaleTruncation q M r := by
    simpa only [y, r] using
      D.enlargedVector_mem_largeScaleTruncation_before_selected p hp
  apply Lattice.ext
  apply le_antisymm
  · exact Lattice.adjoinVector_le hsmallLarge hyLarge
  · intro z hz
    have hzM : z ∈ M :=
      (Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mp hz).1
    have hzAdjoin : z ∈ Lattice.adjoinVector N y := by
      dsimp only [y, Beli2019Lemma51InputData.enlargedVector]
      change z ∈ Lattice.adjoinVector N
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) •
          (D.input.block.carrierRepresentative : V))
      rw [D.input.block.coe_carrierRepresentative,
        D.input.enlarged_eq]
      exact hzM
    rw [Lattice.mem_adjoinVector_iff] at hzAdjoin
    rcases hzAdjoin with ⟨n, hn, c, hsum⟩
    have hcyLarge : c • y ∈ Lattice.scaleTruncation q M r :=
      (Lattice.scaleTruncation q M r).smul_mem c hyLarge
    have hnEq : n = z - c • y := by
      rw [← hsum]
      abel
    have hnLarge : n ∈ Lattice.scaleTruncation q M r := by
      rw [hnEq]
      exact (Lattice.scaleTruncation q M r).sub_mem hz hcyLarge
    have hnData :=
      Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mp hnLarge
    have hnSmall : n ∈ Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator p)) := by
      rw [← hscale]
      apply Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mpr
      exact ⟨hn, fun w hw ↦ hnData.2 w (D.smallLattice_le_large hw)⟩
    rw [← hsum]
    have hyAdj : y ∈ Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p))) y :=
      Lattice.mem_adjoinVector _ _
    exact (Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p))) y).add_mem
      (Lattice.le_adjoinVector _ _ hnSmall)
      ((Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator p))) y).smul_mem
            c hyAdj)

/-- Collision-safe gap-two weight equality at an aligned coordinate before
the selected component. -/
theorem weakAligned_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    Lattice.weightIdeal q
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1))) =
      Lattice.weightIdeal q
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            ((D.smallWeakProfileWitness b).indexEquiv i.castSucc).1))) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective :=
    D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hsmallBefore : r < D.smallSelectedPosition := by
    rw [hselected, ← hrp]
    exact hbefore
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by
        change b.order i.castSucc < a.order i.castSucc
        omega
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap : targetEffective = sourceEffective + 2 := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
      at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
      at htargetLocalNormalized
    change a.order I = b.order I + 2 at hcurrent
    omega
  let Rlarge := D.largeStrictCoordinateResolution a I hbefore.le
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBefore.le
  have hrescale : Lattice.rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p))) ≤
      Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp, hscaleRaw]
    exact D.rescale_largeScaleTruncation_le_small
      (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
  have hpos : 0 < finrank K V := by
    rw [← a.toBONG.length_eq_finrank]
    omega
  have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
    hpos hrescale (by
      change targetEffective = sourceEffective + 2
      exact heffectiveGap)
  let A := Rlarge.fundamentalNormGenerator
  change Lattice.IsNormGeneratorValue q Rlarge.fundamentalLattice A ∧
      Lattice.IsNormGeneratorValue q Rsmall.fundamentalLattice
        ((uniformizerUnit K) ^ 2 * A) at hpair
  obtain ⟨z, hz, hzanis⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos q
      Rlarge.fundamentalLattice hpos
  let X : Kˣ := Units.mk0 (q.quadratic z) hzanis
  have hXcoe : (X : K) = q.quadratic z := rfl
  have hprincipalXA :
      Lattice.principalIdeal (K := K) (X : K) =
        Lattice.principalIdeal (K := K) (A : K) := by
    rw [hXcoe]
    exact hz.normIdeal_eq.symm.trans hpair.1.2
  have hXA : ordUnit K X = ordUnit K A :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq X A).mp hprincipalXA
  have hznot : z ∉ Rsmall.fundamentalLattice := by
    intro hzSmall
    have hqzSmall : q.quadratic z ∈
        Lattice.principalIdeal (K := K)
          ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) := by
      rw [← hpair.2.2]
      exact Lattice.quadratic_mem_normIdeal_of_mem q
        Rsmall.fundamentalLattice hzSmall
    have hord := Lattice.ord_le_of_mem_principalIdeal
      (Units.ne_zero ((uniformizerUnit K) ^ 2 * A)) hqzSmall
    have hord' : ordUnit K ((uniformizerUnit K) ^ 2 * A) ≤
        ordUnit K X := by
      apply WithTop.coe_le_coe.mp
      simpa only [Dyadic.coe_ordUnit, hXcoe] using hord
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    simp only [ordUnit_mul, ordUnit_pow, hpi] at hord'
    rw [hXA] at hord'
    omega
  let enlarged : V := ((D.input.enlargedVector :
    D.input.block.component.carrier) : V)
  have hadjoinY : Lattice.adjoinVector Rsmall.fundamentalLattice enlarged =
      Rlarge.fundamentalLattice := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation,
      Rlarge.fundamentalLattice_eq_scaleTruncation]
    change Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r))) enlarged =
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p))
    rw [← hrp]
    simpa only [enlarged] using
      D.adjoin_enlargedVector_smallScaleTruncation_eq_large
        p hbefore hscaleRaw
  have hyLarge : enlarged ∈ Rlarge.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation]
    change enlarged ∈ Lattice.scaleTruncation q M
      (ordUnit K (D.largeAlmostJordan.scaleGenerator p))
    simpa only [enlarged] using
      D.enlargedVector_mem_largeScaleTruncation_before_selected p hbefore
  have hpiYField : (uniformizer K) • enlarged ∈
      Rsmall.fundamentalLattice := by
    apply hrescale
    exact Lattice.smul_mem_rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice hyLarge
  have hpiY : (uniformizerInteger K) • enlarged ∈
      Rsmall.fundamentalLattice := by
    change (uniformizer K) • enlarged ∈ Rsmall.fundamentalLattice
    exact hpiYField
  have hadjoinX : Lattice.adjoinVector Rsmall.fundamentalLattice z =
      Rlarge.fundamentalLattice :=
    Lattice.adjoinVector_eq_of_uniformizer_smul_mem_of_not_mem
      hadjoinY hpiY hz.mem hznot
  have hpiXField : (uniformizer K) • z ∈ Rsmall.fundamentalLattice := by
    apply hrescale
    exact Lattice.smul_mem_rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice hz.mem
  have hpiX : (uniformizerInteger K) • z ∈
      Rsmall.fundamentalLattice := by
    change (uniformizer K) • z ∈ Rsmall.fundamentalLattice
    exact hpiXField
  have hsmallX : Lattice.IsNormGeneratorValue q
      Rsmall.fundamentalLattice ((uniformizerUnit K) ^ 2 * X) := by
    constructor
    · refine ⟨(uniformizerInteger K) • z, hpiX, 0,
        Submodule.zero_mem _, ?_⟩
      have hscalar :
          algebraMap (IntegerRing K) K (uniformizerInteger K) =
            uniformizer K := rfl
      rw [add_zero, ← IsScalarTower.algebraMap_smul K
        (uniformizerInteger K) z, q.quadratic_smul, hscalar]
      change ((((uniformizerUnit K) ^ 2 * X : Kˣ) : K)) =
        uniformizer K ^ 2 * q.quadratic z
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, X,
        Units.val_mk0, coe_uniformizerUnit]
    · apply hpair.2.2.trans
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
        ((uniformizerUnit K) ^ 2 * A)
        ((uniformizerUnit K) ^ 2 * X)).2
      simp only [ordUnit_mul, ordUnit_pow, hXA]
  have hscaleResolved :
      Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component := by
    calc
      Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) :=
        Rsmall.scaleOrder_eq
      _ = ordUnit K (D.largeAlmostJordan.scaleGenerator p) := by
        rw [← hrp]
        exact hscaleRaw.symm
      _ = Rlarge.jordan.fundamentalScaleOrder Rlarge.component :=
        Rlarge.scaleOrder_eq.symm
  have htwo : Lattice.twoScaleIdeal q Rsmall.fundamentalLattice =
      Lattice.twoScaleIdeal q Rlarge.fundamentalLattice := by
    unfold Lattice.twoScaleIdeal
    congr 1
    calc
      Lattice.scaleIdeal q Rsmall.fundamentalLattice =
          Lattice.powerIdeal (K := K)
            (Rsmall.jordan.fundamentalScaleOrder Rsmall.component) :=
        Rsmall.jordan.scaleIdeal_scaleTruncation_at_component Rsmall.component
      _ = Lattice.powerIdeal (K := K)
          (Rlarge.jordan.fundamentalScaleOrder Rlarge.component) := by
        rw [hscaleResolved]
      _ = Lattice.scaleIdeal q Rlarge.fundamentalLattice :=
        (Rlarge.jordan.scaleIdeal_scaleTruncation_at_component
          Rlarge.component).symm
  have hweight := Lattice.weightIdeal_eq_of_adjoin_normGenerator_gapTwo
    hz hzanis hadjoinX hsmallX htwo
  rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
    Rsmall.fundamentalLattice_eq_scaleTruncation] at hweight
  simpa only [x, y, p, r, I] using hweight

/-- A reverse strict order inequality before the selected component forces
the current weak local coordinate to be positive. -/
theorem weakAligned_current_local_pos_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    0 < ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).2.val := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized : b.order I =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by simpa only [I] using hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have hpos : 0 < localIndex := by
    by_contra hnot
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  simpa only [localIndex, x, I] using hpos

/-- In the collision-safe gap-two branch, the common intrinsic fundamental
weight gives equality of the two preceding alpha endpoints. -/
theorem weakAligned_previous_order_add_alpha_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    ∃ hpos : 0 < i.val,
      (a.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          a.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
        (b.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          b.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hsmallBefore : r < D.smallSelectedPosition := by
    rw [hselected, ← hrp]
    exact hbefore
  let Rlarge := D.largeStrictCoordinateResolution a I hbefore.le
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBefore.le
  have hgt : b.order i.castSucc < a.order i.castSucc := by omega
  have hsourceWeakPos :=
    D.weakAligned_current_local_pos_of_current_gt
      hselected a b i hbefore hgt
  have htargetWeakPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    simpa only [x, I] using hsourceWeakPos
  have hlargeOffset :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hbefore.le hbefore
  have hsmallOffset :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallBefore.le
  have hsourceResolvedPos :
      0 < (Rlarge.profile.indexEquiv I).2.val := by
    rw [Rlarge.localCoordinate_eq, hlargeOffset, Nat.zero_add]
    simpa only [x] using hsourceWeakPos
  have htargetResolvedPos :
      0 < (Rsmall.profile.indexEquiv I).2.val := by
    rw [Rsmall.localCoordinate_eq, hsmallOffset, Nat.zero_add]
    exact htargetWeakPos
  rcases previous_profile_coordinate_internal_of_current_local_pos
      a Rlarge.profile i hsourceResolvedPos with
    ⟨hipos, hsourceComponent, hsourceInternal⟩
  rcases previous_profile_coordinate_internal_of_current_local_pos
      b Rsmall.profile i htargetResolvedPos with
    ⟨_, htargetComponent, htargetInternal⟩
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hweightIdeal :=
    D.weakAligned_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
      hselected a b i hbefore hcurrent
  have hweightOrder :
      Rlarge.jordan.fundamentalWeightOrder Rlarge.component =
        Rsmall.jordan.fundamentalWeightOrder Rsmall.component := by
    unfold Lattice.JordanDecomposition.fundamentalWeightOrder
    apply Lattice.powerIdeal_injective (K := K)
    rw [← Lattice.weightIdeal_eq_powerIdeal,
      ← Lattice.weightIdeal_eq_powerIdeal]
    change Lattice.weightIdeal q Rlarge.fundamentalLattice =
      Lattice.weightIdeal q Rsmall.fundamentalLattice
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    simpa only [x, y, I] using hweightIdeal
  have hsourceFormula :=
    Rlarge.profile.internal_weightOrder_eq_order_add_alpha
      previous hsourceInternal
  have htargetFormula :=
    Rsmall.profile.internal_weightOrder_eq_order_add_alpha
      previous htargetInternal
  have hsourceComponent' :
      (Rlarge.profile.indexEquiv previous.castSucc).1 =
        Rlarge.component := by
    simpa only [previous, I, BONG.StrictCoordinateResolution.component] using
      hsourceComponent
  have htargetComponent' :
      (Rsmall.profile.indexEquiv previous.castSucc).1 =
        Rsmall.component := by
    simpa only [previous, I, BONG.StrictCoordinateResolution.component] using
      htargetComponent
  rw [hsourceComponent'] at hsourceFormula
  rw [htargetComponent'] at htargetFormula
  have hweightQ :
      (Rlarge.jordan.fundamentalWeightOrder Rlarge.component : ℚ) =
        (Rsmall.jordan.fundamentalWeightOrder Rsmall.component : ℚ) := by
    exact_mod_cast hweightOrder
  refine ⟨hipos, ?_⟩
  change (a.order previous.castSucc : ℚ) + a.alphaValue previous =
    (b.order previous.castSucc : ℚ) + b.alphaValue previous
  linarith

/-- Collision-safe version of the weight endpoint comparison in case 1(b).
The possible equal-scale neighbours are first merged by the coordinate-local
strict resolutions. -/
theorem weakAligned_order_add_alphaValue_le_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    (a.order i.castSucc : ℚ) + a.alphaValue i ≤
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact congrFun (D.almostJordan_componentRank_eq hselected) p
  have hweakInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hlargeLe : (x.indexEquiv I).1 ≤ D.largeSelectedPosition :=
    hbefore.le
  have hsmallLe : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ ≤ D.largeSelectedPosition := hlargeLe
      _ = D.smallSelectedPosition := hselected.symm
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe (Or.inl (by simpa only [p, localIndex] using hweakInternal))
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hscales := D.weakAligned_fundamentalScale_interval
    hselected a b I (Or.inl hbefore)
  change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K D.input.block.enlargedScaleGenerator at hscales
  have hscale : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      Rsmall.jordan.fundamentalScaleOrder
        (Rsmall.profile.indexEquiv I).1 := by
    rw [Rlarge.scaleOrder_eq, Rsmall.scaleOrder_eq]
    exact hscales.1
  have hbound : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    rw [Rlarge.scaleOrder_eq]
    exact hscales.2
  have hfundamental :
      Rsmall.jordan.fundamentalLattice (Rsmall.profile.indexEquiv I).1 ≤
        Rlarge.jordan.fundamentalLattice (Rlarge.profile.indexEquiv I).1 := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan)
      (Rsmall.profile.indexEquiv I).1 (Rlarge.profile.indexEquiv I).1
      hscale hbound
  exact BONG.order_add_alphaValue_le_of_fundamentalLattice_le
    a b Rlarge.profile Rsmall.profile i Rlarge.internal hfundamental

/-- Collision-safe one-step specialization used in case 2. -/
theorem weakAligned_alphaValue_le_one_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    a.alphaValue i ≤ 1 := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex =
        JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ = a.order I + 1 := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 :=
        congrArg (fun z : Int ↦ z + 1) hsourceLocal
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_succ
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective := by
    rw [← htargetOrderLocal, hcurrent, hsourceOrderLocal]
    omega
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact congrFun (D.almostJordan_componentRank_eq hselected) p
  have hweakInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hlargeLe : (x.indexEquiv I).1 ≤ D.largeSelectedPosition :=
    hbefore.le
  have hsmallLe : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ ≤ D.largeSelectedPosition := hlargeLe
      _ = D.smallSelectedPosition := hselected.symm
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe (Or.inl (by simpa only [p, localIndex] using hweakInternal))
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hscales := D.weakAligned_fundamentalScale_interval
    hselected a b I (Or.inl hbefore)
  change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K D.input.block.enlargedScaleGenerator at hscales
  have hscale : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      Rsmall.jordan.fundamentalScaleOrder
        (Rsmall.profile.indexEquiv I).1 := by
    rw [Rlarge.scaleOrder_eq, Rsmall.scaleOrder_eq]
    exact hscales.1
  have hbound : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    rw [Rlarge.scaleOrder_eq]
    exact hscales.2
  have hfundamental :
      Rsmall.jordan.fundamentalLattice (Rsmall.profile.indexEquiv I).1 ≤
        Rlarge.jordan.fundamentalLattice (Rlarge.profile.indexEquiv I).1 := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan)
      (Rsmall.profile.indexEquiv I).1 (Rlarge.profile.indexEquiv I).1
      hscale hbound
  have hsourceGeneratorOrder :
      ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) = a.order I := by
    have hgen := Rlarge.jordan.fundamentalNormGenerator_order_eq_effective
      (Rlarge.profile.indexEquiv I).1
    change ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rlarge.jordan
        (Rlarge.profile.indexEquiv I).1
        (Rlarge.jordan.fundamentalScaleOrder
          (Rlarge.profile.indexEquiv I).1) at hgen
    rw [Rlarge.scaleOrder_eq, Rlarge.effectiveNormOrder_eq] at hgen
    exact hgen.trans hsourceOrderLocal.symm
  have htargetGeneratorOrder :
      ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) = b.order I := by
    have hgen := Rsmall.jordan.fundamentalNormGenerator_order_eq_effective
      (Rsmall.profile.indexEquiv I).1
    change ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rsmall.jordan
        (Rsmall.profile.indexEquiv I).1
        (Rsmall.jordan.fundamentalScaleOrder
          (Rsmall.profile.indexEquiv I).1) at hgen
    rw [Rsmall.scaleOrder_eq, Rsmall.effectiveNormOrder_eq] at hgen
    exact hgen.trans htargetOrderLocal.symm
  exact BONG.alphaValue_le_one_of_fundamentalLattice_le_current_succ
    a b Rlarge.profile Rsmall.profile i Rlarge.internal hfundamental
      hsourceGeneratorOrder htargetGeneratorOrder hcurrent

/-- Collision-safe two-step rigidity in case 1(b). -/
theorem weakAligned_source_twoStep_eq_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := rfl
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt
          (x.indexEquiv I).1 scale = sourceEffective := rfl
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := hscaleTarget
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt
          (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator
              (y.indexEquiv I).1)) = targetEffective := rfl
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact congrFun (D.almostJordan_componentRank_eq hselected) p
  have hsourceInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have htargetInternal : (y.indexEquiv I).2.val + 1 <
      finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hlocal, ← hrankEq]
    exact hsourceInternal
  have hglobalNext : i.val + 1 < n + 2 := by omega
  have hoddNext : ¬Even (localIndex + 1) := by
    intro h
    exact (Nat.even_add_one.mp h) heven
  have hsourceNext :
      a.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - sourceEffective := by
    have h := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hglobalNext hsourceInternal
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    change a.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_odd_of_scale_le
      hsourceScale hoddNext] at h
    exact h
  have htargetNext :
      b.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - targetEffective := by
    have h := y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hglobalNext htargetInternal
    simp only [BONG.weakJordanExpectedOrder] at h
    simp only [I] at h
    rw [htargetScaleAt] at h
    have htargetEffectiveScale :
        D.smallAlmostJordan.effectiveNormOrderAt
            (y.indexEquiv I).1 scale = targetEffective := by
      rw [← htargetScaleAt]
    rw [htargetEffectiveScale] at h
    have hlocalNext : (y.indexEquiv I).2.val + 1 =
        localIndex + 1 := by omega
    change b.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val + 1) at h
    rw [hlocalNext, JordanProfileOrder.localOrder_odd_of_scale_le
      htargetScale hoddNext] at h
    exact h
  have hnextReverse :
      b.order ⟨i.val + 1, hglobalNext⟩ <
        a.order ⟨i.val + 1, hglobalNext⟩ := by
    rw [hsourceNext, htargetNext]
    have heffectiveStrict : sourceEffective < targetEffective := by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent
    omega
  rcases (D.weakAligned_coordinate hselected a b
      (i.val + 1) hglobalNext).compare with hdirect |
        ⟨_hpositive, htwo, hpair⟩
  · have : False := by
      change a.order ⟨i.val + 1, hglobalNext⟩ ≤
        b.order ⟨i.val + 1, hglobalNext⟩ at hdirect
      exact (not_le_of_gt hnextReverse) hdirect
    contradiction
  · refine ⟨by omega, ?_⟩
    have htwoLe : a.order ⟨i.val + 2, by omega⟩ ≤ a.order I := by
      have hpair' : a.order ⟨i.val + 1, hglobalNext⟩ +
            a.order ⟨i.val + 2, by omega⟩ ≤
          b.order ⟨i.val, by omega⟩ +
            b.order ⟨i.val + 1, hglobalNext⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at,
          show i.val + 1 - 1 = i.val by omega,
          show i.val + 1 + 1 = i.val + 2 by omega] using hpair
      have hcurrentTarget : b.order ⟨i.val, by omega⟩ =
          targetEffective := by
        have hindex : (⟨i.val, by omega⟩ : Fin (n + 2)) = I := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact htargetOrderLocal
      rw [hsourceNext, htargetNext, hcurrentTarget] at hpair'
      rw [hsourceOrderLocal]
      omega
    apply le_antisymm
    · have htwoI : I.val + 2 < n + 2 := by
        change i.val + 2 < n + 2
        omega
      exact a.good I htwoI
    · exact htwoLe

theorem weakAligned_source_twoStep_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ :=
  D.weakAligned_source_twoStep_eq_before_selected_of_current_lt
    hselected a b i hbefore (by omega)

/-- A strict rise at the current comparison coordinate forces the next
global coordinate to stay in the same common weak component. -/
theorem weakAligned_next_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  let I : Fin (n + 2) := g.castSucc
  let J : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = I := by
    apply Fin.ext
    rfl
  have hcurrentI : a.order I < b.order I := by
    rw [← hpreviousIndex]
    exact hcurrent
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrentI
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrentI)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact congrFun (D.almostJordan_componentRank_eq hselected) p
  have hsourceInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hglobal : I.val + 1 < n + 2 :=
    x.global_succ_lt_of_local_succ I (by
      simpa only [p, localIndex] using hsourceInternal)
  have hnextPair :
      x.indexEquiv ⟨I.val + 1, hglobal⟩ =
        ⟨p, ⟨localIndex + 1, by
          simpa only [p, localIndex] using hsourceInternal⟩⟩ := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2
        (by simpa only [p, localIndex] using hsourceInternal)
    have hcurrentInverse : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hindex : (⟨I.val + 1, hglobal⟩ : Fin (n + 2)) =
        x.indexEquiv.symm
          ⟨p, ⟨localIndex + 1, by
            simpa only [p, localIndex] using hsourceInternal⟩⟩ := by
      apply Fin.ext
      calc
        I.val + 1 = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          rw [hcurrentInverse]
        _ = (x.indexEquiv.symm
            ⟨p, ⟨localIndex + 1, by
              simpa only [p, localIndex] using hsourceInternal⟩⟩).val := by
          simpa only [p, localIndex] using hval.symm
    rw [hindex, x.indexEquiv.apply_symm_apply]
  have hJ : J = ⟨I.val + 1, hglobal⟩ := by
    apply Fin.ext
    simp only [J, I, g, BONG.GoodBONG.representationAlphaIndex,
      Fin.val_castSucc]
    have := i.pos
    omega
  change (x.indexEquiv J).1 < D.largeSelectedPosition
  rw [hJ, hnextPair]
  exact hbefore

theorem weakAligned_commonBound_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentG : a.order g.castSucc < b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hcurrent
  obtain ⟨htwo, houterRaw⟩ :=
    D.weakAligned_source_twoStep_eq_before_selected_of_current_lt
      hselected a b g hbefore hcurrentG
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    omega
  have hrightIndex :
      (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
        ⟨i.val + 1, hnext⟩ := by
    apply Fin.ext
    change g.val + 2 = i.val + 1
    simp only [g, BONG.GoodBONG.representationAlphaIndex]
    have := i.pos
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := congrArg a.order hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ :=
        congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  push_cast at hcandidate hrecurrence
  have hupper : a.representationAlphaValue b i ≤
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
        a.alphaValue g := by
    calc
      a.representationAlphaValue b i ≤
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
            (b.order ⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue ⟨i.val, by omega⟩ := hcandidate
      _ = (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue g := by linarith [hrecurrence]
  have hweight :=
    D.weakAligned_order_add_alphaValue_le_before_selected_of_current_lt
      hselected a b g hbefore hcurrentG
  have hcurrentQ :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) <
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcurrent
  have hweightCanonical :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue g ≤
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          b.alphaValue g := by
    simpa only [← hpreviousIndex] using hweight
  have hsource : a.representationAlphaValue b i ≤ a.alphaValue g := by
    linarith
  have htarget : a.representationAlphaValue b i ≤ b.alphaValue g := by
    linarith
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsource
  · exact_mod_cast htarget

theorem weakAligned_commonCertificate_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrentLt : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  have hrightBefore :=
    D.weakAligned_next_before_selected_of_current_lt
      hselected a b i hbefore hcurrentLt
  obtain ⟨X, hsource, htarget⟩ :=
    D.weakAligned_commonApproximation_before_selected
      hselected a b i hrightBefore hnotSucc
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
      (D.weakAligned_commonBound_before_selected_of_current_lt
        hselected a b i hbefore hcurrentLt)

theorem weakAligned_representationAlphaValue_le_zero_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.representationAlphaValue b i ≤ 0 := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentOrder : b.order g.castSucc = a.order g.castSucc + 1 := by
    have h := hcurrent
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hprevious,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hprevious] at h
    simp only [BONG.GoodBONG.orderSequence_at] at h
    rw [← hpreviousIndex]
    exact h
  have halpha : a.alphaValue g ≤ 1 :=
    D.weakAligned_alphaValue_le_one_before_selected
      hselected a b g hbefore hcurrentOrder
  obtain ⟨htwo, houterRaw⟩ :=
    D.weakAligned_source_twoStep_eq_before_selected
      hselected a b g hbefore hcurrentOrder
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    have hrightIndex :
        (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      change g.val + 2 = i.val + 1
      simp only [g, BONG.GoodBONG.representationAlphaIndex]
      have := i.pos
      omega
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := congrArg a.order hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ :=
        congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  have hcurrentCanonical : b.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
    calc
      b.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          b.order g.castSucc := congrArg b.order hpreviousIndex
      _ = a.order g.castSucc + 1 := hcurrentOrder
      _ = a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
        rw [← congrArg a.order hpreviousIndex]
  have hcurrentCanonicalQ :
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) =
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) + 1 := by
    exact_mod_cast hcurrentCanonical
  push_cast at hcandidate hrecurrence
  calc
    a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ := hcandidate
    _ = ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩) - 1 := by
      rw [hcurrentCanonicalQ]
      ring
    _ = a.alphaValue g - 1 := by rw [hrecurrence]
    _ ≤ 0 := by linarith

theorem weakAligned_oddCertificate_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.odd
  · have hstart :=
      D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
    change D.largeSelectedStart = D.smallSelectedStart at hstart
    have hiDefect : D.DefectReducedRange i := by
      change i.val ≤ D.largeSelectedStart +
        finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
        at hi
      change i.val ≤ D.smallSelectedStart +
        finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      rw [D.largeAlmostJordan_finrank_selected] at hi
      rw [D.smallAlmostJordan_finrank_selected, ← hstart]
      exact hi
    have hprevious :=
      D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
        a b i hiDefect hcurrent
    have hipos := i.pos
    rw [show i.val = (i.val - 1) + 1 by omega,
      b.orderSequence.prefixSum_succ,
      a.orderSequence.prefixSum_succ, ← hprevious, hcurrent]
    abel
  · rw [← a.coe_representationAlphaValue b i]
    exact_mod_cast
      D.weakAligned_representationAlphaValue_le_zero_before_selected
        hselected a b i hbefore hcurrent

theorem weakAligned_representationAlphaValue_le_targetAlpha_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    a.representationAlphaValue b i ≤
      b.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  rcases (D.weakAligned_coordinate hselected a b
      g.val g.castSucc.isLt).compare with hdirect | hpairData
  · have hdirect' : a.order g.castSucc ≤ b.order g.castSucc := by
      have hraw : a.order ⟨g.val, g.castSucc.isLt⟩ ≤
          b.order ⟨g.val, g.castSucc.isLt⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at] using hdirect
      have hindex : (⟨g.val, g.castSucc.isLt⟩ : Fin (n + 2)) =
          g.castSucc := by
        apply Fin.ext
        rfl
      rw [hindex] at hraw
      exact hraw
    omega
  · obtain ⟨hpositive, hnext, hpair⟩ := hpairData
    have hiPrevious : 1 < i.val := by
      change 0 < i.val - 1 at hpositive
      omega
    let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    have hpreviousLe : previousAlpha ≤ g := by
      change i.val - 2 ≤ i.val - 1
      omega
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousLe
    change (b.order previousAlpha.castSucc : ℚ) +
        b.alphaValue previousAlpha ≤
      (b.order g.castSucc : ℚ) + b.alphaValue g at hendpoint
    have hcandidate :=
      a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
    have hnextIndex :
        (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hpreviousIndex :
        (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
          previousAlpha.castSucc := by
      apply Fin.ext
      change (i.val - 1) - 1 = i.val - 2
      omega
    have hpairRaw :
        a.order ⟨g.val, g.castSucc.isLt⟩ +
            a.order ⟨g.val + 1, hnext⟩ ≤
          b.order ⟨g.val - 1, by omega⟩ +
            b.order ⟨g.val, g.castSucc.isLt⟩ := by
      simpa only [BONG.GoodBONG.orderSequence_at] using hpair
    have hpairQ :
        (a.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) +
            (a.order ⟨g.val + 1, hnext⟩ : ℚ) ≤
          (b.order ⟨g.val - 1, by omega⟩ : ℚ) +
            (b.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) := by
      exact_mod_cast hpairRaw
    have hsourceCurrentValue :
        a.order ⟨g.val, g.castSucc.isLt⟩ = a.order g.castSucc := by
      apply congrArg a.order
      apply Fin.ext
      rfl
    have htargetCurrentValue :
        b.order ⟨g.val, g.castSucc.isLt⟩ = b.order g.castSucc := by
      apply congrArg b.order
      apply Fin.ext
      rfl
    have hsourceNextValue :
        a.order ⟨g.val + 1, hnext⟩ =
          a.order ⟨i.val, i.lt_large⟩ := congrArg a.order hnextIndex
    have htargetPreviousValue :
        b.order ⟨g.val - 1, by omega⟩ =
          b.order previousAlpha.castSucc := congrArg b.order hpreviousIndex
    have hcandidate' : a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
      have hcurrentMathIndex :
          (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
            g.castSucc := by
        apply Fin.ext
        rfl
      have hpreviousAlphaIndex :
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
            previousAlpha := by
        apply Fin.ext
        rfl
      push_cast at hcandidate
      rw [hcurrentMathIndex, hpreviousAlphaIndex] at hcandidate
      exact hcandidate
    have hcurrentQ : (b.order g.castSucc : ℚ) <
        (a.order g.castSucc : ℚ) := by
      exact_mod_cast hcurrent
    rw [hsourceCurrentValue, htargetCurrentValue,
      hsourceNextValue, htargetPreviousValue] at hpairQ
    linarith

theorem weakAligned_source_previous_twoStep_eq_before_selected_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    ∃ (hpos : 0 < i.val) (hnext : i.val + 1 < n + 2),
      a.order ⟨i.val - 1, by omega⟩ =
        a.order ⟨i.val + 1, hnext⟩ ∧
      a.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ ∧
      (a.order i.castSucc = b.order i.castSucc + 1 ∨
        a.order i.castSucc = b.order i.castSucc + 2) ∧
      b.order ⟨i.val - 1, by omega⟩ -
          a.order ⟨i.val - 1, by omega⟩ =
        a.order i.castSucc - b.order i.castSucc ∧
      Even (a.order ⟨i.val - 1, by omega⟩ + a.order i.castSucc) ∧
      Even (a.orderGap i) ∧
      a.orderGap i < 2 * (ramificationIndex K : Int) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have heffectiveUpper : targetEffective ≤ sourceEffective + 2 := by
    have hupper := (D.common_effectiveNormOrder_bounds p hbefore).2
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2
    rw [← hrp, ← hscaleRaw]
    exact hupper
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have htargetCeiling :
      targetEffective ≤ scale + (ramificationIndex K : Int) := by
    have h :=
      D.smallAlmostJordan.effectiveNormOrderAt_scale_le_scale_add_ramificationIndex r
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) +
        (ramificationIndex K : Int) at h
    simpa only [targetEffective, hscaleTarget] using h
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap :
      targetEffective = sourceEffective + 1 ∨
        targetEffective = sourceEffective + 2 := by
    have hstrict : sourceEffective < targetEffective := by
      rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd,
        JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
        at hlocalCurrent
      omega
    omega
  have hcurrentGap :
      a.order I = b.order I + 1 ∨ a.order I = b.order I + 2 := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    rcases heffectiveGap with hgap | hgap
    · left
      omega
    · right
      omega
  have hlocalPos : 0 < localIndex := by
    by_contra h
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  have hglobalPos : 0 < i.val := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change I.val = _ + localIndex at hindex
    change 0 < I.val
    omega
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hpreviousCast : previous.castSucc =
      x.indexEquiv.symm
        ⟨p, ⟨localIndex - 1, by
          change localIndex - 1 <
            finrank K (D.largeAlmostJordan.component p).carrier
          have := (x.indexEquiv I).2.isLt
          change localIndex <
            finrank K (D.largeAlmostJordan.component p).carrier at this
          omega⟩⟩ := by
    have hpredVal := x.inverse_index_val_local_pred
      p (x.indexEquiv I).2 (by simpa only [localIndex] using hlocalPos)
    have hcurrentInverse : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    apply Fin.ext
    change i.val - 1 = _
    have hpredVal' :
        (x.indexEquiv.symm
          ⟨p, ⟨localIndex - 1, by
            change localIndex - 1 <
              finrank K (D.largeAlmostJordan.component p).carrier
            have := (x.indexEquiv I).2.isLt
            change localIndex <
              finrank K (D.largeAlmostJordan.component p).carrier at this
            omega⟩⟩).val + 1 = I.val := by
      simpa only [p, localIndex] using
        hpredVal.trans (congrArg Fin.val hcurrentInverse)
    have hIval : I.val = i.val := rfl
    rw [hIval] at hpredVal'
    omega
  have hpreviousComponent : (x.indexEquiv previous.castSucc).1 = p := by
    rw [hpreviousCast, x.indexEquiv.apply_symm_apply]
  have hpreviousBefore :
      (x.indexEquiv previous.castSucc).1 < D.largeSelectedPosition := by
    rw [hpreviousComponent]
    exact hbefore
  have hevenPrevious : Even (localIndex - 1) := by
    rcases Nat.not_even_iff_odd.mp hodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hsourcePrevious : a.order previous.castSucc = sourceEffective := by
    have h := x.order_pred_eq_weakJordanExpectedOrder_of_local_pred I
      (by simpa only [localIndex] using hlocalPos)
    simp only [BONG.weakJordanExpectedOrder] at h
    change a.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex - 1) at h
    rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsourceScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have htargetPrevious : b.order previous.castSucc = targetEffective := by
    have htargetPos : 0 < (y.indexEquiv I).2.val := by
      rw [← hlocal]
      exact hlocalPos
    have h := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred I htargetPos
    simp only [BONG.weakJordanExpectedOrder] at h
    change b.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
          ((y.indexEquiv I).2.val - 1) at h
    have hprevLocal : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by
      omega
    rw [hscaleTarget, hprevLocal,
      JordanProfileOrder.localOrder_even_of_scale_le
        htargetScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have heffectiveStrict : sourceEffective < targetEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
      at hcurrent
    omega
  have hpreviousStrict :
      a.order previous.castSucc < b.order previous.castSucc := by
    rw [hsourcePrevious, htargetPrevious]
    exact heffectiveStrict
  have hgapEquality :
      b.order previous.castSucc - a.order previous.castSucc =
        a.order I - b.order I := by
    rw [hsourcePrevious, htargetPrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    ring
  have hevenPair : Even (a.order previous.castSucc + a.order I) := by
    refine ⟨scale, ?_⟩
    rw [hsourcePrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    omega
  obtain ⟨htwo, htwoEq⟩ :=
    D.weakAligned_source_twoStep_eq_before_selected_of_current_lt
      hselected a b previous hpreviousBefore hpreviousStrict
  have hnext : i.val + 1 < n + 2 := by
    change previous.val + 2 < n + 2 at htwo
    dsimp only [previous] at htwo
    omega
  have hrightGap :
      (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) = i.succ := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hleftGap : previous.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htwoGap :
      a.order ⟨i.val - 1, by omega⟩ = a.order i.succ := by
    rw [← hleftGap, ← hrightGap]
    exact htwoEq
  have hnextEffective : a.order i.succ = sourceEffective := by
    calc
      a.order i.succ = a.order ⟨i.val - 1, by omega⟩ := htwoGap.symm
      _ = a.order previous.castSucc := by rw [hleftGap]
      _ = sourceEffective := hsourcePrevious
  have hgapFormula : a.orderGap i = 2 * (sourceEffective - scale) := by
    unfold BONG.GoodBONG.orderGap
    rw [hnextEffective, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    ring
  have hgapEven : Even (a.orderGap i) := by
    refine ⟨sourceEffective - scale, ?_⟩
    rw [hgapFormula]
    ring
  have hgapLt : a.orderGap i < 2 * (ramificationIndex K : Int) := by
    have hsourceCeiling :
        sourceEffective < scale + (ramificationIndex K : Int) :=
      heffectiveStrict.trans_le htargetCeiling
    rw [hgapFormula]
    omega
  refine ⟨hglobalPos, hnext, ?_, ?_, ?_, ?_, ?_, hgapEven, hgapLt⟩
  · have hright :
        (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      dsimp only [previous]
      omega
    have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft, hright] at htwoEq
    exact htwoEq
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hpreviousStrict
    exact hpreviousStrict
  · exact hcurrentGap
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hgapEquality
    exact hgapEquality
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hevenPair
    exact hevenPair

theorem weakAligned_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 1 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.weakAligned_source_previous_twoStep_eq_before_selected_of_current_gt
      hselected a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  have hpreviousCurrent :
      b.order ⟨g.val - 1, by omega⟩ =
        a.order ⟨g.val - 1, by omega⟩ + 1 := by
    omega
  have hjpos : 0 < i.val - 1 := by omega
  have hjlt : i.val - 1 < n + 2 :=
    (Nat.sub_le _ _).trans_lt i.lt_large
  have hjle : i.val - 1 ≤ n + 2 := hjlt.le
  let j : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, hjpos, hjlt, hjle⟩
  have hj : D.Lemma517Range j := by
    change j.val ≤ D.lemma517Cutoff
    change i.val ≤ D.lemma517Cutoff at hi
    dsimp only [j]
    omega
  have hentryIndex :
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 2)) =
        ⟨g.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hpreviousEntry :
      b.orderSequence.entryOrZero (j.val - 1) =
        a.orderSequence.entryOrZero (j.val - 1) + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := j.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := j.lt_large; omega),
      BONG.GoodBONG.orderSequence_at, BONG.GoodBONG.orderSequence_at,
      hentryIndex]
    exact hpreviousCurrent
  have hstart :=
    D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
  change D.largeSelectedStart = D.smallSelectedStart at hstart
  have hjDefect : D.DefectReducedRange j := by
    change j.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hj
    change j.val ≤ D.smallSelectedStart +
      finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
    rw [D.largeAlmostJordan_finrank_selected] at hj
    rw [D.smallAlmostJordan_finrank_selected, ← hstart]
    exact hj
  have hpreviousSum :=
    D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
      a b j hjDefect hpreviousEntry
  have hprefixOddRaw :=
    a.comparisonPrefixProduct_order_odd_of_previous_prefix_eq b
      j.val j.pos j.lt_large.le j.lt_large.le hpreviousSum hpreviousEntry
  have hprefixOdd : Odd (ordUnit K
      (a.prefixProduct (i.val - 1) * b.prefixProduct (i.val - 1))) := by
    simpa only [j] using hprefixOddRaw
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentIndex : g.castSucc =
      (⟨i.val - 1, hjlt⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hevenCurrentNext : Even
      (a.order ⟨i.val - 1, hjlt⟩ +
        a.order ⟨i.val, i.lt_large⟩) := by
    have hpair := hevenPair
    rw [htwo, hnextIndex, hcurrentIndex] at hpair
    simpa only [add_comm] using hpair
  have hshiftOdd :=
    a.shiftedPrimaryProduct_odd_of_previousPrefix_odd_of_sourcePair_even
      b i hiPrevious hprefixOdd hevenCurrentNext
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b
    (-1) (i.val + 1) (i.val - 1) hshiftOdd
  have hcandidate :=
    a.representationAlphaValue_le_primaryCoefficient_of_defect_zero b i hzero
  have halphaLower :=
    a.orderGap_add_one_le_alphaValue_of_even_of_lt_twoE g hgapEven hgapLt
  have hnextGapIndex : g.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentGapIndex : g.castSucc =
      (⟨i.val - 1, hjlt⟩ : Fin (n + 2)) := hcurrentIndex
  push_cast at hcandidate
  push_cast at halphaLower
  unfold BONG.GoodBONG.orderGap at halphaLower
  rw [hnextGapIndex, hcurrentGapIndex] at halphaLower
  push_cast at halphaLower
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 1 := by
    exact_mod_cast hcurrent
  rw [hcurrentGapIndex] at hcurrentQ
  linarith

/-- Collision-safe source-alpha bound in the reverse gap-two branch. -/
theorem weakAligned_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 2 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.weakAligned_source_previous_twoStep_eq_before_selected_of_current_gt
      hselected a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hpreviousLe : previousAlpha ≤ g := by
    change i.val - 2 ≤ i.val - 1
    omega
  have hendpoint := a.alphaLeftEndpoint_monotone hpreviousLe
  change (a.order previousAlpha.castSucc : ℚ) +
      a.alphaValue previousAlpha ≤
    (a.order g.castSucc : ℚ) + a.alphaValue g at hendpoint
  have hweightData :=
    D.weakAligned_previous_order_add_alpha_eq_of_current_eq_target_add_two
      hselected a b g hbefore hcurrent
  rcases hweightData with ⟨_, hweightSum⟩
  have hpreviousAlphaIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 1)) = previousAlpha := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  rw [hpreviousAlphaIndex] at hweightSum
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hpreviousIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
        previousAlpha.castSucc := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  have htwoNormalized :
      a.order previousAlpha.castSucc =
        a.order ⟨i.val, i.lt_large⟩ := by
    rw [← hpreviousIndex, ← hnextIndex]
    exact htwo
  have hgapNormalized :
      b.order previousAlpha.castSucc - a.order previousAlpha.castSucc =
        a.order g.castSucc - b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hgapEquality
  have hcandidate :=
    a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
  have hcurrentMathIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
        g.castSucc := by
    apply Fin.ext
    rfl
  have hcandidate' : a.representationAlphaValue b i ≤
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
        (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
    push_cast at hcandidate
    rw [hcurrentMathIndex,
      show (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
        previousAlpha by rfl] at hcandidate
    exact hcandidate
  have htwoQ :
      (a.order previousAlpha.castSucc : ℚ) =
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast htwoNormalized
  have hgapQ :
      (b.order previousAlpha.castSucc : ℚ) -
          (a.order previousAlpha.castSucc : ℚ) =
        (a.order g.castSucc : ℚ) - (b.order g.castSucc : ℚ) := by
    exact_mod_cast hgapNormalized
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 2 := by
    exact_mod_cast hcurrent
  linarith

/-- Complete collision-safe alpha-cap estimate in the reverse strict-order
branch before the selected component. -/
theorem weakAligned_commonBound_before_selected_of_current_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  have hcases :=
    D.weakAligned_source_previous_twoStep_eq_before_selected_of_current_gt
      hselected a b g hbefore hcurrent
  rcases hcases with
    ⟨_hpos, _hnext, _htwo, _hpreviousStrict, hcurrentCases,
      _hgapEquality, _hevenPair, _hgapEven, _hgapLt⟩
  have hsourceBound : a.representationAlphaValue b i ≤
      a.alphaValue g := by
    rcases hcurrentCases with hgapOne | hgapTwo
    · exact D.weakAligned_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
        hselected a b i hi hbefore hgapOne
    · exact D.weakAligned_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
        hselected a b i hbefore hgapTwo
  have htargetBound : a.representationAlphaValue b i ≤
      b.alphaValue g :=
    D.weakAligned_representationAlphaValue_le_targetAlpha_of_current_gt
      hselected a b i hcurrent
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsourceBound
  · exact_mod_cast htargetBound

/-- Any common approximation at the right boundary, together with the
collision-safe reverse-order bound, yields the Section 5 defect
certificate. -/
theorem weakAligned_commonCertificate_before_selected_of_current_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc)
    (happrox : ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  obtain ⟨X, hsource, htarget⟩ := happrox
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
      (D.weakAligned_commonBound_before_selected_of_current_gt
        hselected a b i hi hbefore hcurrent)

/-- Without a large-side scale collision, every large coordinate resolution
has zero left offset, including a coordinate in the selected block. -/
theorem largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_noCollision
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition) :
    (D.largeStrictCoordinateResolution a I hle).localCoordinateOffset = 0 := by
  classical
  simp only [largeStrictCoordinateResolution]
  split
  · next hcollision => exact (hlarge hcollision).elim
  · rfl

/-- If the large family is already strict, the determinant seeds of the
two resolved selected blocks differ by a square even when the small selected
block is amalgamated with its equal-scale right neighbour. -/
theorem strictResolution_determinantSeeds_square_at_boundary_of_noLargeCollision
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition)
    (hsmallPosition : ((D.smallWeakProfileWitness b).indexEquiv I).1 =
      D.largeSelectedPosition)
    (hsmallBound : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition)
    (hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j) :
    let hlargeLe : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
        D.largeSelectedPosition := hposition.le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallBound
    ∃ s : Kˣ,
      Rsmall.determinantSeedData.leftDet =
        Rlarge.determinantSeedData.leftDet * s ^ 2 := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let hlargeLe := hposition.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBound
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_noCollision
      hlarge a I hlargeLe
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallBound
  have hcomponentLarge : Rlarge.component.val = (x.indexEquiv I).1.val :=
    Rlarge.component_val_eq_of_offset_zero hoffLarge
  have hcomponentSmall : Rsmall.component.val = (y.indexEquiv I).1.val :=
    Rsmall.component_val_eq_of_offset_zero hoffSmall
  have hcomponentVal : Rlarge.component.val = Rsmall.component.val :=
    hcomponentLarge.trans <|
      (congrArg Fin.val hposition).trans <|
        (congrArg Fin.val hsmallPosition).symm.trans hcomponentSmall.symm
  by_cases hpzero : Rlarge.component.val = 0
  · have hsmallZero : Rsmall.component.val = 0 :=
      hcomponentVal.symm.trans hpzero
    refine ⟨1, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_zero hsmallZero,
      Rlarge.determinantSeedData_leftDet_of_component_zero hpzero]
    simp
  · let cut := Rlarge.component.val
    let P := Rlarge.jordan.toOrthogonalDecomposition
    let Q := Rsmall.jordan.toOrthogonalDecomposition
    have hcut : cut - 1 + 1 = cut := by
      dsimp only [cut]
      omega
    have hP : cut - 1 + 1 ≤ Rlarge.componentCount := by
      rw [hcut]
      exact Rlarge.component.isLt.le
    have hQ : cut - 1 + 1 ≤ Rsmall.componentCount := by
      rw [hcut]
      have hsmallLt := Rsmall.component.isLt
      omega
    have hprefixComponent (z : Fin (cut - 1 + 1)) :
        P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
          Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
      let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
      let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
      have hjPVal : jP.val = z.val :=
        P.prefixIndexEquiv_val (cut - 1 + 1) hP z
      have hjQVal : jQ.val = z.val :=
        Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
      have hzCut : z.val < cut := by
        have hz := z.isLt
        omega
      have hjP : jP < Rlarge.component := by
        change jP.val < Rlarge.component.val
        dsimp only [cut] at hzCut
        omega
      have hjQ : jQ < Rsmall.component := by
        change jQ.val < Rsmall.component.val
        omega
      obtain ⟨oldP, holdPVal, holdP⟩ :=
        Rlarge.prefixComponent_eq jP hjP
      obtain ⟨oldQ, holdQVal, holdQ⟩ :=
        Rsmall.prefixComponent_eq jQ hjQ
      have holdEq : oldP = oldQ := by
        apply Fin.ext
        rw [holdPVal, holdQVal, hjPVal, hjQVal]
      have holdPBefore : oldP < D.largeSelectedPosition := by
        change oldP.val < D.largeSelectedPosition.val
        calc
          oldP.val = jP.val := holdPVal
          _ < Rlarge.component.val := hjP
          _ = (x.indexEquiv I).1.val := hcomponentLarge
          _ = D.largeSelectedPosition.val := congrArg Fin.val hposition
      change Rlarge.strictWeak.component jP =
        Rsmall.strictWeak.component jQ
      rw [holdP, holdQ, ← holdEq]
      exact hcomponent oldP holdPBefore
    have hsquare :=
      P.exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry_of_differentCounts
        Q hP hQ (fun z ↦ by
          rw [hprefixComponent z]
          exact Lattice.Isometry.refl _ _)
    rcases hsquare with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_ne_zero (by omega),
      Rlarge.determinantSeedData_leftDet_of_component_ne_zero hpzero]
    change
      (Q.prefixQuadraticSublattice Rsmall.component.val).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice Rlarge.component.val).refinedDeterminantUnit *
          s ^ 2
    rw [← hcomponentVal]
    simpa only [hcut] using hs

/-- Aligned specialization of the boundary determinant-seed transport. -/
theorem weakAligned_strictResolution_determinantSeeds_square_at_selected_of_noLargeCollision
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition) :
    let hlargeLe : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
        D.largeSelectedPosition := hposition.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
      rw [hselected, ← hcoordinates.1]
      exact hposition.le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    ∃ s : Kˣ,
      Rsmall.determinantSeedData.leftDet =
        Rlarge.determinantSeedData.leftDet * s ^ 2 := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 = D.largeSelectedPosition :=
    hcoordinates.1.symm.trans hposition
  have hsmallBound : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    rw [hsmallPosition, hselected]
  have hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j := by
    intro j hj
    exact D.aligned_component_eq hselected j (ne_of_lt hj)
  simpa only [x, y] using
    D.strictResolution_determinantSeeds_square_at_boundary_of_noLargeCollision
      hlarge a b I hposition hsmallPosition hsmallBound hcomponent

/-- Lemma 5.13(i) on the aligned selected block when the large side has no
scale collision.  The small side may have its selected block amalgamated
with an equal-scale right neighbour. -/
theorem noLargeCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hxPosition : (x.indexEquiv I).1 = D.largeSelectedPosition := by
    simpa only [x, I] using hposition
  have hsmallPosition : (y.indexEquiv I).1 =
      D.smallSelectedPosition := by
    rw [hselected, ← hcoordinates.1]
    exact hposition
  let hlargeLe := hposition.le
  let hsmallLe := hsmallPosition.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  let C := Rlarge.coordinates
  let E := Rsmall.coordinates
  let j := (Rlarge.profile.indexEquiv I).2.val
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_noCollision
      hlarge a I hlargeLe
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hlocalLarge : j = (x.indexEquiv I).2.val := by
    dsimp only [j]
    rw [Rlarge.localCoordinate_eq, hoffLarge, Nat.zero_add]
  have hlocalSmall : (Rsmall.profile.indexEquiv I).2.val = j := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add,
      ← hcoordinates.2, ← hlocalLarge]
  have hiStartLarge := Rlarge.index_val_eq_coordinates_start_add_local
  have hiStartSmall := Rsmall.index_val_eq_coordinates_start_add_local
  have hstart : C.start = E.start := by
    change I.val = C.start + j at hiStartLarge
    change I.val = E.start + (Rsmall.profile.indexEquiv I).2.val at hiStartSmall
    rw [hlocalSmall] at hiStartSmall
    omega
  have hiStart : i.val = C.start + j := by
    simpa only [I] using hiStartLarge
  have hiC : i.val < C.stop := by
    simpa only [I] using Rlarge.index_val_lt_coordinates_stop
  have hiE : i.val < E.stop := by
    simpa only [I] using Rsmall.index_val_lt_coordinates_stop
  let dLarge := Rlarge.determinantSeedData
  let dSmall := Rsmall.determinantSeedData
  have hdet : ∃ s : Kˣ,
      dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    simpa only [dLarge, dSmall] using
      D.weakAligned_strictResolution_determinantSeeds_square_at_selected_of_noLargeCollision
        hlarge hselected a b I hposition
  have hjBound : j < finrank K D.input.block.component.carrier := by
    calc
      j = (x.indexEquiv I).2.val := hlocalLarge
      _ < finrank K
          (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier :=
        (x.indexEquiv I).2.isLt
      _ = finrank K D.input.block.component.carrier := by
        rw [hxPosition, D.largeAlmostJordan_finrank_selected]
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := Rlarge.approximationSeedsWith dLarge
      Rlarge.fundamentalNormGenerator Rlarge.fundamentalNormGenerator_spec
    let T := Rsmall.approximationSeedsWith dSmall
      Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
    have hdet' : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2 := by
      simpa only [S, T,
        BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
          hdet
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet'
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    have hfin : finrank K D.input.block.component.carrier = 2 := by
      rcases D.rank_one_or_two with hOne | hTwo
      · rw [hOne] at hjBound
        omega
      · exact hTwo
    have hj : j = 1 := by
      rw [hfin] at hjBound
      omega
    have hweakLocal : (x.indexEquiv I).2.val = 1 := by
      rw [← hlocalLarge, hj]
    let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
    let targetSmall := ordUnit K D.input.block.scaleGenerator
    let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
      D.largeSelectedPosition targetLarge
    let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
      D.smallSelectedPosition targetSmall
    have heLargeSmall := D.largeSelected_effectiveNormOrder_le_smallSelected
    have heSmallLarge :=
      D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
        hfin
    change eLarge ≤ eSmall at heLargeSmall
    change eSmall ≤ eLarge + 2 at heSmallLarge
    have hnotOne : eSmall ≠ eLarge + 1 := by
      simpa only [eLarge, eSmall, targetLarge, targetSmall, x, I] using
        D.selectedBinary_effectiveNormOrder_ne_add_one_of_current_ne
          hselected hfin a b i hposition hweakLocal hcurrent
    have hcases : eLarge = eSmall ∨ eSmall = eLarge + 2 := by
      omega
    have hscaleLarge :
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component =
          targetLarge := by
      calc
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component =
            ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1) := Rlarge.scaleOrder_eq
        _ = targetLarge := by
          rw [hxPosition, D.largeAlmostJordan_scaleGenerator_selected]
    have hscaleSmall :
        Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
          targetSmall := by
      calc
        Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
            ordUnit K (D.smallAlmostJordan.scaleGenerator
              (y.indexEquiv I).1) := Rsmall.scaleOrder_eq
        _ = targetSmall := by
          rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_selected]
    have hscaleLe :
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component ≤
          Rsmall.jordan.fundamentalScaleOrder Rsmall.component := by
      rw [hscaleLarge, hscaleSmall]
      exact D.enlargedScaleOrder_lt_smallScaleOrder.le
    have hbound :
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component ≤
          ordUnit K D.input.block.enlargedScaleGenerator := by
      rw [hscaleLarge]
    have hinclude : Rsmall.fundamentalLattice ≤
        Rlarge.fundamentalLattice :=
      D.smallFundamentalLattice_le_large_of_scale_le
        Rsmall.component Rlarge.component hscaleLe hbound
    have hrescale : Lattice.rescale (uniformizerUnit K)
        Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
      rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
        Rsmall.fundamentalLattice_eq_scaleTruncation]
      change Lattice.rescale (uniformizerUnit K)
          (Lattice.scaleTruncation q M
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1))) ≤
        Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1))
      rw [hxPosition, hsmallPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected]
      exact D.rescale_largeFundamental_le_small_of_rank_two hfin
    rcases hcases with heq | htwo
    · have heffective :
          D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
              (ordUnit K (D.largeAlmostJordan.scaleGenerator
                (x.indexEquiv I).1)) =
            D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
              (ordUnit K (D.smallAlmostJordan.scaleGenerator
                (y.indexEquiv I).1)) := by
        simpa only [hxPosition, hsmallPosition,
          D.largeAlmostJordan_scaleGenerator_selected,
          D.smallAlmostJordan_scaleGenerator_selected,
          targetLarge, targetSmall, eLarge, eSmall] using heq
      obtain ⟨A, hALarge, hASmall⟩ :=
        Rlarge.exists_commonNormGenerator_of_effective_eq Rsmall
          hinclude heffective
      let S := Rlarge.approximationSeedsWith dLarge A hALarge
      let T := Rsmall.approximationSeedsWith dSmall A hASmall
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · have hpos : 0 < finrank K V := by
        rw [← a.toBONG.length_eq_finrank]
        omega
      have heffective :
          D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
              (ordUnit K (D.smallAlmostJordan.scaleGenerator
                (y.indexEquiv I).1)) =
            D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
                (ordUnit K (D.largeAlmostJordan.scaleGenerator
                  (x.indexEquiv I).1)) + 2 := by
        simpa only [hxPosition, hsmallPosition,
          D.largeAlmostJordan_scaleGenerator_selected,
          D.smallAlmostJordan_scaleGenerator_selected,
          targetLarge, targetSmall, eLarge, eSmall] using htwo
      have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
        hpos hrescale heffective
      let A := Rlarge.fundamentalNormGenerator
      let B := (uniformizerUnit K) ^ 2 * A
      let S := Rlarge.approximationSeedsWith dLarge A hpair.1
      let T := Rsmall.approximationSeedsWith dSmall B hpair.2
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

/-- Complete aligned Lemma 5.13 local data with arbitrary endpoint scale
collisions. -/
theorem weakAligned_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range := by
  by_cases hlarge : D.LargeScaleCollision
  · obtain ⟨c, hscale⟩ := hlarge
    exact D.largeCollision_aligned_lemma513LocalData
      hselected c hscale a b
  · refine
      { commonApproximation := ?_
        previousPrefixSum_eq := ?_ }
    · intro i hi hcurrent
      rcases D.weakAligned_reducedRange_right_coordinate a i hi with
        hbefore | hposition
      · exact D.weakAligned_commonApproximation_before_selected
          hselected a b i hbefore hcurrent
      · exact D.noLargeCollision_commonApproximation_at_selected
          hlarge hselected a b i hposition hcurrent
    · intro i hi hcurrent
      have hstart :=
        D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
      change D.largeSelectedStart = D.smallSelectedStart at hstart
      have hiDefect : D.DefectReducedRange i := by
        change i.val ≤ D.largeSelectedStart +
          finrank K
            (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
          at hi
        change i.val ≤ D.smallSelectedStart +
          finrank K
            (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
        rw [D.largeAlmostJordan_finrank_selected] at hi
        rw [D.smallAlmostJordan_finrank_selected, ← hstart]
        exact hi
      exact D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
        a b i hiDefect hcurrent

/-- Reaching the first local coordinate of the aligned selected block on
the literal Lemma 5.17 boundary forces that block to be binary.  In the
unary case the one-based boundary would already lie one step beyond the
cutoff. -/
theorem weakAligned_selected_rank_two_of_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    finrank K D.input.block.component.carrier = 2 := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  have hglobal := x.index_val_eq_componentStart_add_local I
  have hstart : i.val - 1 = D.largeSelectedStart := by
    change I.val = x.componentStart (x.indexEquiv I).1 +
      (x.indexEquiv I).2.val at hglobal
    calc
      i.val - 1 = I.val := rfl
      _ = x.componentStart (x.indexEquiv I).1 +
          (x.indexEquiv I).2.val := hglobal
      _ = x.componentStart (x.indexEquiv I).1 := by rw [hlocal, add_zero]
      _ = x.componentStart D.largeSelectedPosition :=
        congrArg x.componentStart hposition
      _ = D.largeSelectedStart := rfl
  change i.val ≤ D.largeSelectedStart +
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1 at hi
  rw [D.largeAlmostJordan_finrank_selected] at hi
  rcases D.rank_one_or_two with hOne | hTwo
  · rw [hOne] at hi
    have hipos := i.pos
    omega
  · exact hTwo

/-- Collision-safe form of the weight estimate at the first coordinate of
the aligned selected binary block.  Even if either weak component is
amalgamated with an equal-scale neighbour, that coordinate is internal in
a strict resolution.  Inclusion of the two fundamental lattices and a
one-step rise of their norm-generator orders therefore give `alpha <= 1`.
-/
theorem weakAligned_alphaValue_le_one_at_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 =
      D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).2.val = 0)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    a.alphaValue i ≤ 1 := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hp : p = D.largeSelectedPosition := hposition
  have hr : r = D.smallSelectedPosition := by
    calc
      r = p := hcoordinates.1.symm
      _ = D.largeSelectedPosition := hp
      _ = D.smallSelectedPosition := hselected.symm
  have hlocalIndex : localIndex = 0 := hlocal
  have htargetLocalIndex : (y.indexEquiv I).2.val = 0 :=
    hcoordinates.2.symm.trans hlocalIndex
  have heffective : sourceEffective ≤ targetEffective := by
    simpa only [sourceEffective, targetEffective, scale, hp, hr,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected] using
        D.largeSelected_effectiveNormOrder_le_smallSelected
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale (by
        refine ⟨0, ?_⟩
        simpa only [zero_add] using hlocal)]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocal,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale (by
        refine ⟨0, ?_⟩
        simpa only [zero_add] using htargetLocalIndex)]
  have hweakInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    rw [hp, D.largeAlmostJordan_finrank_selected, hfin, hlocalIndex]
    omega
  have hlargeLe : p ≤ D.largeSelectedPosition := hp.le
  have hsmallLe : r ≤ D.smallSelectedPosition := hr.le
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe (Or.inl (by
      simpa only [p, localIndex] using hweakInternal))
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hscales := D.weakAligned_fundamentalScale_interval
    hselected a b I (Or.inr ⟨hposition, hlocal⟩)
  change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K D.input.block.enlargedScaleGenerator at hscales
  have hscale : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      Rsmall.jordan.fundamentalScaleOrder
        (Rsmall.profile.indexEquiv I).1 := by
    rw [Rlarge.scaleOrder_eq, Rsmall.scaleOrder_eq]
    exact hscales.1
  have hbound : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    rw [Rlarge.scaleOrder_eq]
    exact hscales.2
  have hfundamental :
      Rsmall.jordan.fundamentalLattice (Rsmall.profile.indexEquiv I).1 ≤
        Rlarge.jordan.fundamentalLattice (Rlarge.profile.indexEquiv I).1 := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan)
      (Rsmall.profile.indexEquiv I).1 (Rlarge.profile.indexEquiv I).1
      hscale hbound
  have hsourceGeneratorOrder :
      ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) = a.order I := by
    have hgen := Rlarge.jordan.fundamentalNormGenerator_order_eq_effective
      (Rlarge.profile.indexEquiv I).1
    change ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rlarge.jordan
        (Rlarge.profile.indexEquiv I).1
        (Rlarge.jordan.fundamentalScaleOrder
          (Rlarge.profile.indexEquiv I).1) at hgen
    rw [Rlarge.scaleOrder_eq, Rlarge.effectiveNormOrder_eq] at hgen
    exact hgen.trans hsourceOrderLocal.symm
  have htargetGeneratorOrder :
      ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) = b.order I := by
    have hgen := Rsmall.jordan.fundamentalNormGenerator_order_eq_effective
      (Rsmall.profile.indexEquiv I).1
    change ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rsmall.jordan
        (Rsmall.profile.indexEquiv I).1
        (Rsmall.jordan.fundamentalScaleOrder
          (Rsmall.profile.indexEquiv I).1) at hgen
    rw [Rsmall.scaleOrder_eq, Rsmall.effectiveNormOrder_eq] at hgen
    exact hgen.trans htargetOrderLocal.symm
  exact BONG.alphaValue_le_one_of_fundamentalLattice_le_current_succ
    a b Rlarge.profile Rsmall.profile i Rlarge.internal hfundamental
      hsourceGeneratorOrder htargetGeneratorOrder hcurrent

/-- Complete condition-(ii) certificate whenever the comparison coordinate
immediately preceding the boundary lies strictly before the aligned selected
block, with arbitrary scale collisions. -/
theorem weakAligned_defectCertificate_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let localData := D.weakAligned_lemma513LocalData hselected a b
  by_cases hlt : a.order g.castSucc < b.order g.castSucc
  · by_cases hsucc : b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) + 1
    · exact D.weakAligned_oddCertificate_before_selected
        hselected a b i hi hbefore hsucc
    · have hcurrentLt : a.order
            ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
          b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
        have hindex :
            (⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Fin (n + 2)) =
                g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hlt
      exact D.weakAligned_commonCertificate_before_selected_of_current_lt
        hselected a b i hi hbefore hcurrentLt hsucc
  · by_cases heq : a.order g.castSucc = b.order g.castSucc
    · have hentryEq : a.orderSequence.entryOrZero (i.val - 1) =
          b.orderSequence.entryOrZero (i.val - 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact heq
      exact localData.equalCertificate a b D.smallLattice_le_large
        (D.lemma517Data_proved a b) i hi hentryEq
    · have hgt : b.order g.castSucc < a.order g.castSucc := by omega
      have hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
          a.orderSequence.entryOrZero (i.val - 1) + 1 := by
        rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        omega
      have happrox := localData.commonApproximation i hi hnotSucc
      exact D.weakAligned_commonCertificate_before_selected_of_current_gt
        hselected a b i hi hbefore hgt happrox

/-- Corollary 5.15 applied to the selected binary pair `J ⊆ J'`.  If
the norm order of `J` is exactly one above that of `J'`, a norm generator of
`J` is the required represented value in `J'`.  The chosen BONG of `J'` is
headed by an arbitrary norm generator, so its first order is the intrinsic
large selected norm order. -/
theorem selectedBinary_corollary515
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hnormSucc : ordUnit K
        (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition) =
      ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition) + 1) :
    ∃ B : BONG D.input.enlargedComponent.carrier
        D.input.enlargedComponent.space
        D.input.enlargedComponent.lattice 2,
      B.order 0 = ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition) ∧
      B.binaryOrderGap =
          2 * ordUnit K D.input.block.enlargedScaleGenerator -
            2 * ordUnit K
              (D.largeAlmostJordan.normGeneratorUnit
                D.largeSelectedPosition) ∧
      ((ramificationIndex K : Int) + B.binaryOrderGap / 2 ≤ 0 ∨
        (beliParameterDefect K B.binaryParameter ≠ ⊤ ∧
          B.binaryOrderGap +
            (beliParameterDefectNat K B.binaryParameter : Int) = 1)) := by
  have hfinLarge : finrank K D.input.enlargedComponent.carrier = 2 := by
    change finrank K
      (D.input.block.component.adjoinVector D.input.enlargedVector).carrier = 2
    rw [Lattice.QuadraticSublattice.adjoinVector_carrier]
    exact hfin
  have hposLarge : 0 < finrank K D.input.enlargedComponent.carrier := by
    omega
  obtain ⟨x, hx, hxAnisotropic⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos
      D.input.enlargedComponent.space D.input.enlargedComponent.lattice
      hposLarge
  let B : BONG D.input.enlargedComponent.carrier
      D.input.enlargedComponent.space
      D.input.enlargedComponent.lattice 2 :=
    BONG.ofNormGeneratorBinary D.input.enlargedComponent.space
      D.input.enlargedComponent.lattice x hx hxAnisotropic hfinLarge
  let X : Kˣ := Units.mk0
    (D.input.enlargedComponent.space.quadratic x) hxAnisotropic
  have hXOrder : ordUnit K X = ordUnit K
      (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
    apply Lattice.principalIdeal_eq_iff_ordUnit_eq X
      (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition) |>.mp
    exact hx.normIdeal_eq.symm.trans D.largeSelected_normIdeal_eq
  have hBOrder : B.order 0 = ordUnit K
      (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
    calc
      B.order 0 = ordUnit K (B.valueUnit 0) := B.order_eq_ordUnit 0
      _ = ordUnit K X := by
        congr 1
      _ = _ := hXOrder
  have hfinSmall : 0 < finrank K D.input.block.component.carrier := by
    omega
  obtain ⟨z, hz, hzAnisotropic⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos
      D.input.block.component.space D.input.block.component.lattice
      hfinSmall
  let Z : Kˣ := Units.mk0
    (D.input.block.component.space.quadratic z) hzAnisotropic
  have hZOrder : ordUnit K Z = ordUnit K
      (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition) := by
    apply Lattice.principalIdeal_eq_iff_ordUnit_eq Z
      (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition) |>.mp
    exact hz.normIdeal_eq.symm.trans D.smallSelected_normIdeal_eq
  have hzCarrier : (z : V) ∈ D.input.enlargedComponent.carrier := by
    change (z : V) ∈
      (D.input.block.component.adjoinVector
        D.input.enlargedVector).carrier
    simpa only [Lattice.QuadraticSublattice.adjoinVector_carrier] using
      z.property
  let zLarge : D.input.enlargedComponent.carrier := ⟨z, hzCarrier⟩
  have hzLarge : zLarge ∈ D.input.enlargedComponent.lattice := by
    apply D.small_le_large
    have hzEq : zLarge = z := by
      apply Subtype.ext
      rfl
    rw [hzEq]
    exact hz.mem
  have hquadratic :
      D.input.enlargedComponent.space.quadratic zLarge =
        D.input.block.component.space.quadratic z := by
    rfl
  have hzOrder : ord K
      (D.input.enlargedComponent.space.quadratic zLarge) =
        (((B.order 0 + 1 : Int)) : WithTop Int) := by
    calc
      ord K (D.input.enlargedComponent.space.quadratic zLarge) =
          ord K (Z : K) := by
        rw [hquadratic]
        rfl
      _ = ((ordUnit K Z : Int) : WithTop Int) :=
        (coe_ordUnit K Z).symm
      _ = _ := by rw [hZOrder, hnormSucc, ← hBOrder]
  have heven := B.even_binaryOrderGap_of_isModular
    D.input.block.enlargedScaleGenerator D.large_modular
  have hcor := B.represented_order_succ_implies_half_nonpos_or_defect_eq_one
    heven hzLarge hzOrder
  refine ⟨B, hBOrder, ?_, hcor⟩
  rw [B.binaryOrderGap_eq_of_isModular
    D.input.block.enlargedScaleGenerator D.large_modular, hBOrder]

/-- If the large selected effective norm is strictly below the selected
norm, a common component attaining that minimum lies before the selected
component.  A component after it would contribute the same value at the
small selected scale and contradict the one-step effective-norm jump. -/
theorem largeSelected_exists_minimizing_common_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hjump : D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) =
        D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) + 1)
    (hlt : D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) <
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition)) :
    ∃ c : Fin D.complementComponentCount,
      D.largeCommonPosition c < D.largeSelectedPosition ∧
        JordanProfileOrder.adjustedAt
            D.largeAlmostJordan.scaleOrderFamily
            D.largeAlmostJordan.normOrderFamily
            (ordUnit K D.input.block.enlargedScaleGenerator)
            (D.largeCommonPosition c) =
          D.largeAlmostJordan.effectiveNormOrderAt
            D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator) := by
  let rLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let rSmall := ordUnit K D.input.block.scaleGenerator
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition rLarge
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition rSmall
  obtain ⟨p, _hpMem, hp⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset
      (Fin (D.complementComponentCount + 1))))
    ⟨D.largeSelectedPosition, Finset.mem_univ _⟩
    (JordanProfileOrder.adjustedAt
      D.largeAlmostJordan.scaleOrderFamily
      D.largeAlmostJordan.normOrderFamily rLarge)
  have hp' : JordanProfileOrder.adjustedAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily rLarge p = eLarge := by
    simpa only [eLarge,
      Lattice.WeakJordanDecomposition.effectiveNormOrderAt,
      JordanProfileOrder.effectiveAt] using hp.symm
  rcases D.largePosition_eq_selected_or_common p with
    hpSelected | ⟨c, hpCommon⟩
  · subst p
    have : eLarge = ordUnit K
        (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) := by
      rw [← hp']
      simp [JordanProfileOrder.adjustedAt, rLarge,
        Lattice.WeakJordanDecomposition.scaleOrderFamily,
        Lattice.WeakJordanDecomposition.normOrderFamily,
        D.largeAlmostJordan_scaleGenerator_selected]
    exact False.elim ((ne_of_lt hlt) this)
  · subst p
    refine ⟨c, ?_, hp'⟩
    have hne := D.largeSelectedPosition_ne_common c
    rcases lt_or_gt_of_ne hne.symm with hbefore | hafter
    · exact hbefore
    · exfalso
      have hscaleAfter :=
        D.largeSelected_scale_lt_common_of_position_lt c hafter
      have hscaleStep : rSmall = rLarge + 1 := by
        rcases D.input.block.componentRank_and_enlargedScaleOrder with
          hOne | hTwo
        · omega
        · have hs := hTwo.2
          change rLarge = rSmall - 1 at hs
          omega
      have hcommonScale : rSmall ≤
          ordUnit K (D.complementStrictWeak.scaleGenerator c) := by
        change rSmall ≤ _
        change rLarge < _ at hscaleAfter
        omega
      have hsmallLe : eSmall ≤ eLarge := by
        have hnotSmall : ¬ordUnit K
            (D.complementStrictWeak.scaleGenerator c) < rSmall := by omega
        have hnotLarge : ¬ordUnit K
            (D.complementStrictWeak.scaleGenerator c) < rLarge := by omega
        calc
          eSmall ≤ JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily rSmall
              (D.smallCommonPosition c) :=
            JordanProfileOrder.effectiveAt_le _ _ _ _ _
          _ = JordanProfileOrder.adjustedAt
              D.largeAlmostJordan.scaleOrderFamily
              D.largeAlmostJordan.normOrderFamily rLarge
              (D.largeCommonPosition c) := by
            simp [JordanProfileOrder.adjustedAt,
              Lattice.WeakJordanDecomposition.scaleOrderFamily,
              Lattice.WeakJordanDecomposition.normOrderFamily,
              D.smallAlmostJordan_scaleGenerator_common,
              D.largeAlmostJordan_scaleGenerator_common,
              D.common_normOrder_eq, hnotSmall, hnotLarge]
          _ = eLarge := hp'
      change eSmall = eLarge + 1 at hjump
      omega

/-- Dually, if the small selected effective norm is strictly below its
selected norm, a common component attaining the minimum lies after the
selected component. -/
theorem smallSelected_exists_minimizing_common_after
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (hjump : D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) =
        D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) + 1)
    (hlt : D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) <
        ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition)) :
    ∃ c : Fin D.complementComponentCount,
      D.smallSelectedPosition < D.smallCommonPosition c ∧
        JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily
            (ordUnit K D.input.block.scaleGenerator)
            (D.smallCommonPosition c) =
          D.smallAlmostJordan.effectiveNormOrderAt
            D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator) := by
  let rLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let rSmall := ordUnit K D.input.block.scaleGenerator
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition rLarge
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition rSmall
  obtain ⟨p, _hpMem, hp⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset
      (Fin (D.complementComponentCount + 1))))
    ⟨D.smallSelectedPosition, Finset.mem_univ _⟩
    (JordanProfileOrder.adjustedAt
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily rSmall)
  have hp' : JordanProfileOrder.adjustedAt
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily rSmall p = eSmall := by
    simpa only [eSmall,
      Lattice.WeakJordanDecomposition.effectiveNormOrderAt,
      JordanProfileOrder.effectiveAt] using hp.symm
  rcases D.smallPosition_eq_selected_or_common p with
    hpSelected | ⟨c, hpCommon⟩
  · subst p
    have : eSmall = ordUnit K
        (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition) := by
      rw [← hp']
      simp [JordanProfileOrder.adjustedAt, rSmall,
        Lattice.WeakJordanDecomposition.scaleOrderFamily,
        Lattice.WeakJordanDecomposition.normOrderFamily,
        D.smallAlmostJordan_scaleGenerator_selected]
    exact False.elim ((ne_of_lt hlt) this)
  · subst p
    refine ⟨c, ?_, hp'⟩
    have hne := D.smallSelectedPosition_ne_common c
    rcases lt_or_gt_of_ne hne with hafter | hbefore
    · exact hafter
    · exfalso
      have hscaleBefore :=
        D.smallCommon_scale_lt_selected_of_position_lt c hbefore
      have hscaleStep : rSmall = rLarge + 1 := by
        rcases D.input.block.componentRank_and_enlargedScaleOrder with
          hOne | hTwo
        · omega
        · have hs := hTwo.2
          change rLarge = rSmall - 1 at hs
          omega
      have hcommonScale :
          ordUnit K (D.complementStrictWeak.scaleGenerator c) ≤ rLarge := by
        change _ ≤ rLarge
        change _ < rSmall at hscaleBefore
        omega
      have hlargeLe : eLarge ≤ eSmall - 2 := by
        calc
          eLarge ≤ JordanProfileOrder.adjustedAt
              D.largeAlmostJordan.scaleOrderFamily
              D.largeAlmostJordan.normOrderFamily rLarge
              (D.largeCommonPosition c) :=
            JordanProfileOrder.effectiveAt_le _ _ _ _ _
          _ = JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily rSmall
              (D.smallCommonPosition c) - 2 := by
            simp only [JordanProfileOrder.adjustedAt,
              Lattice.WeakJordanDecomposition.scaleOrderFamily,
              Lattice.WeakJordanDecomposition.normOrderFamily,
              D.smallAlmostJordan_scaleGenerator_common,
              D.largeAlmostJordan_scaleGenerator_common,
              D.common_normOrder_eq]
            split <;> omega
          _ = eSmall - 2 := by rw [hp']
      change eSmall = eLarge + 1 at hjump
      omega

/-- A common minimizer before the large selected component propagates with
slope two to the immediately preceding component scale.  At that common
scale the two aligned lattices have the same effective norm. -/
theorem previous_effectiveNormOrder_of_large_minimizer
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (c : Fin D.complementComponentCount)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hmin : JordanProfileOrder.adjustedAt
          D.largeAlmostJordan.scaleOrderFamily
          D.largeAlmostJordan.normOrderFamily
          (ordUnit K D.input.block.enlargedScaleGenerator)
          (D.largeCommonPosition c) =
        D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator)) :
    ∃ pPrev : Fin (D.complementComponentCount + 1),
      D.largeSelectedPosition.val = pPrev.val + 1 ∧
        let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
        let r := ordUnit K D.input.block.enlargedScaleGenerator
        let e := D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition r
        D.largeAlmostJordan.effectiveNormOrderAt pPrev s =
            e - 2 * (r - s) ∧
          D.smallAlmostJordan.effectiveNormOrderAt pPrev s =
            e - 2 * (r - s) := by
  let pPrev : Fin (D.complementComponentCount + 1) :=
    ⟨D.largeSelectedPosition.val - 1, by
      have hp := D.largeSelectedPosition.isLt
      omega⟩
  have hselectedVal : D.largeSelectedPosition.val = pPrev.val + 1 := by
    dsimp only [pPrev]
    have := Fin.mk_lt_mk.mp hbefore
    omega
  refine ⟨pPrev, hselectedVal, ?_⟩
  let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
  let r := ordUnit K D.input.block.enlargedScaleGenerator
  let e := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition r
  let commonScale := ordUnit K
    (D.complementStrictWeak.scaleGenerator c)
  have hcLePrev : D.largeCommonPosition c ≤ pPrev := by
    apply Fin.mk_le_mk.mpr
    change (D.largeCommonPosition c).val ≤
      D.largeSelectedPosition.val - 1
    have := Fin.mk_lt_mk.mp hbefore
    omega
  have hprevLeSelected : pPrev ≤ D.largeSelectedPosition := by
    apply Fin.mk_le_mk.mpr
    change D.largeSelectedPosition.val - 1 ≤
      D.largeSelectedPosition.val
    omega
  have hcommonScaleLe : commonScale ≤ s := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hcLePrev
    simpa only [commonScale, s,
      D.largeAlmostJordan_scaleGenerator_common] using hmono
  have hsLe : s ≤ r := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hprevLeSelected
    simpa only [s, r,
      D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hrSmall : r < ordUnit K D.input.block.scaleGenerator := by
    exact D.enlargedScaleOrder_lt_smallScaleOrder
  have hadjustedAtS : JordanProfileOrder.adjustedAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily s
        (D.largeCommonPosition c) = e - 2 * (r - s) := by
    have hmin' : JordanProfileOrder.adjustedAt
          D.largeAlmostJordan.scaleOrderFamily
          D.largeAlmostJordan.normOrderFamily r
          (D.largeCommonPosition c) = e := by
      simpa only [r, e] using hmin
    simp only [JordanProfileOrder.adjustedAt,
      Lattice.WeakJordanDecomposition.scaleOrderFamily,
      Lattice.WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_common] at hmin' ⊢
    split at hmin' <;> split <;> omega
  have hlargeUpper :
      D.largeAlmostJordan.effectiveNormOrderAt pPrev s ≤
        e - 2 * (r - s) := by
    exact (JordanProfileOrder.effectiveAt_le _ _ pPrev
      (D.largeCommonPosition c) s).trans_eq hadjustedAtS
  have hlargeLower : e - 2 * (r - s) ≤
      D.largeAlmostJordan.effectiveNormOrderAt pPrev s := by
    have hslope := JordanProfileOrder.effectiveAt_target_le_add_two_mul_sub
      D.largeAlmostJordan.scaleOrderFamily
      D.largeAlmostJordan.normOrderFamily pPrev
      D.largeSelectedPosition hsLe
    change e ≤ D.largeAlmostJordan.effectiveNormOrderAt pPrev s +
      2 * (r - s) at hslope
    omega
  have hlargeEq : D.largeAlmostJordan.effectiveNormOrderAt pPrev s =
      e - 2 * (r - s) := le_antisymm hlargeUpper hlargeLower
  have hcross := D.large_effectiveNormOrderAt_le_small_of_target_lt
    pPrev pPrev s (hsLe.trans_lt hrSmall)
  have hsmallUpper : D.smallAlmostJordan.effectiveNormOrderAt pPrev s ≤
      e - 2 * (r - s) := by
    calc
      D.smallAlmostJordan.effectiveNormOrderAt pPrev s ≤
          JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily s
            (D.smallCommonPosition c) :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = JordanProfileOrder.adjustedAt
            D.largeAlmostJordan.scaleOrderFamily
            D.largeAlmostJordan.normOrderFamily s
            (D.largeCommonPosition c) := by
        simp only [JordanProfileOrder.adjustedAt,
          Lattice.WeakJordanDecomposition.scaleOrderFamily,
          Lattice.WeakJordanDecomposition.normOrderFamily,
          D.smallAlmostJordan_scaleGenerator_common,
          D.largeAlmostJordan_scaleGenerator_common,
          D.common_normOrder_eq]
      _ = e - 2 * (r - s) := hadjustedAtS
  exact ⟨hlargeEq,
    le_antisymm hsmallUpper (hlargeEq ▸ hcross)⟩

/-- A common minimizer after the small selected component remains minimal
at the scale of the immediately following component.  The corresponding
large-side effective norm has the same value. -/
theorem next_effectiveNormOrder_of_small_minimizer
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    (c : Fin D.complementComponentCount)
    (hafter : D.smallSelectedPosition < D.smallCommonPosition c)
    (hmin : JordanProfileOrder.adjustedAt
          D.smallAlmostJordan.scaleOrderFamily
          D.smallAlmostJordan.normOrderFamily
          (ordUnit K D.input.block.scaleGenerator)
          (D.smallCommonPosition c) =
        D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator)) :
    ∃ pNext : Fin (D.complementComponentCount + 1),
      pNext.val = D.largeSelectedPosition.val + 1 ∧
        let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)
        let e := D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator)
        D.smallAlmostJordan.effectiveNormOrderAt pNext s = e ∧
          D.largeAlmostJordan.effectiveNormOrderAt pNext s = e := by
  have hlargeAfter : D.largeSelectedPosition < D.smallCommonPosition c := by
    rw [← hselected]
    exact hafter
  let pNext : Fin (D.complementComponentCount + 1) :=
    ⟨D.largeSelectedPosition.val + 1, by
      have hc := (D.smallCommonPosition c).isLt
      have hv := Fin.mk_lt_mk.mp hlargeAfter
      omega⟩
  have hpNextVal : pNext.val = D.largeSelectedPosition.val + 1 := rfl
  refine ⟨pNext, hpNextVal, ?_⟩
  let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)
  let r := ordUnit K D.input.block.scaleGenerator
  let e := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition r
  have hpNextLeCommon : pNext ≤ D.smallCommonPosition c := by
    apply Fin.mk_le_mk.mpr
    change D.largeSelectedPosition.val + 1 ≤
      (D.smallCommonPosition c).val
    have hv := Fin.mk_lt_mk.mp hlargeAfter
    omega
  have hpNextNeSelected : pNext ≠ D.largeSelectedPosition := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp only [pNext] at hv
    omega
  rcases D.largePosition_eq_selected_or_common pNext with
    hsel | ⟨d, hd⟩
  · exact (hpNextNeSelected hsel).elim
  · have hcommonPositions :=
      D.commonPositions_eq_of_selectedPositions_eq hselected d
    have hpNextSmall : D.smallCommonPosition d = pNext := by
      rw [hcommonPositions, hd]
    have hscaleEq : ordUnit K
        (D.smallAlmostJordan.scaleGenerator pNext) = s := by
      rw [← hpNextSmall,
        D.smallAlmostJordan_scaleGenerator_common]
      dsimp only [s]
      rw [hd, D.largeAlmostJordan_scaleGenerator_common]
    have hrLeS : r ≤ s := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono
        (show D.smallSelectedPosition ≤ D.smallCommonPosition d by
          rw [hpNextSmall, hselected]
          apply Fin.mk_le_mk.mpr
          change D.largeSelectedPosition.val ≤
            D.largeSelectedPosition.val + 1
          omega)
      change ordUnit K
          (D.smallAlmostJordan.scaleGenerator D.smallSelectedPosition) ≤
        ordUnit K
          (D.smallAlmostJordan.scaleGenerator (D.smallCommonPosition d))
        at hmono
      rw [D.smallAlmostJordan_scaleGenerator_selected,
        hpNextSmall, hscaleEq] at hmono
      exact hmono
    have hcommonScaleLe : s ≤ ordUnit K
        (D.complementStrictWeak.scaleGenerator c) := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono hpNextLeCommon
      change ordUnit K (D.smallAlmostJordan.scaleGenerator pNext) ≤
        ordUnit K
          (D.smallAlmostJordan.scaleGenerator (D.smallCommonPosition c))
        at hmono
      rw [hscaleEq,
        D.smallAlmostJordan_scaleGenerator_common] at hmono
      exact hmono
    have hadjustedAtS : JordanProfileOrder.adjustedAt
          D.smallAlmostJordan.scaleOrderFamily
          D.smallAlmostJordan.normOrderFamily s
          (D.smallCommonPosition c) = e := by
      have hmin' : JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily r
            (D.smallCommonPosition c) = e := by
        simpa only [r, e] using hmin
      simp only [JordanProfileOrder.adjustedAt,
        Lattice.WeakJordanDecomposition.scaleOrderFamily,
        Lattice.WeakJordanDecomposition.normOrderFamily,
        D.smallAlmostJordan_scaleGenerator_common] at hmin' ⊢
      rw [if_neg (not_lt_of_ge hcommonScaleLe)]
      rw [if_neg (not_lt_of_ge (hrLeS.trans hcommonScaleLe))] at hmin'
      exact hmin'
    have hsmallUpper :
        D.smallAlmostJordan.effectiveNormOrderAt pNext s ≤ e :=
      (JordanProfileOrder.effectiveAt_le _ _ pNext
        (D.smallCommonPosition c) s).trans_eq hadjustedAtS
    have hsmallLower : e ≤
        D.smallAlmostJordan.effectiveNormOrderAt pNext s :=
      JordanProfileOrder.effectiveAt_mono_target
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily D.smallSelectedPosition
        pNext hrLeS
    have hsmallEq := le_antisymm hsmallUpper hsmallLower
    have hrLargeLtS : ordUnit K D.input.block.enlargedScaleGenerator < s :=
      D.enlargedScaleOrder_lt_smallScaleOrder.trans_le hrLeS
    have hcross := D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      pNext pNext s hrLargeLtS
    have hlargeUpper :
        D.largeAlmostJordan.effectiveNormOrderAt pNext s ≤ e := by
      calc
        D.largeAlmostJordan.effectiveNormOrderAt pNext s ≤
            JordanProfileOrder.adjustedAt
              D.largeAlmostJordan.scaleOrderFamily
              D.largeAlmostJordan.normOrderFamily s
              (D.largeCommonPosition c) :=
          JordanProfileOrder.effectiveAt_le _ _ _ _ _
        _ = JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily s
              (D.smallCommonPosition c) := by
          simp only [JordanProfileOrder.adjustedAt,
            Lattice.WeakJordanDecomposition.scaleOrderFamily,
            Lattice.WeakJordanDecomposition.normOrderFamily,
            D.smallAlmostJordan_scaleGenerator_common,
            D.largeAlmostJordan_scaleGenerator_common,
            D.common_normOrder_eq]
        _ = e := hadjustedAtS
    have hlargeLower : e ≤
        D.largeAlmostJordan.effectiveNormOrderAt pNext s := by
      calc
        e = D.smallAlmostJordan.effectiveNormOrderAt pNext s := hsmallEq.symm
        _ ≤ D.largeAlmostJordan.effectiveNormOrderAt pNext s := hcross
    exact ⟨hsmallEq, le_antisymm hlargeUpper hlargeLower⟩

/-- At local coordinate zero of aligned selected components, the two BONG
orders are exactly the two selected effective norm orders. -/
theorem weakAligned_selected_current_orders
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (b : BONG.GoodBONG q N n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv I).2.val = 0) :
    a.order I = D.largeAlmostJordan.effectiveNormOrderAt
        D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator) ∧
      b.order I = D.smallAlmostJordan.effectiveNormOrderAt
        D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  have hxy := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 =
      D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hxy.1.symm
      _ = D.largeSelectedPosition := hposition
      _ = D.smallSelectedPosition := hselected.symm
  have hsmallLocal : (y.indexEquiv I).2.val = 0 :=
    hxy.2.symm.trans hlocal
  simp only [x] at hposition hlocal
  simp only [y] at hsmallPosition hsmallLocal
  have hlargeScale := D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
    D.largeSelectedPosition
      (ordUnit K D.input.block.enlargedScaleGenerator)
  have hsmallScale := D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
    D.smallSelectedPosition (ordUnit K D.input.block.scaleGenerator)
  constructor
  · rw [D.largeWeak_order_eq_localOrder a I]
    simp only [hposition,
      D.largeAlmostJordan_scaleGenerator_selected]
    rw [JordanProfileOrder.localOrder_even_of_scale_le hlargeScale
      ⟨0, by simpa only [zero_add] using hlocal⟩]
  · rw [D.smallWeak_order_eq_localOrder b I]
    simpa only [hsmallPosition,
      D.smallAlmostJordan_scaleGenerator_selected] using
      JordanProfileOrder.localOrder_even_of_scale_le hsmallScale
        ⟨0, by simpa only [zero_add] using hsmallLocal⟩

/-- In the first exceptional selected-binary branch, the source successor
order equals the target predecessor order and the intervening target gap is
odd.  This is the collision-safe form of `R_(i+1)=S_(i-1)` in Section 5. -/
theorem selectedBinary_sourceNext_eq_targetPrevious_of_largeNorm_strict
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (hlt : D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) <
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition)) :
    ∃ hiOne : 1 < i.val,
      a.order ⟨i.val, i.lt_large⟩ =
        b.order ⟨i.val - 2,
          (Nat.sub_le i.val 2).trans_lt i.lt_large⟩ ∧
      Odd (b.orderGap ⟨i.val - 2,
        (Nat.sub_lt i.pos (by omega)).trans_le
          (Nat.le_of_lt_succ (by simpa only [Nat.succ_eq_add_one] using
            i.lt_large))⟩) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  let r := ordUnit K D.input.block.enlargedScaleGenerator
  let e := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition r
  have horders := D.weakAligned_selected_current_orders
    hselected a b I hposition hlocal
  have hjump : D.smallAlmostJordan.effectiveNormOrderAt
        D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) = e + 1 := by
    change b.order I = a.order I + 1 at hcurrent
    simpa only [e, r, horders.1, horders.2] using hcurrent
  obtain ⟨c, hcbefore, hcmin⟩ :=
    D.largeSelected_exists_minimizing_common_before hfin hjump hlt
  obtain ⟨pPrev, hpPrev, hlargePrev, hsmallPrev⟩ :=
    D.previous_effectiveNormOrder_of_large_minimizer
      hfin c hcbefore hcmin
  let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
  have hpPrevNe : pPrev ≠ D.largeSelectedPosition := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  rcases D.largePosition_eq_selected_or_common pPrev with
    hpSel | ⟨d, hd⟩
  · exact (hpPrevNe hpSel).elim
  · have hcommonPositions :=
      D.commonPositions_eq_of_selectedPositions_eq hselected d
    have hpPrevSmall : D.smallCommonPosition d = pPrev := by
      rw [hcommonPositions, ← hd]
    have hscaleEq : ordUnit K
        (D.smallAlmostJordan.scaleGenerator pPrev) = s := by
      rw [← hpPrevSmall, D.smallAlmostJordan_scaleGenerator_common]
      dsimp only [s]
      rw [hd, D.largeAlmostJordan_scaleGenerator_common]
    have hxy := D.weakProfile_coordinates_eq hselected a b I
    have hsmallPosition : (y.indexEquiv I).1 =
        D.smallSelectedPosition := by
      calc
        (y.indexEquiv I).1 = (x.indexEquiv I).1 := hxy.1.symm
        _ = D.largeSelectedPosition := hposition
        _ = D.smallSelectedPosition := hselected.symm
    have hsmallLocal : (y.indexEquiv I).2.val = 0 :=
      hxy.2.symm.trans hlocal
    have hrankSelected : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 2 := by
      rw [hposition, D.largeAlmostJordan_finrank_selected, hfin]
    have hsourceLocalSucc : (x.indexEquiv I).2.val + 1 <
        finrank K
          (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      have hlocalBound := (x.indexEquiv I).2.isLt
      omega
    have hIVal : I.val = i.val - 1 := rfl
    have hIValSucc : I.val + 1 = i.val := by
      have := i.pos
      omega
    have hiNext : I.val + 1 < n + 2 := by
      rw [hIValSucc]
      exact i.lt_large
    have hsourceNextRaw :=
      x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
        I hiNext hsourceLocalSucc
    have hsourceScale :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
        D.largeSelectedPosition r
    have hsourceNext : a.order ⟨i.val, i.lt_large⟩ = 2 * r - e := by
      have hIndex : (⟨I.val + 1, hiNext⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        exact hIValSucc
      have hexpected : JordanProfileOrder.localOrder
          (ordUnit K
            (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
          (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
            (ordUnit K
              (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
          ((x.indexEquiv I).2.val + 1) = 2 * r - e := by
        have hoddLocal : ¬Even ((x.indexEquiv I).2.val + 1) := by
          rw [hlocal]
          decide
        simpa only [hposition,
          D.largeAlmostJordan_scaleGenerator_selected, r, e] using
          JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale
            hoddLocal
      calc
        a.order ⟨i.val, i.lt_large⟩ =
            a.toBONG.order ⟨I.val + 1, hiNext⟩ := by
          rw [hIndex]
          rfl
        _ = BONG.weakJordanExpectedOrder D.largeAlmostJordan
              (x.indexEquiv I).1
              ⟨(x.indexEquiv I).2.val + 1, hsourceLocalSucc⟩ :=
          hsourceNextRaw
        _ = 2 * r - e := hexpected
    have hpPrevRankPos : 0 < finrank K
        (D.smallAlmostJordan.component pPrev).carrier :=
      D.smallAlmostJordan.component_finrank_pos pPrev
    have hcurrentRankPos : 0 < finrank K
        (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier :=
      D.smallAlmostJordan.component_finrank_pos (y.indexEquiv I).1
    have hprevVal : (y.indexEquiv I).1.val = pPrev.val + 1 := by
      rw [hsmallPosition, hselected, hpPrev]
    have hiPos : 0 < I.val :=
      y.index_val_pos_of_previous_component I pPrev hprevVal hpPrevRankPos
    have hiOne : 1 < i.val := by omega
    have htargetPreviousRaw :=
      y.order_pred_eq_weakJordanExpectedOrder_of_previous_component
        I hiPos pPrev hprevVal hsmallLocal hpPrevRankPos hcurrentRankPos
    have htargetLast :=
      WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pPrev
    have hsmallPrev' : D.smallAlmostJordan.effectiveNormOrderAt pPrev s =
        e - 2 * (r - s) := by
      simpa only [s, r, e] using hsmallPrev
    let prevIndex : Fin (n + 2) :=
      ⟨i.val - 2, (Nat.sub_le i.val 2).trans_lt i.lt_large⟩
    have htargetPrevious : b.order prevIndex =
        2 * r - e := by
      have hIndex : I.val - 1 = i.val - 2 := by
        omega
      let rawPrev : Fin (n + 2) := ⟨I.val - 1, by omega⟩
      have hIndexFin : rawPrev = prevIndex := by
        apply Fin.ext
        exact hIndex
      have hexpected : JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator pPrev))
          (D.smallAlmostJordan.effectiveNormOrderAt pPrev
            (ordUnit K (D.smallAlmostJordan.scaleGenerator pPrev)))
          (finrank K (D.smallAlmostJordan.component pPrev).carrier - 1) =
            2 * r - e := by
        rw [htargetLast, hscaleEq, hsmallPrev']
        omega
      calc
        b.order prevIndex = b.toBONG.order rawPrev := by
          rw [hIndexFin]
          rfl
        _ = BONG.weakJordanExpectedOrder D.smallAlmostJordan pPrev
            ⟨finrank K (D.smallAlmostJordan.component pPrev).carrier - 1,
              by omega⟩ := htargetPreviousRaw
        _ = 2 * r - e := hexpected
    refine ⟨hiOne, hsourceNext.trans htargetPrevious.symm, ?_⟩
    let k : Fin (n + 1) := ⟨i.val - 2,
      (Nat.sub_lt i.pos (by omega)).trans_le
        (Nat.le_of_lt_succ (by simpa only [Nat.succ_eq_add_one] using
          i.lt_large))⟩
    have hgap : b.orderGap k = 2 * (e - r) + 1 := by
      unfold BONG.GoodBONG.orderGap
      have hcast : k.castSucc = prevIndex := by
        apply Fin.ext
        rfl
      have hsucc : k.succ = I := by
        apply Fin.ext
        change (i.val - 2) + 1 = I.val
        omega
      rw [hcast, hsucc, horders.2, htargetPrevious, hjump]
      omega
    change Odd (b.orderGap k)
    rw [hgap]
    exact ⟨e - r, by omega⟩

/-- The preceding-common-component branch proves the required nonpositive
representation alpha by the target-side primary cap. -/
theorem selectedBinary_representationAlphaValue_le_zero_of_largeNorm_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (hlt : D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) <
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition)) :
    a.representationAlphaValue b i ≤ 0 := by
  obtain ⟨hiOne, hneighbor, hodd⟩ :=
    D.selectedBinary_sourceNext_eq_targetPrevious_of_largeNorm_strict
      hselected hfin a b i hposition hlocal hcurrent hlt
  let previous : Fin (n + 1) := ⟨i.val - 2,
    (Nat.sub_lt i.pos (by omega)).trans_le
      (Nat.le_of_lt_succ (by simpa only [Nat.succ_eq_add_one] using
        i.lt_large))⟩
  let current : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let previousOrder : Fin (n + 2) :=
    ⟨i.val - 2, (Nat.sub_le i.val 2).trans_lt i.lt_large⟩
  let sourceNext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  have hodd' : Odd (b.orderGap previous) := by
    simpa only [previous] using hodd
  have hbeta := b.beli2009Corollary29_ii previous hodd'
  have hbetaLe : b.alphaValue previous ≤ (b.orderGap previous : ℚ) := by
    rw [hbeta]
    exact min_le_right _ _
  have hpreviousCast : previous.castSucc = previousOrder := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ = current := by
    apply Fin.ext
    change (i.val - 2) + 1 = i.val - 1
    omega
  unfold BONG.GoodBONG.orderGap at hbetaLe
  rw [hpreviousCast, hpreviousSucc] at hbetaLe
  have hcandidate :=
    a.representationAlphaValue_le_primary_previousAlpha b i hiOne
  let currentRaw : Fin (n + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let previousRaw : Fin (n + 1) :=
    ⟨i.val - 2, by have := i.lt_large; omega⟩
  have hcurrentRaw : currentRaw = current := by
    apply Fin.ext
    rfl
  have hpreviousRaw : previousRaw = previous := by
    apply Fin.ext
    rfl
  have hcandidate' : a.representationAlphaValue b i ≤
      ((a.order sourceNext - b.order current : Int) : ℚ) +
        b.alphaValue previous := by
    change a.representationAlphaValue b i ≤
      ((a.order sourceNext - b.order currentRaw : Int) : ℚ) +
        b.alphaValue previousRaw at hcandidate
    rw [hcurrentRaw, hpreviousRaw] at hcandidate
    exact hcandidate
  have hneighbor' : a.order sourceNext = b.order previousOrder := by
    simpa only [sourceNext, previousOrder] using hneighbor
  have hneighborQ : (a.order sourceNext : ℚ) =
      (b.order previousOrder : ℚ) := by
    exact_mod_cast hneighbor'
  push_cast at hbetaLe hcandidate'
  linarith

/-- In the second exceptional selected-binary branch, the first order in
the common component after the selected block equals the current target
order, and the source gap across that boundary is odd. -/
theorem selectedBinary_sourceAfter_eq_targetCurrent_of_smallNorm_strict
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (hlt : D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) <
        ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition)) :
    ∃ hafter : i.val + 1 < n + 2,
      a.order ⟨i.val + 1, hafter⟩ =
          b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc ∧
        Odd (a.orderGap ⟨i.val, by omega⟩) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  let r := ordUnit K D.input.block.enlargedScaleGenerator
  let e := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition r
  have horders := D.weakAligned_selected_current_orders
    hselected a b I hposition hlocal
  have hjump : D.smallAlmostJordan.effectiveNormOrderAt
        D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) = e + 1 := by
    change b.order I = a.order I + 1 at hcurrent
    simpa only [e, r, horders.1, horders.2] using hcurrent
  obtain ⟨c, hcafter, hcmin⟩ :=
    D.smallSelected_exists_minimizing_common_after hfin hjump hlt
  obtain ⟨pNext, hpNext, hsmallNext, hlargeNext⟩ :=
    D.next_effectiveNormOrder_of_small_minimizer
      hselected hfin c hcafter hcmin
  let s := ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)
  have hlocalSucc : (x.indexEquiv I).2.val + 1 <
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
    have hrank : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 2 := by
      rw [hposition, D.largeAlmostJordan_finrank_selected, hfin]
    have hlocalBound := (x.indexEquiv I).2.isLt
    omega
  have hglobalSucc : I.val + 1 < n + 2 :=
    x.global_succ_lt_of_local_succ I hlocalSucc
  let J : Fin (n + 2) := ⟨I.val + 1, hglobalSucc⟩
  let localOne : Fin (finrank K
      (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier) :=
    ⟨(x.indexEquiv I).2.val + 1, hlocalSucc⟩
  have hJCoord : x.indexEquiv J =
      ⟨(x.indexEquiv I).1, localOne⟩ := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalSucc
    have hcurrentInv : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hval' : (x.indexEquiv.symm
        ⟨(x.indexEquiv I).1, localOne⟩).val = I.val + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          simpa only [localOne] using hval
        _ = I.val + 1 := by rw [hcurrentInv]
    have hJInv : J = x.indexEquiv.symm
        ⟨(x.indexEquiv I).1, localOne⟩ := by
      apply Fin.ext
      exact hval'.symm
    rw [hJInv, x.indexEquiv.apply_symm_apply]
  have hJPosition : (x.indexEquiv J).1 =
      D.largeSelectedPosition := by
    rw [hJCoord]
    exact hposition
  have hJLocal : (x.indexEquiv J).2.val = 1 := by
    rw [hJCoord]
    dsimp only [localOne]
    omega
  have hselectedLast : (x.indexEquiv J).2.val + 1 =
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv J).1).carrier := by
    have hrank : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv J).1).carrier = 2 := by
      rw [hJPosition, D.largeAlmostJordan_finrank_selected, hfin]
    omega
  have hpNextVal : pNext.val = (x.indexEquiv J).1.val + 1 := by
    rw [hJPosition]
    exact hpNext
  have hpNextRankPos : 0 < finrank K
      (D.largeAlmostJordan.component pNext).carrier :=
    D.largeAlmostJordan.component_finrank_pos pNext
  have hafter : J.val + 1 < n + 2 := by
    have hval := x.inverse_index_val_next_component
      (x.indexEquiv J).1 pNext hpNextVal (x.indexEquiv J).2
        hselectedLast hpNextRankPos
    have hcurrentInv : x.indexEquiv.symm (x.indexEquiv J) = J :=
      x.indexEquiv.symm_apply_apply J
    have hbound :=
      (x.indexEquiv.symm ⟨pNext, ⟨0, hpNextRankPos⟩⟩).isLt
    have hval' :
        (x.indexEquiv.symm ⟨pNext, ⟨0, hpNextRankPos⟩⟩).val =
          J.val + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv J)).val + 1 := by
          simpa using hval
        _ = J.val + 1 := by rw [hcurrentInv]
    exact hval' ▸ hbound
  have hsourceAfterRaw :=
    x.order_succ_eq_weakJordanExpectedOrder_of_next_component
      J hafter pNext hpNextVal hselectedLast hpNextRankPos
  have hlargeNext' :
      D.largeAlmostJordan.effectiveNormOrderAt pNext s = e + 1 := by
    rw [hlargeNext]
    exact hjump
  have hnextScale := D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
    pNext s
  have hsourceAfter : a.order ⟨J.val + 1, hafter⟩ = e + 1 := by
    calc
      a.order ⟨J.val + 1, hafter⟩ =
          BONG.weakJordanExpectedOrder D.largeAlmostJordan pNext
            ⟨0, hpNextRankPos⟩ := hsourceAfterRaw
      _ = JordanProfileOrder.localOrder s
          (D.largeAlmostJordan.effectiveNormOrderAt pNext s) 0 := by
        rfl
      _ = e + 1 := by
        rw [JordanProfileOrder.localOrder_even_of_scale_le hnextScale
          (by decide), hlargeNext']
  have hIVal : I.val = i.val - 1 := rfl
  have hJVal : J.val = i.val := by
    dsimp only [J]
    have := i.pos
    omega
  have hafter' : i.val + 1 < n + 2 := by
    rw [← hJVal]
    exact hafter
  have hsourceAfter' : a.order ⟨i.val + 1, hafter'⟩ = e + 1 := by
    have hindex : (⟨i.val + 1, hafter'⟩ : Fin (n + 2)) =
        ⟨J.val + 1, hafter⟩ := by
      apply Fin.ext
      change i.val + 1 = J.val + 1
      omega
    rw [hindex]
    exact hsourceAfter
  have hsourceSelectedNextRaw :=
    x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hglobalSucc hlocalSucc
  have hsourceScale :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      D.largeSelectedPosition r
  have hsourceSelectedNext : a.order ⟨i.val, by omega⟩ = 2 * r - e := by
    have hindex : (⟨i.val, by omega⟩ : Fin (n + 2)) = J := by
      apply Fin.ext
      exact hJVal.symm
    rw [hindex]
    have hexpected : BONG.weakJordanExpectedOrder
        D.largeAlmostJordan (x.indexEquiv I).1 localOne = 2 * r - e := by
      change JordanProfileOrder.localOrder
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
        (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
          (ordUnit K
            (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
        localOne.val = _
      have hoddLocal : ¬Even localOne.val := by
        dsimp only [localOne]
        rw [hlocal]
        decide
      simpa only [hposition,
        D.largeAlmostJordan_scaleGenerator_selected, r, e] using
        JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hoddLocal
    exact hsourceSelectedNextRaw.trans hexpected
  refine ⟨hafter', ?_, ?_⟩
  · calc
      a.order ⟨i.val + 1, hafter'⟩ = e + 1 := hsourceAfter'
      _ = b.order I := by rw [horders.2, hjump]
      _ = b.order
          (BONG.GoodBONG.representationAlphaIndex i).castSucc := rfl
  · let k : Fin (n + 1) := ⟨i.val, by omega⟩
    have hgap : a.orderGap k = 2 * (e - r) + 1 := by
      unfold BONG.GoodBONG.orderGap
      have hcast : k.castSucc = J := by
        apply Fin.ext
        exact hJVal.symm
      have hsucc : k.succ = (⟨i.val + 1, hafter'⟩ : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      rw [hcast, hsucc]
      have hJOrder : a.order J = 2 * r - e := by
        have hindex : J = (⟨i.val, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          exact hJVal
        rw [hindex]
        exact hsourceSelectedNext
      rw [hJOrder, hsourceAfter']
      omega
    change Odd (a.orderGap k)
    rw [hgap]
    exact ⟨e - r, by omega⟩

/-- The following-common-component branch proves nonpositivity by the
source-side primary cap. -/
theorem selectedBinary_representationAlphaValue_le_zero_of_smallNorm_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (hlt : D.smallAlmostJordan.effectiveNormOrderAt
          D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) <
        ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition)) :
    a.representationAlphaValue b i ≤ 0 := by
  obtain ⟨hafter, hneighbor, hodd⟩ :=
    D.selectedBinary_sourceAfter_eq_targetCurrent_of_smallNorm_strict
      hselected hfin a b i hposition hlocal hcurrent hlt
  let next : Fin (n + 1) := ⟨i.val, by omega⟩
  let sourceCurrent : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let sourceAfter : Fin (n + 2) := ⟨i.val + 1, hafter⟩
  let targetCurrent : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  have hodd' : Odd (a.orderGap next) := by
    simpa only [next] using hodd
  have halpha := a.beli2009Corollary29_ii next hodd'
  have halphaLe : a.alphaValue next ≤ (a.orderGap next : ℚ) := by
    rw [halpha]
    exact min_le_right _ _
  have hnextCast : next.castSucc = sourceCurrent := by
    apply Fin.ext
    rfl
  have hnextSucc : next.succ = sourceAfter := by
    apply Fin.ext
    rfl
  unfold BONG.GoodBONG.orderGap at halphaLe
  rw [hnextCast, hnextSucc] at halphaLe
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i (by omega)
  let sourceRaw : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let targetRaw : Fin (n + 2) :=
    ⟨i.val - 1, by have := i.lt_large; omega⟩
  let alphaRaw : Fin (n + 1) := ⟨i.val, by omega⟩
  have hsourceRaw : sourceRaw = sourceCurrent := by rfl
  have htargetRaw : targetRaw = targetCurrent := by
    apply Fin.ext
    rfl
  have halphaRaw : alphaRaw = next := by rfl
  have hcandidate' : a.representationAlphaValue b i ≤
      ((a.order sourceCurrent - b.order targetCurrent : Int) : ℚ) +
        a.alphaValue next := by
    change a.representationAlphaValue b i ≤
      ((a.order sourceRaw - b.order targetRaw : Int) : ℚ) +
        a.alphaValue alphaRaw at hcandidate
    rw [hsourceRaw, htargetRaw, halphaRaw] at hcandidate
    exact hcandidate
  have hneighbor' : a.order sourceAfter = b.order targetCurrent := by
    simpa only [sourceAfter, targetCurrent] using hneighbor
  have hneighborQ : (a.order sourceAfter : ℚ) =
      (b.order targetCurrent : ℚ) := by
    exact_mod_cast hneighbor'
  push_cast at halphaLe hcandidate'
  linarith

/-- The second coordinate of the selected binary weak component is the
complementary order `2r-e`. -/
theorem selectedBinary_sourceNext_order
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    a.order ⟨i.val, i.lt_large⟩ =
      2 * ordUnit K D.input.block.enlargedScaleGenerator -
        D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let x := D.largeWeakProfileWitness a
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  have hrank : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 2 := by
    rw [hposition, D.largeAlmostJordan_finrank_selected, hfin]
  have hlocalSucc : (x.indexEquiv I).2.val + 1 <
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
    have hbound := (x.indexEquiv I).2.isLt
    omega
  have hIVal : I.val = i.val - 1 := rfl
  have hIValSucc : I.val + 1 = i.val := by
    have := i.pos
    omega
  have hglobal : I.val + 1 < n + 2 := by
    rw [hIValSucc]
    exact i.lt_large
  have hraw := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
    I hglobal hlocalSucc
  have hscale := D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
    D.largeSelectedPosition
      (ordUnit K D.input.block.enlargedScaleGenerator)
  have hodd : ¬Even ((x.indexEquiv I).2.val + 1) := by
    rw [hlocal]
    decide
  have hexpected : BONG.weakJordanExpectedOrder D.largeAlmostJordan
      (x.indexEquiv I).1
      ⟨(x.indexEquiv I).2.val + 1, hlocalSucc⟩ =
        2 * ordUnit K D.input.block.enlargedScaleGenerator -
          D.largeAlmostJordan.effectiveNormOrderAt
            D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator) := by
    change JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K
          (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      ((x.indexEquiv I).2.val + 1) = _
    simpa only [hposition,
      D.largeAlmostJordan_scaleGenerator_selected] using
      JordanProfileOrder.localOrder_odd_of_scale_le hscale hodd
  have hindex : (⟨I.val + 1, hglobal⟩ : Fin (n + 2)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    exact hIValSucc
  calc
    a.order ⟨i.val, i.lt_large⟩ =
        a.toBONG.order ⟨I.val + 1, hglobal⟩ := by
      rw [hindex]
      rfl
    _ = BONG.weakJordanExpectedOrder D.largeAlmostJordan
        (x.indexEquiv I).1
        ⟨(x.indexEquiv I).2.val + 1, hlocalSucc⟩ := hraw
    _ = _ := hexpected

/-- The hyperbolic/half-gap alternative of Corollary 5.15 makes the
representation half-gap strictly negative at the selected boundary. -/
theorem selectedBinary_representationAlphaValue_le_zero_of_half
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (hhalf : (ramificationIndex K : Int) +
        (2 * ordUnit K D.input.block.enlargedScaleGenerator -
          2 * D.largeAlmostJordan.effectiveNormOrderAt
            D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator)) / 2 ≤ 0) :
    a.representationAlphaValue b i ≤ 0 := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let r := ordUnit K D.input.block.enlargedScaleGenerator
  let e := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition r
  have horders := D.weakAligned_selected_current_orders
    hselected a b I hposition hlocal
  have htarget : b.order I = e + 1 := by
    change b.order I = a.order I + 1 at hcurrent
    rw [hcurrent, horders.1]
  have hsource := D.selectedBinary_sourceNext_order
    hfin a i hposition hlocal
  have hhalfInt : (ramificationIndex K : Int) + (r - e) ≤ 0 := by
    change (ramificationIndex K : Int) + (2 * r - 2 * e) / 2 ≤ 0
      at hhalf
    omega
  have hhalfQ : (ramificationIndex K : ℚ) + ((r - e : Int) : ℚ) ≤ 0 := by
    exact_mod_cast hhalfInt
  have hvalue :
      (((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ) : ℚ) ≤ 0 := by
    have htargetIndex :
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) = I := by
      apply Fin.ext
      rfl
    rw [htargetIndex, htarget]
    change a.order ⟨i.val, i.lt_large⟩ = 2 * r - e at hsource
    rw [hsource]
    push_cast at hhalfQ ⊢
    linarith
  apply WithTop.coe_le_coe.mp
  rw [a.coe_representationAlphaValue b i]
  calc
    a.representationAlpha b i ≤ a.representationHalfGap b i :=
      a.representationAlpha_le_halfGap b i
    _ = (((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) /
          2 + (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
      rfl
    _ ≤ 0 := by exact_mod_cast hvalue

/-- For every aligned selected position, the determinant of the large
almost-Jordan prefix through the selected component is the determinant of
the small prefix before it times the enlarged selected determinant, up to
an actual square.  Unlike the earlier collision-specialized form, this
also covers a first selected component and the no-collision case. -/
theorem exists_aligned_largeSelectedPrefixDeterminant_eq_smallPrefix_mul_enlarged_square
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition) :
    ∃ s : Kˣ,
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) *
          D.input.enlargedComponent.refinedDeterminantUnit * s ^ 2 =
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice
            (D.largeSelectedPosition.val + 1)
          |>.refinedDeterminantUnit) := by
  classical
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  let p := D.largeSelectedPosition
  let cut := p.val
  have hprefixClass :
      unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) := by
    by_cases hzero : cut = 0
    · have hPsub : Subsingleton
          (P.prefixQuadraticSublattice cut).carrier := by
        rw [hzero]
        exact Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton P
      have hQsub : Subsingleton
          (Q.prefixQuadraticSublattice cut).carrier := by
        rw [hzero]
        exact Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton Q
      have hPone : unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) = 1 := by
        change Lattice.determinantClass
          (P.prefixQuadraticSublattice cut).space
          (P.prefixQuadraticSublattice cut).lattice = 1
        exact Lattice.determinantClass_eq_one_of_subsingleton _ _ hPsub
      have hQone : unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) = 1 := by
        change Lattice.determinantClass
          (Q.prefixQuadraticSublattice cut).space
          (Q.prefixQuadraticSublattice cut).lattice = 1
        exact Lattice.determinantClass_eq_one_of_subsingleton _ _ hQsub
      exact hPone.trans hQone.symm
    · have hcut : cut - 1 + 1 = cut := by omega
      have hP : cut - 1 + 1 ≤ D.complementComponentCount + 1 := by
        rw [hcut]
        exact p.isLt.le
      have hQ : cut - 1 + 1 ≤ D.complementComponentCount + 1 := hP
      have hprefixComponent (z : Fin (cut - 1 + 1)) :
          P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
            Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
        let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
        let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
        have hjPVal : jP.val = z.val :=
          P.prefixIndexEquiv_val (cut - 1 + 1) hP z
        have hjQVal : jQ.val = z.val :=
          Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
        have hjEq : jP = jQ := by
          apply Fin.ext
          rw [hjPVal, hjQVal]
        have hjBefore : jP < D.largeSelectedPosition := by
          change jP.val < p.val
          rw [hjPVal]
          have hz := z.isLt
          omega
        change D.largeAlmostJordan.component jP =
          D.smallAlmostJordan.component jQ
        rw [← hjEq]
        exact D.aligned_component_eq hselected jP (ne_of_lt hjBefore)
      let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
        (fun z ↦ by
          rw [hprefixComponent z]
          exact Lattice.Isometry.refl _ _)
      have hraw := Lattice.determinantClass_eq_of_isometry F
      change unitSquareClass K
          (P.prefixQuadraticSublattice (cut - 1 + 1)
            |>.refinedDeterminantUnit) =
        unitSquareClass K
          (Q.prefixQuadraticSublattice (cut - 1 + 1)
            |>.refinedDeterminantUnit) at hraw
      rw [hcut] at hraw
      exact hraw
  have happend := P.unitSquareClass_prefix_succ_eq_mul_component p
  rw [D.largeAlmostJordan_component_selected] at happend
  have htarget :
      unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
        unitSquareClass K
          ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit) := by
    calc
      unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
          unitSquareClass K
              ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit := by
        rw [unitSquareClass_mul]
      _ = unitSquareClass K
              ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit := by
        rw [hprefixClass]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) := by
        rw [unitSquareClass_mul]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit) := by
        simpa only [P, p, cut] using happend.symm
  obtain ⟨s, hs⟩ :=
    BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
      ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
        D.input.enlargedComponent.refinedDeterminantUnit)
      ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit)
      htarget
  refine ⟨s, ?_⟩
  simpa only [P, Q, p, cut, ← hselected] using hs

/-- The determinant of the target almost-Jordan prefix immediately before
the aligned selected binary component is an approximation at `i-1`, even
when the selected component is amalgamated with the common component on
its right. -/
theorem selectedBinary_smallPrefixBefore_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    b.IsPrefixApproximation (i.val - 1)
      (D.smallAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice D.smallSelectedPosition.val
        |>.refinedDeterminantUnit) := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  have hxy := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 =
      D.smallSelectedPosition :=
    hxy.1.symm.trans (hposition.trans hselected.symm)
  have hsmallLocal : (y.indexEquiv I).2.val = 0 :=
    hxy.2.symm.trans hlocal
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallPosition.le
  have hoffset : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallPosition.le
  have hresolvedLocal : (Rsmall.profile.indexEquiv I).2.val = 0 := by
    rw [Rsmall.localCoordinate_eq, hoffset, Nat.zero_add]
    exact hsmallLocal
  have hstart : Rsmall.coordinates.start = i.val - 1 := by
    have hindex := Rsmall.index_val_eq_coordinates_start_add_local
    have hIVal : I.val = i.val - 1 := rfl
    omega
  let determinant := Rsmall.determinantSeedData
  have hseed := determinant.evenSeed
  change b.IsPrefixApproximation Rsmall.coordinates.start
    determinant.leftDet at hseed
  rw [hstart] at hseed
  obtain ⟨s, hs⟩ :=
    Rsmall.exists_determinantSeedData_eq_weakPrefix_mul_square hoffset
  have hs' :
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) =
        determinant.leftDet * s ^ 2 := by
    rw [hsmallPosition] at hs
    simpa only [determinant] using hs
  rw [hs']
  exact (b.isPrefixApproximation_mul_square_iff
    (i.val - 1) determinant.leftDet s).2 hseed

/-- The determinant of the source almost-Jordan prefix through the aligned
selected binary component is an approximation at `i+1`.  A large-side
collision is resolved by amalgamating the common left component and then
transporting the strict prefix determinant back by a square. -/
theorem selectedBinary_largePrefixThrough_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0) :
    a.IsPrefixApproximation (i.val + 1)
      (D.largeAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice
          (D.largeSelectedPosition.val + 1)
        |>.refinedDeterminantUnit) := by
  classical
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let x := D.largeWeakProfileWitness a
  change (x.indexEquiv I).1 = D.largeSelectedPosition at hposition
  change (x.indexEquiv I).2.val = 0 at hlocal
  by_cases hcollision : D.LargeScaleCollision
  · obtain ⟨c, hscale⟩ := hcollision
    obtain ⟨k, hkCommon, hkSelected⟩ :=
      D.largeCollision_adjacent c hscale
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hkCommon, hkSelected]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    let S := D.largeAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k
            ⟨hkCommon, hkSelected⟩)
    let P : BONG.JordanOrderProfileWitness a.toBONG
        (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hright : (x.indexEquiv I).1 = k.succ :=
      hposition.trans hkSelected.symm
    have hcoordinates := x.strict_coordinates_of_right
      D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict S hstrict P
    let p := (P.indexEquiv I).1
    let C := w.jordanBlockCoordinates
      (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
        D.largeAlmostJordan k heq) p
    let commonRank :=
      finrank K (D.largeAlmostJordan.component k.castSucc).carrier
    have hp : p = k := hcoordinates.1
    have hresolvedLocal : (P.indexEquiv I).2.val = commonRank := by
      change (P.indexEquiv I).2.val = commonRank
      rw [hcoordinates.2, hlocal, Nat.add_zero]
    have hrank : finrank K (S.component p).carrier = commonRank + 2 := by
      rw [hp, D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq,
        hkSelected, D.largeAlmostJordan_finrank_selected, hfin]
    have hindex := w.index_val_eq_componentStart_add_local I
    have hindex' : I.val = w.componentStart p + commonRank := by
      calc
        I.val = w.componentStart p + (P.indexEquiv I).2.val := hindex
        _ = w.componentStart p + commonRank := by rw [hresolvedLocal]
    have hindex'' : i.val - 1 = w.componentStart p + commonRank := by
      have hIVal : I.val = i.val - 1 := rfl
      exact hIVal.symm.trans hindex'
    have hstop : C.stop = i.val + 1 := by
      change w.componentStart p + finrank K (S.component p).carrier =
        i.val + 1
      have hiPos := i.pos
      rw [hrank]
      omega
    have happroxRaw :=
      BONG.WeakJordanOrderProfileWitness.prefixThrough_isPrefixApproximation
        a S
        (D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
          D.largeAlmostJordan k heq)
        hstrict P p
    change a.IsPrefixApproximation C.stop
      (S.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit) at happroxRaw
    rw [hstop] at happroxRaw
    let dOld : Kˣ :=
      (D.largeAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice
          (D.largeSelectedPosition.val + 1)
        |>.refinedDeterminantUnit)
    let dMerged : Kˣ :=
      (S.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit)
    change a.IsPrefixApproximation (i.val + 1) dMerged at happroxRaw
    obtain ⟨s, hs⟩ :=
      D.largeAlmostJordan.exists_mergeAdjacentAt_prefixThrough_mul_square
        k heq
    have hs' : dOld * s ^ 2 = dMerged := by
      dsimp only [dOld, dMerged, S]
      rw [hp, show D.largeSelectedPosition.val = k.val + 1 by
        exact congrArg Fin.val hkSelected |>.symm]
      simpa only [Nat.add_assoc] using hs
    change a.IsPrefixApproximation (i.val + 1) dOld
    rw [← hs'] at happroxRaw
    exact (a.isPrefixApproximation_mul_square_iff
      (i.val + 1) dOld s).1 happroxRaw
  · let hstrict :=
      D.largeAlmostJordan_scaleOrder_strict_of_noCollision hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict
      D.largeAlmostJordan hstrict P
    let p := (P.indexEquiv I).1
    let C := w.jordanBlockCoordinates
      D.largeAlmostJordan_hasImproperEvenRank p
    have hcoordinates :=
      D.largeWeak_noCollision_coordinates_eq hcollision a I
    have hp : p = D.largeSelectedPosition :=
      hcoordinates.1.symm.trans hposition
    have hresolvedLocal : (P.indexEquiv I).2.val = 0 :=
      hcoordinates.2.symm.trans hlocal
    have hrank : finrank K
        (D.largeAlmostJordan.component p).carrier = 2 := by
      rw [hp, D.largeAlmostJordan_finrank_selected, hfin]
    have hindex := w.index_val_eq_componentStart_add_local I
    have hindex' : I.val = w.componentStart p := by
      calc
        I.val = w.componentStart p + (P.indexEquiv I).2.val := hindex
        _ = w.componentStart p := by rw [hresolvedLocal, Nat.add_zero]
    have hindex'' : i.val - 1 = w.componentStart p := by
      have hIVal : I.val = i.val - 1 := rfl
      exact hIVal.symm.trans hindex'
    have hstop : C.stop = i.val + 1 := by
      change w.componentStart p +
        finrank K (D.largeAlmostJordan.component p).carrier = i.val + 1
      have hiPos := i.pos
      rw [hrank]
      omega
    have happroxRaw :=
      BONG.WeakJordanOrderProfileWitness.prefixThrough_isPrefixApproximation
        a D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
          hstrict P p
    change a.IsPrefixApproximation C.stop
      (D.largeAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit) at happroxRaw
    rw [hstop, hp] at happroxRaw
    exact happroxRaw

/-- The refined determinant of an enlarged binary component represents
the same square class as the binary parameter of any BONG on that
component. -/
theorem enlargedDeterminant_mul_square_eq_binaryParameter
    (D : Beli2019Lemma51Data q M N)
    (B : BONG D.input.enlargedComponent.carrier
      D.input.enlargedComponent.space
      D.input.enlargedComponent.lattice 2) :
    ∃ s : Kˣ,
      D.input.enlargedComponent.refinedDeterminantUnit * s ^ 2 =
        B.binaryParameter := by
  obtain ⟨p, hp⟩ :=
    Lattice.exists_valueProduct_eq_determinantUnit_mul_square B
  have hp' : B.valueProduct =
      D.input.enlargedComponent.refinedDeterminantUnit * p ^ 2 := by
    simpa only [Lattice.QuadraticSublattice.refinedDeterminantUnit] using hp
  have hparameter : B.valueProduct =
      B.binaryParameter * (B.valueUnit 0) ^ 2 := by
    rw [BONG.valueProduct, B.prefixProduct_succ 1 (by omega),
      B.prefixProduct_succ 0 (by omega)]
    simp [BONG.binaryParameter, div_eq_mul_inv, pow_two]
    exact mul_comm _ _
  let s := p / B.valueUnit 0
  refine ⟨s, ?_⟩
  calc
    D.input.enlargedComponent.refinedDeterminantUnit * s ^ 2 =
        (D.input.enlargedComponent.refinedDeterminantUnit * p ^ 2) /
          (B.valueUnit 0) ^ 2 := by
      dsimp only [s]
      rw [div_pow]
      exact (mul_div_assoc
        D.input.enlargedComponent.refinedDeterminantUnit
        (p ^ 2) ((B.valueUnit 0) ^ 2)).symm
    _ = B.valueProduct / (B.valueUnit 0) ^ 2 := by rw [← hp']
    _ = (B.binaryParameter * (B.valueUnit 0) ^ 2) /
        (B.valueUnit 0) ^ 2 := by rw [hparameter]
    _ = B.binaryParameter := mul_div_cancel_right _ _

/-- In the finite-defect alternative of Corollary 5.15, the selected
binary primary candidate is exactly bounded by
`(binaryOrderGap - 1) + d(-parameter) = 0`.  The prefix determinants above
identify the capped defect with the same binary parameter square class. -/
theorem selectedBinary_representationAlphaValue_le_zero_of_defect
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1)
    (B : BONG D.input.enlargedComponent.carrier
      D.input.enlargedComponent.space
      D.input.enlargedComponent.lattice 2)
    (hBGap : B.binaryOrderGap =
      2 * ordUnit K D.input.block.enlargedScaleGenerator -
        2 * D.largeAlmostJordan.effectiveNormOrderAt
          D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator))
    (hfinite : beliParameterDefect K B.binaryParameter ≠ ⊤)
    (hdefectEq : B.binaryOrderGap +
      (beliParameterDefectNat K B.binaryParameter : Int) = 1) :
    a.representationAlphaValue b i ≤ 0 := by
  let I : Fin (n + 2) :=
    (BONG.GoodBONG.representationAlphaIndex i).castSucc
  let r := ordUnit K D.input.block.enlargedScaleGenerator
  let e := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition r
  let X : Kˣ :=
    (D.largeAlmostJordan.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice
        (D.largeSelectedPosition.val + 1)
      |>.refinedDeterminantUnit)
  let Y : Kˣ :=
    (D.smallAlmostJordan.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice D.smallSelectedPosition.val
      |>.refinedDeterminantUnit)
  let dE : Kˣ := D.input.enlargedComponent.refinedDeterminantUnit
  have hX : a.IsPrefixApproximation (i.val + 1) X := by
    simpa only [X] using
      D.selectedBinary_largePrefixThrough_isPrefixApproximation
        hfin a i hposition hlocal
  have hY : b.IsPrefixApproximation (i.val - 1) Y := by
    simpa only [Y] using
      D.selectedBinary_smallPrefixBefore_isPrefixApproximation
        hselected a b i hposition hlocal
  obtain ⟨sDet, hDet⟩ :=
    D.exists_aligned_largeSelectedPrefixDeterminant_eq_smallPrefix_mul_enlarged_square
      hselected
  have hDet' : Y * dE * sDet ^ 2 = X := by
    simpa only [X, Y, dE] using hDet
  obtain ⟨sParam, hParam⟩ :=
    D.enlargedDeterminant_mul_square_eq_binaryParameter B
  have hParam' : dE * sParam ^ 2 = B.binaryParameter := by
    simpa only [dE] using hParam
  have hproduct : (((-1 : Kˣ) * X * Y) * sParam ^ 2) =
      (-B.binaryParameter) * (Y * sDet) ^ 2 := by
    rw [← hDet', ← hParam']
    simp only [neg_mul, one_mul, mul_pow, pow_two]
    ac_rfl
  have hproductDefect :
      BONG.GoodBONG.defectOrder (K := K) ((-1 : Kˣ) * X * Y) =
        BONG.GoodBONG.defectOrder (K := K) (-B.binaryParameter) := by
    calc
      BONG.GoodBONG.defectOrder (K := K) ((-1 : Kˣ) * X * Y) =
          BONG.GoodBONG.defectOrder (K := K)
            (((-1 : Kˣ) * X * Y) * sParam ^ 2) :=
        (BONG.GoodBONG.defectOrder_mul_square
          ((-1 : Kˣ) * X * Y) sParam).symm
      _ = BONG.GoodBONG.defectOrder (K := K)
          ((-B.binaryParameter) * (Y * sDet) ^ 2) := by rw [hproduct]
      _ = BONG.GoodBONG.defectOrder (K := K) (-B.binaryParameter) :=
        BONG.GoodBONG.defectOrder_mul_square
          (-B.binaryParameter) (Y * sDet)
  let d := beliParameterDefectNat K B.binaryParameter
  have hdefectOrder : BONG.GoodBONG.defectOrder (K := K)
      (-B.binaryParameter) = (((d : Nat) : ℚ) : WithTop ℚ) := by
    have hfinite' : quadraticDefect K (-B.binaryParameter) ≠ ⊤ := by
      simpa only [beliParameterDefect] using hfinite
    unfold BONG.GoodBONG.defectOrder d beliParameterDefectNat
      beliParameterDefect
    rw [← ENat.coe_toNat hfinite']
    rfl
  have htruncated : a.truncatedPrefixDefect b (-1)
      (i.val + 1) (i.val - 1) ≤ (((d : Nat) : ℚ) : WithTop ℚ) := by
    rw [a.truncatedPrefixDefect_eq_of_approximations b (-1)
      (i.val + 1) (i.val - 1) X Y hX hY]
    exact (min_le_left _ _).trans_eq (hproductDefect.trans hdefectOrder)
  have horders := D.weakAligned_selected_current_orders
    hselected a b I hposition hlocal
  have htarget : b.order I = e + 1 := by
    change b.order I = a.order I + 1 at hcurrent
    rw [hcurrent, horders.1]
  have hsource := D.selectedBinary_sourceNext_order
    hfin a i hposition hlocal
  have hdiff :
      a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ =
        B.binaryOrderGap - 1 := by
    have htargetIndex :
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) = I := by
      apply Fin.ext
      rfl
    rw [htargetIndex, htarget]
    change a.order ⟨i.val, i.lt_large⟩ = 2 * r - e at hsource
    change B.binaryOrderGap = 2 * r - 2 * e at hBGap
    rw [hsource, hBGap]
    omega
  have hzeroInt : B.binaryOrderGap - 1 + (d : Int) = 0 := by
    change B.binaryOrderGap +
      (beliParameterDefectNat K B.binaryParameter : Int) = 1 at hdefectEq
    simpa only [d] using (show B.binaryOrderGap - 1 +
      (beliParameterDefectNat K B.binaryParameter : Int) = 0 by omega)
  have hzeroQ : ((B.binaryOrderGap - 1 : Int) : ℚ) + (d : ℚ) = 0 := by
    exact_mod_cast hzeroInt
  have hprimary : a.representationPrimaryDefect b i ≤ 0 := by
    unfold BONG.GoodBONG.representationPrimaryDefect
    rw [hdiff]
    calc
      ((((B.binaryOrderGap - 1 : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)) ≤
        ((((B.binaryOrderGap - 1 : Int) : ℚ) : WithTop ℚ) +
          (((d : Nat) : ℚ) : WithTop ℚ)) :=
        add_le_add_right htruncated _
      _ = 0 := by
        norm_cast
  apply WithTop.coe_le_coe.mp
  rw [a.coe_representationAlphaValue b i]
  exact (a.representationAlpha_le_primary b i).trans hprimary

/-- Complete exceptional selected-binary branch of Section 5(ii).  The two
strict effective-norm subcases are controlled by the neighbouring common
component.  If both effective minima are attained on the selected binary
components, Corollary 5.15 supplies either the half-gap bound or the exact
finite-defect identity handled above. -/
theorem selectedBinary_representationAlphaValue_le_zero
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    a.representationAlphaValue b i ≤ 0 := by
  let rLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let rSmall := ordUnit K D.input.block.scaleGenerator
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition rLarge
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition rSmall
  by_cases hlargeStrict : eLarge < ordUnit K
      (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
  · exact D.selectedBinary_representationAlphaValue_le_zero_of_largeNorm_strict
      hselected hfin a b i hposition hlocal hcurrent hlargeStrict
  · by_cases hsmallStrict : eSmall < ordUnit K
        (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition)
    · exact D.selectedBinary_representationAlphaValue_le_zero_of_smallNorm_strict
        hselected hfin a b i hposition hlocal hcurrent hsmallStrict
    · have hlargeLe : eLarge ≤ ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) := by
        simpa only [eLarge, rLarge,
          D.largeAlmostJordan_scaleGenerator_selected] using
          D.largeAlmostJordan.effectiveNormOrderAt_scale_le_normOrder
            D.largeSelectedPosition
      have hsmallLe : eSmall ≤ ordUnit K
          (D.smallAlmostJordan.normGeneratorUnit
            D.smallSelectedPosition) := by
        simpa only [eSmall, rSmall,
          D.smallAlmostJordan_scaleGenerator_selected] using
          D.smallAlmostJordan.effectiveNormOrderAt_scale_le_normOrder
            D.smallSelectedPosition
      have hlargeEq : ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) = eLarge :=
        le_antisymm (le_of_not_gt hlargeStrict) hlargeLe
      have hsmallEq : ordUnit K
          (D.smallAlmostJordan.normGeneratorUnit
            D.smallSelectedPosition) = eSmall :=
        le_antisymm (le_of_not_gt hsmallStrict) hsmallLe
      let I : Fin (n + 2) :=
        (BONG.GoodBONG.representationAlphaIndex i).castSucc
      have horders := D.weakAligned_selected_current_orders
        hselected a b I hposition hlocal
      have hjump : eSmall = eLarge + 1 := by
        change b.order I = a.order I + 1 at hcurrent
        simpa only [eLarge, eSmall, rLarge, rSmall,
          horders.1, horders.2] using hcurrent
      have hnormSucc : ordUnit K
          (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition) =
        ordUnit K
          (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) + 1 := by
        rw [hsmallEq, hlargeEq]
        exact hjump
      obtain ⟨B, _hBOrder, hBGap, hcor⟩ :=
        D.selectedBinary_corollary515 hfin hnormSucc
      have hBGapEffective : B.binaryOrderGap =
          2 * rLarge - 2 * eLarge := by
        rw [hBGap, hlargeEq]
      rcases hcor with hhalf | ⟨hfinite, hdefectEq⟩
      · apply D.selectedBinary_representationAlphaValue_le_zero_of_half
          hselected hfin a b i hposition hlocal hcurrent
        rw [hBGapEffective] at hhalf
        simpa only [rLarge, eLarge] using hhalf
      · exact D.selectedBinary_representationAlphaValue_le_zero_of_defect
          hselected hfin a b i hposition hlocal hcurrent B
            (by simpa only [rLarge, eLarge] using hBGapEffective)
            hfinite hdefectEq

/-- At the final boundary of an aligned selected binary component, a
one-step rise of the target order gives the `odd` Section 5 certificate.
Lemma 5.13 supplies the prefix-sum identity, while the preceding theorem
closes all three local subcases needed for the nonpositive alpha bound. -/
theorem weakAligned_selectedBinary_oddCertificate
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 =
        D.largeSelectedPosition)
    (hlocal : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).2.val = 0)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let localData := D.weakAligned_lemma513LocalData hselected a b
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.odd
  · apply localData.prefixSum_succ_of_current_succ i hi
    have hbound : i.val - 1 < n + 2 :=
      (Nat.sub_le _ _).trans_lt i.lt_large
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hbound,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hbound]
    simp only [BONG.GoodBONG.orderSequence_at]
    have hindex :
        (⟨i.val - 1, hbound⟩ : Fin (n + 2)) =
          (BONG.GoodBONG.representationAlphaIndex i).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hcurrent
  · rw [← a.coe_representationAlphaValue b i]
    exact_mod_cast D.selectedBinary_representationAlphaValue_le_zero
      hselected hfin a b i hposition hlocal hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
