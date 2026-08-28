/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveDefectReverse
import Bong.Bong.Beli2009LatticeSumSpecialization
import Bong.Lattice.DVRFactorization

/-!
# The effective-norm gap-two branch in Beli (2019), Section 5

This file implements the application of Beli (2009), Lemma 2.11 in the proof
of Beli (2019), Lemma 5.13(i).  Before the selected Jordan component, the
larger fundamental lattice is a one-uniformizer enlargement of the smaller
one.  In the effective-norm gap-two case their weight ideals therefore agree.
-/

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The vector adjoined in Lemma 5.1 belongs to every large fundamental
lattice whose component occurs before the selected component. -/
theorem enlargedVector_mem_largeFundamental_before_selected
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
      (D.largeNoCollisionJordan hlarge).fundamentalLattice p := by
  let H := D.largeNoCollisionJordan hlarge
  let r := ordUnit K (H.scaleGenerator p)
  have hscale : r ≤ ordUnit K (H.scaleGenerator D.largeSelectedPosition) :=
    (H.scaleOrder_strict hp).le
  have hfactor : H.scaleTruncationFactor r D.largeSelectedPosition = 1 :=
    H.scaleTruncationFactor_eq_one_of_le r D.largeSelectedPosition hscale
  let T := H.scaleTruncationDecomposition r
  have hcomponent : T.component D.largeSelectedPosition =
      H.component D.largeSelectedPosition := by
    rw [H.scaleTruncationDecomposition_component, hfactor]
    cases H.component D.largeSelectedPosition
    simp [QuadraticSublattice.rescaleLattice, Lattice.rescale_one]
  have hyEnlarged :
      ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
        D.input.enlargedComponent.ambientSubmodule :=
    ⟨D.input.enlargedVector, Lattice.mem_adjoinVector _ _, rfl⟩
  have hySelected :
      ((D.input.enlargedVector : D.input.block.component.carrier) : V) ∈
        (H.component D.largeSelectedPosition).ambientSubmodule := by
    simpa only [H, largeNoCollisionJordan,
      Lattice.WeakJordanDecomposition.toJordan_component,
      D.largeAlmostJordan_component_selected] using hyEnlarged
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
      (ordUnit K ((D.largeNoCollisionJordan hlarge).scaleGenerator p))).toSubmodule
  simpa only [H, r, T] using hyTrunc

/-- At a common scale before the selected component, the larger fundamental
lattice is obtained by adjoining the Lemma 5.1 enlarged vector to the
smaller fundamental lattice. -/
theorem adjoin_enlargedVector_smallFundamental_eq_largeFundamental
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition)
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p)) :
    Lattice.adjoinVector
        ((D.smallNoCollisionJordan hsmall).fundamentalLattice p)
        (((D.input.enlargedVector :
          D.input.block.component.carrier) : V)) =
      (D.largeNoCollisionJordan hlarge).fundamentalLattice p := by
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  let r := ordUnit K (H.scaleGenerator p)
  let y : V := ((D.input.enlargedVector :
    D.input.block.component.carrier) : V)
  have hscaleHJ : H.fundamentalScaleOrder p =
      J.fundamentalScaleOrder p := by
    simpa only [H, J, largeNoCollisionJordan, smallNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator] using hscale
  have hbound : H.fundamentalScaleOrder p ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hs := (H.scaleOrder_strict hp).le
    simpa only [H, largeNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      D.largeAlmostJordan_scaleGenerator_selected] using hs
  have hsmallLarge : J.fundamentalLattice p ≤
      H.fundamentalLattice p :=
    D.smallFundamentalLattice_le_large_of_scale_le p p
      hscaleHJ.le hbound
  have hyLarge : y ∈ H.fundamentalLattice p := by
    simpa only [y, H] using
      D.enlargedVector_mem_largeFundamental_before_selected hlarge p hp
  apply Lattice.ext
  apply le_antisymm
  · exact Lattice.adjoinVector_le hsmallLarge hyLarge
  · intro z hz
    have hzM : z ∈ M := by
      have hz' := (Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mp hz).1
      exact hz'
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
    have hcyLarge : c • y ∈ H.fundamentalLattice p :=
      (H.fundamentalLattice p).smul_mem c hyLarge
    have hnEq : n = z - c • y := by
      rw [← hsum]
      abel
    have hnLarge : n ∈ H.fundamentalLattice p := by
      rw [hnEq]
      exact (H.fundamentalLattice p).sub_mem hz hcyLarge
    have hnData := Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mp hnLarge
    have hnSmall : n ∈ J.fundamentalLattice p := by
      apply Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mpr
      constructor
      · exact hn
      · intro w hw
        rw [← hscaleHJ]
        exact hnData.2 w (D.smallLattice_le_large hw)
    rw [← hsum]
    have hyAdj : y ∈ Lattice.adjoinVector (J.fundamentalLattice p) y :=
      Lattice.mem_adjoinVector _ _
    exact (Lattice.adjoinVector (J.fundamentalLattice p) y).add_mem
      (Lattice.le_adjoinVector _ _ hnSmall)
      ((Lattice.adjoinVector (J.fundamentalLattice p) y).smul_mem c hyAdj)

/-- Multiplication by the uniformizer sends the large fundamental lattice
at a common scale into the corresponding small fundamental lattice. -/
theorem uniformizer_smul_mem_smallFundamental_of_mem_large
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p))
    {x : V} (hx : x ∈
      (D.largeNoCollisionJordan hlarge).fundamentalLattice p) :
    (uniformizerInteger K) • x ∈
      (D.smallNoCollisionJordan hsmall).fundamentalLattice p := by
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  have hscaleHJ : H.fundamentalScaleOrder p =
      J.fundamentalScaleOrder p := by
    simpa only [H, J, largeNoCollisionJordan, smallNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator] using hscale
  have hxData := Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mp hx
  have hpiRescale : (uniformizer K) • x ∈
      Lattice.rescale (uniformizerUnit K) M := by
    exact Lattice.smul_mem_rescale (uniformizerUnit K) M hxData.1
  have hpiNField : (uniformizer K) • x ∈ N :=
    D.uniformizer_largeLattice_le_small hpiRescale
  have hpiN : (uniformizerInteger K) • x ∈ N := by
    change (uniformizer K) • x ∈ N
    exact hpiNField
  apply Lattice.mem_scaleTruncation_iff_ord_bilin_ge.mpr
  constructor
  · exact hpiN
  · intro z hz
    rw [← hscaleHJ]
    have hpair := hxData.2 z (D.smallLattice_le_large hz)
    have hscalar :
        algebraMap (IntegerRing K) K (uniformizerInteger K) =
          uniformizer K := rfl
    change (H.fundamentalScaleOrder p : WithTop Int) ≤
      ord K (q.bilin ((uniformizerInteger K) • x) z)
    rw [← IsScalarTower.algebraMap_smul K (uniformizerInteger K) x,
      LinearMap.BilinForm.smul_left, hscalar, ord_mul,
      ord_uniformizer]
    have hzeroOne : ((0 : Int) : WithTop Int) ≤
        ((1 : Int) : WithTop Int) := by norm_num
    have hadd := add_le_add_right hzeroOne (ord K (q.bilin x z))
    have hord : ord K (q.bilin x z) ≤
        ((1 : Int) : WithTop Int) + ord K (q.bilin x z) := by
      simpa [add_comm] using hadd
    exact hpair.trans hord

/-- In the effective-norm gap-two branch before the selected component, the
two intrinsic fundamental lattices have the same weight ideal. -/
theorem noCollision_fundamentalWeightIdeal_eq_of_effective_gapTwo
    [Beli2009WeightIdealData.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition)
    (hscale : ordUnit K (D.largeAlmostJordan.scaleGenerator p) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p))
    (heffective :
      D.smallAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) =
        D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2) :
    Lattice.weightIdeal q
        ((D.largeNoCollisionJordan hlarge).fundamentalLattice p) =
      Lattice.weightIdeal q
        ((D.smallNoCollisionJordan hsmall).fundamentalLattice p) := by
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  let A := D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition
  have hpair := D.noCollision_gapTwo_normGenerator_pair
    hsmall hlarge p hp hscale heffective
  change Lattice.IsNormGeneratorValue q (H.fundamentalLattice p) A ∧
      Lattice.IsNormGeneratorValue q (J.fundamentalLattice p)
        ((uniformizerUnit K) ^ 2 * A) at hpair
  have hpos : 0 < Module.finrank K V :=
    Lattice.finrank_pos_of_isNormGeneratorValue hpair.1
  obtain ⟨x, hx, hxanis⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos q
      (H.fundamentalLattice p) hpos
  let X : Kˣ := Units.mk0 (q.quadratic x) hxanis
  have hXcoe : (X : K) = q.quadratic x := rfl
  have hprincipalXA :
      Lattice.principalIdeal (K := K) (X : K) =
        Lattice.principalIdeal (K := K) (A : K) := by
    rw [hXcoe]
    exact hx.normIdeal_eq.symm.trans hpair.1.2
  have hXA : ordUnit K X = ordUnit K A :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq X A).mp hprincipalXA
  have hxnot : x ∉ J.fundamentalLattice p := by
    intro hxSmall
    have hqxSmall : q.quadratic x ∈
        Lattice.principalIdeal (K := K)
          ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) := by
      rw [← hpair.2.2]
      exact Lattice.quadratic_mem_normIdeal_of_mem q
        (J.fundamentalLattice p) hxSmall
    have hord := Lattice.ord_le_of_mem_principalIdeal
      (Units.ne_zero ((uniformizerUnit K) ^ 2 * A)) hqxSmall
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
  have hyLarge :=
    D.enlargedVector_mem_largeFundamental_before_selected hlarge p hp
  have hadjoinY :=
    D.adjoin_enlargedVector_smallFundamental_eq_largeFundamental
      hsmall hlarge p hp hscale
  have hpiY :=
    D.uniformizer_smul_mem_smallFundamental_of_mem_large
      hsmall hlarge p hscale hyLarge
  have hadjoinX : Lattice.adjoinVector (J.fundamentalLattice p) x =
      H.fundamentalLattice p := by
    exact Lattice.adjoinVector_eq_of_uniformizer_smul_mem_of_not_mem
      hadjoinY hpiY hx.mem hxnot
  have hpiX : (uniformizerInteger K) • x ∈ J.fundamentalLattice p :=
    D.uniformizer_smul_mem_smallFundamental_of_mem_large
      hsmall hlarge p hscale hx.mem
  have hsmallX : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice p) ((uniformizerUnit K) ^ 2 * X) := by
    constructor
    · refine ⟨(uniformizerInteger K) • x, hpiX, 0,
        Submodule.zero_mem _, ?_⟩
      have hscalar :
          algebraMap (IntegerRing K) K (uniformizerInteger K) =
            uniformizer K := rfl
      rw [add_zero, ← IsScalarTower.algebraMap_smul K
        (uniformizerInteger K) x, q.quadratic_smul, hscalar]
      change ((((uniformizerUnit K) ^ 2 * X : Kˣ) : K)) =
        uniformizer K ^ 2 * q.quadratic x
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, X,
        Units.val_mk0, coe_uniformizerUnit]
    · apply hpair.2.2.trans
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
        ((uniformizerUnit K) ^ 2 * A)
        ((uniformizerUnit K) ^ 2 * X)).2
      simp only [ordUnit_mul, ordUnit_pow, hXA]
  have hscaleHJ : H.fundamentalScaleOrder p =
      J.fundamentalScaleOrder p := by
    simpa only [H, J, largeNoCollisionJordan, smallNoCollisionJordan,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator] using hscale
  have htwo : Lattice.twoScaleIdeal q (J.fundamentalLattice p) =
      Lattice.twoScaleIdeal q (H.fundamentalLattice p) := by
    unfold Lattice.twoScaleIdeal
    congr 1
    calc
      Lattice.scaleIdeal q (J.fundamentalLattice p) =
          Lattice.powerIdeal (K := K) (J.fundamentalScaleOrder p) :=
        J.scaleIdeal_scaleTruncation_at_component p
      _ = Lattice.powerIdeal (K := K) (H.fundamentalScaleOrder p) := by
        rw [hscaleHJ]
      _ = Lattice.scaleIdeal q (H.fundamentalLattice p) :=
        (H.scaleIdeal_scaleTruncation_at_component p).symm
  exact Lattice.weightIdeal_eq_of_adjoin_normGenerator_gapTwo
    hx hxanis hadjoinX hsmallX htwo

end Lattice.Beli2019Lemma51Data

end Bong
