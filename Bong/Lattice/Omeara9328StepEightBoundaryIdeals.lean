/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightInvariants
import Bong.Lattice.Omeara9327FundamentalIdeal
import Bong.Lattice.ProductDefectRescale

/-!
# Boundary ideals in O'Meara 93:28, Step 8

The old first boundary is replaced by two boundaries after inserting the
scaled hyperbolic plane.  This file proves O'Meara's two containments

`f₀ ⊆ f₀'` and `f₀ ⊆ f₁'`.

The first is ordinary monotonicity of product-defect sums.  The second uses
the square-scaled norm-group inclusion from 93:25 and the exact covariance
of absolute quadratic defects under multiplication by a square.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace JordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  (J : JordanDecomposition q L (n + 2))

/-- The old first product-defect sum is contained in the product-defect sum
at the first new boundary. -/
theorem stepEight_boundaryProductDefect_first_le
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    J.boundaryProductDefectSum 0 ≤
      (J.stepEightJordan hscaleGap).boundaryProductDefectSum 0 := by
  unfold boundaryProductDefectSum
  apply productDefectSum_mono
  · intro z hz
    have hidx : (0 : Fin (n + 3)) =
        (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    change z ∈ (J.stepEightJordan hscaleGap).fundamentalNormGroup 0
    rw [hidx, J.stepEightJordan_fundamentalNormGroup_old]
    exact hz
  · intro z hz
    have hanti :
        (J.stepEightJordan hscaleGap).fundamentalNormGroup
            (boundaryRightIndex (1 : Fin (n + 2))) ⊆
          (J.stepEightJordan hscaleGap).fundamentalNormGroup
            (boundaryLeftIndex (1 : Fin (n + 2))) :=
      (J.stepEightJordan hscaleGap).fundamentalNormGroup_anti
        (boundaryLeftIndex_le_rightIndex (1 : Fin (n + 2)))
    have hidx : (2 : Fin (n + 3)) =
        (1 : Fin (n + 3)).succAbove (1 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    change z ∈ (J.stepEightJordan hscaleGap).fundamentalNormGroup
      (boundaryLeftIndex (1 : Fin (n + 2)))
    apply hanti
    change z ∈ (J.stepEightJordan hscaleGap).fundamentalNormGroup 2
    rw [hidx, J.stepEightJordan_fundamentalNormGroup_old]
    exact hz

/-- At the second new boundary, the norm-order sum is the old first sum
raised by two. -/
theorem stepEight_boundaryNormOrderSum_second_eq
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    (J.stepEightJordan hscaleGap).boundaryNormOrderSum 1 =
      J.boundaryNormOrderSum 0 + 2 := by
  have hright : ordUnit K
      ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 2) =
      ordUnit K (J.fundamentalNormGenerator 1) := by
    have hidx : (2 : Fin (n + 3)) =
        (1 : Fin (n + 3)).succAbove (1 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    rw [hidx]
    exact J.stepEightJordan_fundamentalNormGenerator_order_old
      hscaleGap (1 : Fin (n + 2))
  have hnew := J.stepEightJordan_fundamentalNormGenerator_order_inserted
    hJ hscaleGap hnormGap hfirst
  unfold boundaryNormOrderSum
  change
    ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1) +
        ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 2) =
      (ordUnit K (J.fundamentalNormGenerator 0) +
        ordUnit K (J.fundamentalNormGenerator 1)) + 2
  rw [hnew, hright]
  omega

/-- The old first product-defect summand, multiplied by `pi²`, is
contained in the product-defect summand at the second new boundary. -/
theorem stepEight_boundaryProductDefect_second_scaled_le
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    scalarIdeal (((uniformizerUnit K) ^ 2 : Kˣ) : K)
        (J.boundaryProductDefectSum 0) ≤
      (J.stepEightJordan hscaleGap).boundaryProductDefectSum 1 := by
  have hright :
      (J.stepEightJordan hscaleGap).fundamentalNormGroup 2 =
        J.fundamentalNormGroup 1 := by
    have hidx : (2 : Fin (n + 3)) =
        (1 : Fin (n + 3)).succAbove (1 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    rw [hidx, J.stepEightJordan_fundamentalNormGroup_old]
  unfold boundaryProductDefectSum
  change scalarIdeal (((uniformizerUnit K) ^ 2 : Kˣ) : K)
      (productDefectSum (J.fundamentalNormGroup 0)
        (J.fundamentalNormGroup 1)) ≤
    productDefectSum
      ((J.stepEightJordan hscaleGap).fundamentalNormGroup 1)
      ((J.stepEightJordan hscaleGap).fundamentalNormGroup 2)
  rw [hright]
  exact scalarIdeal_productDefectSum_le_of_sq_mul_subset
    (uniformizerUnit K)
    (fun _ hz => J.stepEightJordan_sq_uniformizer_mem_insertedNormGroup
      hscaleGap hz)

/-- The old parity summand, multiplied by `pi²`, is exactly no larger
than the parity summand at the second new boundary. -/
theorem stepEight_boundaryParityIdeal_second_scaled_le
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (heven : Even (J.boundaryNormOrderSum 0)) :
    scalarIdeal (((uniformizerUnit K) ^ 2 : Kˣ) : K)
        (J.boundaryParityIdeal 0) ≤
      (J.stepEightJordan hscaleGap).boundaryParityIdeal 1 := by
  have hsum := J.stepEight_boundaryNormOrderSum_second_eq hJ hscaleGap
    hnormGap hfirst
  have hscale := J.stepEightJordan_fundamentalScaleOrder_inserted hscaleGap
  unfold boundaryParityIdeal
  rw [twiceIdeal_powerIdeal, twiceIdeal_powerIdeal]
  change scalarIdeal (((uniformizerUnit K) ^ 2 : Kˣ) : K)
      (powerIdeal (K := K)
        (J.boundaryNormOrderSum 0 / 2 +
          J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))) ≤
    powerIdeal (K := K)
      ((J.stepEightJordan hscaleGap).boundaryNormOrderSum 1 / 2 +
        (J.stepEightJordan hscaleGap).fundamentalScaleOrder 1 +
        (ramificationIndex K : Int))
  rw [scalarIdeal_powerIdeal_units, powerIdeal_le_iff, hsum, hscale,
    ordUnit_pow]
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    norm_num
  rw [hpi]
  rcases heven with ⟨m, hm⟩
  omega

/-- After multiplying by `pi²`, the old first scaled fundamental ideal is
contained in the scaled ideal at the second new boundary. -/
theorem stepEight_scaledFundamentalIdeal_first_scaled_le_second
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    scalarIdeal (((uniformizerUnit K) ^ 2 : Kˣ) : K)
        (J.scaledFundamentalIdeal 0) ≤
      (J.stepEightJordan hscaleGap).scaledFundamentalIdeal 1 := by
  have hsum := J.stepEight_boundaryNormOrderSum_second_eq hJ hscaleGap
    hnormGap hfirst
  have heven_iff :
      Even ((J.stepEightJordan hscaleGap).boundaryNormOrderSum 1) ↔
        Even (J.boundaryNormOrderSum 0) := by
    rw [hsum]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      omega
    · rintro ⟨m, hm⟩
      refine ⟨m + 1, ?_⟩
      omega
  unfold scaledFundamentalIdeal
  by_cases holdEven : Even (J.boundaryNormOrderSum 0)
  · rw [if_pos holdEven, if_pos (heven_iff.mpr holdEven)]
    exact scalarIdeal_sup_le
      (((uniformizerUnit K) ^ 2 : Kˣ) : K) _ _ _
      (J.stepEight_boundaryProductDefect_second_scaled_le hscaleGap |>.trans
        _root_.le_sup_left)
      (J.stepEight_boundaryParityIdeal_second_scaled_le hJ hscaleGap
        hnormGap hfirst holdEven |>.trans _root_.le_sup_right)
  · have hnewNotEven :
        ¬ Even ((J.stepEightJordan hscaleGap).boundaryNormOrderSum 1) :=
      fun h ↦ holdEven (heven_iff.mp h)
    rw [if_neg holdEven, if_neg hnewNotEven]
    exact J.stepEight_boundaryProductDefect_second_scaled_le hscaleGap

/-- Second containment on O'Meara p. 276: the original first fundamental
ideal is contained in the boundary ideal between the inserted plane and the
old second component. -/
theorem stepEight_fundamentalIdeal_first_le_second
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    J.fundamentalIdeal 0 ≤
      (J.stepEightJordan hscaleGap).fundamentalIdeal 1 := by
  let c : Kˣ := uniformizerUnit K
  have hscaled := J.stepEight_scaledFundamentalIdeal_first_scaled_le_second
    hJ hscaleGap hnormGap hfirst
  unfold fundamentalIdeal
  change scalarIdeal (((J.scaleGenerator 0)⁻¹ ^ 2 : Kˣ) : K)
      (J.scaledFundamentalIdeal 0) ≤
    scalarIdeal
      ((((J.stepEightJordan hscaleGap).scaleGenerator 1)⁻¹ ^ 2 : Kˣ) : K)
      ((J.stepEightJordan hscaleGap).scaledFundamentalIdeal 1)
  rw [J.stepEightJordan_scaleGenerator, J.stepEightScaleGenerator_inserted]
  have hmapped :
      scalarIdeal (((J.stepEightScale)⁻¹ ^ 2 : Kˣ) : K)
          (scalarIdeal (((c ^ 2 : Kˣ) : K))
            (J.scaledFundamentalIdeal 0)) ≤
        scalarIdeal (((J.stepEightScale)⁻¹ ^ 2 : Kˣ) : K)
          ((J.stepEightJordan hscaleGap).scaledFundamentalIdeal 1) :=
    Submodule.map_mono hscaled
  rw [scalarIdeal_scalarIdeal_eq] at hmapped
  have hcoeffUnit :
      (J.stepEightScale)⁻¹ ^ 2 * c ^ 2 =
        (J.scaleGenerator 0)⁻¹ ^ 2 := by
    dsimp only [c]
    unfold stepEightScale
    simp [mul_pow, mul_comm]
  have hcoeff :
      (((J.stepEightScale)⁻¹ ^ 2 : Kˣ) : K) *
          (((c ^ 2 : Kˣ) : K)) =
        (((J.scaleGenerator 0)⁻¹ ^ 2 : Kˣ) : K) := by
    exact congrArg Units.val hcoeffUnit
  rw [hcoeff] at hmapped
  exact hmapped

/-- The old parity summand is contained in the first new parity summand. -/
theorem stepEight_boundaryParityIdeal_first_le
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (heven : Even (J.boundaryNormOrderSum 0)) :
    J.boundaryParityIdeal 0 ≤
      (J.stepEightJordan hscaleGap).boundaryParityIdeal 0 := by
  have hzero : ordUnit K
      ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 0) =
      ordUnit K (J.fundamentalNormGenerator 0) := by
    have hidx : (0 : Fin (n + 3)) =
        (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
      apply Fin.ext
      simp
    rw [hidx]
    exact J.stepEightJordan_fundamentalNormGenerator_order_old
      hscaleGap (0 : Fin (n + 2))
  unfold boundaryParityIdeal
  rw [twiceIdeal_powerIdeal, twiceIdeal_powerIdeal, powerIdeal_le_iff]
  have hnewNorm := J.stepEightJordan_fundamentalNormGenerator_order_inserted
    hJ hscaleGap hnormGap hfirst
  have hnewScale := J.stepEightJordan_fundamentalScaleOrder_inserted hscaleGap
  simp only [boundaryNormOrderSum, boundaryLeftIndex, boundaryRightIndex]
  change
    (ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 0) +
          ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1)) /
        2 +
        (J.stepEightJordan hscaleGap).fundamentalScaleOrder 0 +
        (ramificationIndex K : Int) ≤
      (ordUnit K (J.fundamentalNormGenerator 0) +
          ordUnit K (J.fundamentalNormGenerator 1)) /
        2 + J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)
  rw [hzero, hnewNorm]
  have hscaleZero :
      (J.stepEightJordan hscaleGap).fundamentalScaleOrder 0 =
        J.fundamentalScaleOrder 0 := by
    unfold fundamentalScaleOrder
    rw [J.stepEightJordan_scaleGenerator, J.stepEightScaleGenerator_zero]
  rw [hscaleZero]
  change Even (ordUnit K (J.fundamentalNormGenerator 0) +
    ordUnit K (J.fundamentalNormGenerator 1)) at heven
  rcases heven with ⟨m, hm⟩
  omega

/-- First containment on O'Meara p. 276: the original first fundamental
ideal is contained in the first boundary ideal after Step-8 insertion. -/
theorem stepEight_fundamentalIdeal_first_le_first
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    J.fundamentalIdeal 0 ≤
      (J.stepEightJordan hscaleGap).fundamentalIdeal 0 := by
  have hnewEven : Even
      ((J.stepEightJordan hscaleGap).boundaryNormOrderSum 0) := by
    have hzero : ordUnit K
        ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 0) =
        ordUnit K (J.fundamentalNormGenerator 0) := by
      have hidx : (0 : Fin (n + 3)) =
          (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
        apply Fin.ext
        simp
      rw [hidx]
      exact J.stepEightJordan_fundamentalNormGenerator_order_old
        hscaleGap (0 : Fin (n + 2))
    have hnewNorm :=
      J.stepEightJordan_fundamentalNormGenerator_order_inserted
        hJ hscaleGap hnormGap hfirst
    simp only [boundaryNormOrderSum, boundaryLeftIndex, boundaryRightIndex]
    change Even
      (ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 0) +
        ordUnit K ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1))
    rw [hzero, hnewNorm]
    refine ⟨ordUnit K (J.fundamentalNormGenerator 0) + 1, ?_⟩
    omega
  have hscaled : J.scaledFundamentalIdeal 0 ≤
      (J.stepEightJordan hscaleGap).scaledFundamentalIdeal 0 := by
    unfold scaledFundamentalIdeal
    rw [if_pos hnewEven]
    by_cases holdEven : Even (J.boundaryNormOrderSum 0)
    · rw [if_pos holdEven]
      exact _root_.sup_le
        ((J.stepEight_boundaryProductDefect_first_le hscaleGap).trans
          _root_.le_sup_left)
        (J.stepEight_boundaryParityIdeal_first_le hJ hscaleGap hnormGap
          hfirst holdEven |>.trans _root_.le_sup_right)
    · rw [if_neg holdEven]
      exact (J.stepEight_boundaryProductDefect_first_le hscaleGap).trans
        _root_.le_sup_left
  unfold fundamentalIdeal
  simp only [boundaryLeftIndex]
  change scalarIdeal
      (((J.scaleGenerator 0)⁻¹ ^ 2 : Kˣ) : K)
      (J.scaledFundamentalIdeal 0) ≤
    scalarIdeal
      (((J.stepEightScaleGenerator 0)⁻¹ ^ 2 : Kˣ) : K)
      ((J.stepEightJordan hscaleGap).scaledFundamentalIdeal 0)
  rw [J.stepEightScaleGenerator_zero]
  exact Submodule.map_mono hscaled

end JordanDecomposition

end Lattice

end Bong
