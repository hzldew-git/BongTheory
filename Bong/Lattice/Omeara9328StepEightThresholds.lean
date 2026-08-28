/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightDeterminants

/-!
# Representation thresholds in O'Meara 93:28, Step 8

At every raised old index the ideal `4 a w⁻¹` is unchanged.  At the
inserted index it is contained in the old first threshold.  The latter is
the precise comparison needed to reduce both new left-boundary clauses to
the original condition 93:28(iii).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  (J : JordanDecomposition q L (n + 2))

/-- The coherent Step-8 choice leaves every old representation threshold
unchanged at its raised index. -/
theorem stepEight_fourNormOverWeightIdealWith_old
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (i : Fin (n + 2)) :
    (J.stepEightJordan hgap).fourNormOverWeightIdealWith
        (J.stepEightFundamentalNormGeneratorChoice A hJ hgap
          hnormGap hfirst)
        ((1 : Fin (n + 3)).succAbove i) =
      J.fourNormOverWeightIdealWith A i := by
  unfold fourNormOverWeightIdealWith
  rw [J.stepEightFundamentalNormGeneratorChoice_old A hJ hgap
      hnormGap hfirst,
    J.stepEightJordan_fundamentalWeightOrder_old hgap]

/-- The inserted fundamental weight can rise by at most two valuation
steps from the old first weight.  This is the dual inequality of 93:25. -/
theorem stepEight_insertedWeightOrder_le_first_add_two
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    (J.stepEightJordan hgap).fundamentalWeightOrder 1 ≤
      J.fundamentalWeightOrder 0 + 2 := by
  let J₈ := J.stepEightJordan hgap
  have hidx : (0 : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp
  have hnormZero : ordUnit K (J₈.fundamentalNormGenerator 0) =
      ordUnit K (J.fundamentalNormGenerator 0) := by
    rw [hidx]
    exact J.stepEightJordan_fundamentalNormGenerator_order_old hgap 0
  have hnormOne : ordUnit K (J₈.fundamentalNormGenerator 1) =
      ordUnit K (J.fundamentalNormGenerator 0) + 2 :=
    J.stepEightJordan_fundamentalNormGenerator_order_inserted
      hJ hgap hnormGap hfirst
  have heven : Even
      (ordUnit K (J₈.fundamentalNormGenerator 1) -
        ordUnit K (J₈.fundamentalNormGenerator 0)) := by
    rw [hnormZero, hnormOne]
    exact ⟨1, by omega⟩
  have hdual :=
    J₈.fundamentalWeightOrder_sub_two_scale_anti_of_even_normOrderGap
      (i := (0 : Fin (n + 3))) (j := (1 : Fin (n + 3))) (by simp) heven
  have hscaleZero : J₈.fundamentalScaleOrder 0 =
      J.fundamentalScaleOrder 0 := by
    unfold fundamentalScaleOrder
    rw [J.stepEightJordan_scaleGenerator, J.stepEightScaleGenerator_zero]
  have hscaleOne : J₈.fundamentalScaleOrder 1 =
      J.fundamentalScaleOrder 0 + 1 :=
    J.stepEightJordan_fundamentalScaleOrder_inserted hgap
  have hweightZero : J₈.fundamentalWeightOrder 0 =
      J.fundamentalWeightOrder 0 := by
    rw [hidx]
    exact J.stepEightJordan_fundamentalWeightOrder_old hgap 0
  rw [hscaleZero, hscaleOne, hweightZero] at hdual
  change J₈.fundamentalWeightOrder 1 ≤
    J.fundamentalWeightOrder 0 + 2
  omega

/-- The inserted threshold `4(π²a₀)w⁻¹` is contained in the old
first threshold `4a₀w₀⁻¹`. -/
theorem stepEight_fourNormOverWeightIdealWith_inserted_le_first
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    (J.stepEightJordan hgap).fourNormOverWeightIdealWith
        (J.stepEightFundamentalNormGeneratorChoice A hJ hgap
          hnormGap hfirst) 1 ≤
      J.fourNormOverWeightIdealWith A 0 := by
  unfold fourNormOverWeightIdealWith
  rw [powerIdeal_le_iff,
    J.stepEightFundamentalNormGeneratorChoice_inserted A hJ hgap
      hnormGap hfirst,
    J.stepEightRaisedNormGeneratorWith_order]
  have hweight := J.stepEight_insertedWeightOrder_le_first_add_two
    hJ hgap hnormGap hfirst
  omega

end Lattice.JordanDecomposition

end Bong
