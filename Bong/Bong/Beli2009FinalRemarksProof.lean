/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009FinalRemarks
import Bong.Bong.BeliLemma43MaximalNormProof
import Bong.Bong.GoodBONGPrescribedValues
import Bong.Bong.AlphaValueExt
import Bong.Bong.GoodMap
import Bong.Bong.Beli2019QuaternaryFirstScalingProof
import Bong.Bong.DiagonalLocalClassificationProof

/-!
# Proof of Beli (2009/2010), final remarks

This file discharges the two field-specific assertions isolated in
`Beli2009FinalRemarks`.  The residue-two construction is developed first:
the displayed coefficient families are realized as good BONGs and their
underlying lattices are identified by the already proved Theorem 3.1.  The
remaining non-reachability statement is proved through the binary-move
invariant introduced below.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Beli2009FinalRemarksProof

private theorem mul_div_square_mul
    (a b s : Kˣ) : a * b / (s * s * a) = b * s⁻¹ ^ 2 := by
  rw [div_eq_mul_inv, mul_inv_rev]
  simp only [pow_two]
  calc
    a * b * (a⁻¹ * (s⁻¹ * s⁻¹)) =
        (a * a⁻¹) * b * (s⁻¹ * s⁻¹) := by ac_rfl
    _ = b * (s⁻¹ * s⁻¹) := by simp

private theorem square_mul_mul_div_mul
    (a b s : Kˣ) : s * s * b / (a * b) = a⁻¹ * s * s := by
  rw [div_eq_mul_inv, mul_inv_rev]
  calc
    s * s * b * (b⁻¹ * a⁻¹) =
        (b * b⁻¹) * a⁻¹ * s * s := by ac_rfl
    _ = a⁻¹ * s * s := by simp

private theorem square_mul_mul_div_right
    (a b s : Kˣ) : s * s * a * b / b = a * s * s := by
  rw [div_eq_mul_inv]
  calc
    s * s * a * b * b⁻¹ = (b * b⁻¹) * a * s * s := by ac_rfl
    _ = a * s * s := by simp

private theorem div_square_mul_mul
    (a b s : Kˣ) : a / (s * s * a * b) = b⁻¹ * s⁻¹ ^ 2 := by
  rw [div_eq_mul_inv, mul_inv_rev]
  simp only [pow_two]
  calc
    a * (b⁻¹ * (a⁻¹ * (s⁻¹ * s⁻¹))) =
        (a * a⁻¹) * b⁻¹ * (s⁻¹ * s⁻¹) := by ac_rfl
    _ = b⁻¹ * (s⁻¹ * s⁻¹) := by simp

private theorem square_mul_div
    (a s : Kˣ) : s * s / a = a⁻¹ * s * s := by
  rw [div_eq_mul_inv]
  ac_rfl

private theorem mul_mul_mul_inv_square (a b : Kˣ) :
    a * (b * a) * (a⁻¹ * a⁻¹) = b := by
  calc
    a * (b * a) * (a⁻¹ * a⁻¹) =
        (a * a⁻¹) * (a * a⁻¹) * b := by ac_rfl
    _ = b := by simp

/-- Coordinatewise multiplication of diagonal coefficients by nonzero
squares does not change the represented diagonal space. -/
theorem diagonalRepresents_of_pointwise_mul_square {n : Nat}
    (source target s : Fin n → Kˣ)
    (hcoeff : ∀ i, source i = target i * s i ^ 2) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients source)
      (BONG.GoodBONG.diagonalUnitCoefficients target) := by
  let F : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun x i ↦ (s i : K) * x i
      map_add' := by
        intro x y
        funext i
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c x
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
  refine ⟨F, ?_, ?_⟩
  · intro x y hxy
    funext i
    have hi := congrFun hxy i
    change (s i : K) * x i = (s i : K) * y i at hi
    exact mul_left_cancel₀ (Units.ne_zero (s i)) hi
  · intro x
    unfold diagonalQuadratic BONG.GoodBONG.diagonalUnitCoefficients
    apply Finset.sum_congr rfl
    intro i _hi
    have hfield := congrArg Units.val (hcoeff i)
    change (source i : K) = (target i : K) * (s i : K) ^ 2 at hfield
    change (target i : K) * ((s i : K) * x i) ^ 2 =
      (source i : K) * x i ^ 2
    rw [hfield]
    ring

/-- The order pattern of the first rank-four family is `0,R,0,R`. -/
theorem firstValues_order
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) (i : Fin 4) :
    ordUnit K (beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) =
      ![0, beli2009ResidueTwoOrder (K := K) d,
        0, beli2009ResidueTwoOrder (K := K) d] i := by
  have hepsilon : ordUnit K (epsilon : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (epsilon : Kˣ)).1 epsilon.property
  have heta : ordUnit K (eta : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (eta : Kˣ)).1 eta.property
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  fin_cases i <;>
    simp [beli2009ResidueTwoFirstValues, ordUnit_uniformizerPowerUnit,
      hepsilon, heta, hone]

/-- The second rank-four family has the same order pattern. -/
theorem secondValues_order
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) (i : Fin 4) :
    ordUnit K (beli2009ResidueTwoSecondValues (K := K) d epsilon eta i) =
      ![0, beli2009ResidueTwoOrder (K := K) d,
        0, beli2009ResidueTwoOrder (K := K) d] i := by
  have hepsilon : ordUnit K (epsilon : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (epsilon : Kˣ)).1 epsilon.property
  have heta : ordUnit K (eta : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (eta : Kˣ)).1 eta.property
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simp
  fin_cases i <;>
    simp [beli2009ResidueTwoSecondValues, ordUnit_uniformizerPowerUnit,
      hepsilon, heta, hone]

/-- The uniformizer factor occurring in the example is a square. -/
theorem residueTwo_uniformizerFactor_isSquare (d : Nat) :
    IsSquare (uniformizerPowerUnit K
      (beli2009ResidueTwoOrder (K := K) d)) := by
  let s : Kˣ := uniformizerPowerUnit K
    ((ramificationIndex K : Int) - (d : Int))
  refine ⟨s, ?_⟩
  have hR : beli2009ResidueTwoOrder (K := K) d =
      2 * ((ramificationIndex K : Int) - (d : Int)) := by
    simp only [beli2009ResidueTwoOrder]
    ring
  rw [hR]
  dsimp only [s]
  unfold uniformizerPowerUnit
  rw [← zpow_add]
  congr 1
  ring

/-- The three negative adjacent parameters of the first family have the
defects `d, 2e-d, d`. -/
theorem firstValues_negativeAdjacent_defect
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    quadraticDefect K
        (-(beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.succ /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.castSucc)) =
      ![(d : ℕ∞), (2 * ramificationIndex K - d : ℕ∞),
        (d : ℕ∞)] i := by
  rcases residueTwo_uniformizerFactor_isSquare (K := K) d with ⟨s, hs⟩
  fin_cases i
  · change quadraticDefect K
        (-(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 1 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 0)) =
        (d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 1 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 0) =
            (epsilon : Kˣ) * s ^ 2 := by
      simp [beli2009ResidueTwoFirstValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      ac_rfl
    rw [hparameter, quadraticDefect_mul_square, hepsilon]
  · change quadraticDefect K
        (-(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 2 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 1)) =
        (2 * ramificationIndex K - d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 2 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 1) =
            (eta : Kˣ) * s⁻¹ ^ 2 := by
      simp [beli2009ResidueTwoFirstValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      simpa only [pow_two, mul_inv_rev] using
        mul_div_square_mul (epsilon : Kˣ) (eta : Kˣ) s
    rw [hparameter, quadraticDefect_mul_square, heta]
  · change quadraticDefect K
        (-(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 3 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 2)) =
        (d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoFirstValues (K := K) d epsilon eta 3 /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta 2) =
            (epsilon : Kˣ)⁻¹ * s ^ 2 := by
      simp [beli2009ResidueTwoFirstValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      simpa only [mul_assoc] using
        square_mul_mul_div_mul (epsilon : Kˣ) (eta : Kˣ) s
    rw [hparameter, quadraticDefect_mul_square, quadraticDefect_inv,
      hepsilon]

/-- The second family has the same three adjacent defects. -/
theorem secondValues_negativeAdjacent_defect
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    quadraticDefect K
        (-(beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.succ /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.castSucc)) =
      ![(d : ℕ∞), (2 * ramificationIndex K - d : ℕ∞),
        (d : ℕ∞)] i := by
  rcases residueTwo_uniformizerFactor_isSquare (K := K) d with ⟨s, hs⟩
  fin_cases i
  · change quadraticDefect K
        (-(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 1 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 0)) =
        (d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 1 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 0) =
            (epsilon : Kˣ) * s ^ 2 := by
      simp [beli2009ResidueTwoSecondValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      simpa only [mul_assoc] using
        square_mul_mul_div_right (epsilon : Kˣ) (eta : Kˣ) s
    rw [hparameter, quadraticDefect_mul_square, hepsilon]
  · change quadraticDefect K
        (-(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 2 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 1)) =
        (2 * ramificationIndex K - d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 2 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 1) =
            (eta : Kˣ)⁻¹ * s⁻¹ ^ 2 := by
      simp [beli2009ResidueTwoSecondValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      simpa only [pow_two, mul_inv_rev] using
        div_square_mul_mul (epsilon : Kˣ) (eta : Kˣ) s
    rw [hparameter, quadraticDefect_mul_square, quadraticDefect_inv,
      heta]
  · change quadraticDefect K
        (-(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 3 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 2)) =
        (d : ℕ∞)
    have hparameter :
        -(beli2009ResidueTwoSecondValues (K := K) d epsilon eta 3 /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta 2) =
            (epsilon : Kˣ)⁻¹ * s ^ 2 := by
      simp [beli2009ResidueTwoSecondValues]
      rw [hs]
      simp only [pow_two, div_neg, neg_div, neg_neg]
      simpa only [mul_assoc] using square_mul_div (epsilon : Kˣ) s
    rw [hparameter, quadraticDefect_mul_square, quadraticDefect_inv,
      hepsilon]

/-- Consecutive ratios in the first family have orders `R,-R,R`. -/
theorem firstValues_adjacentRatio_order
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) (i : Fin 3) :
    ordUnit K
        (beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.succ /
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.castSucc) =
      ![beli2009ResidueTwoOrder (K := K) d,
        -beli2009ResidueTwoOrder (K := K) d,
        beli2009ResidueTwoOrder (K := K) d] i := by
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    firstValues_order, firstValues_order]
  fin_cases i <;> simp

/-- Consecutive ratios in the second family have the same orders. -/
theorem secondValues_adjacentRatio_order
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) (i : Fin 3) :
    ordUnit K
        (beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.succ /
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.castSucc) =
      ![beli2009ResidueTwoOrder (K := K) d,
        -beli2009ResidueTwoOrder (K := K) d,
        beli2009ResidueTwoOrder (K := K) d] i := by
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    secondValues_order, secondValues_order]
  fin_cases i <;> simp

private theorem outer_absoluteThreshold_le
    (d : Nat) (hdlt : d < 2 * ramificationIndex K) :
    Int.toNat (-beli2009ResidueTwoOrder (K := K) d) ≤ d := by
  unfold beli2009ResidueTwoOrder
  omega

private theorem middle_absoluteThreshold_le
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K) :
    Int.toNat (beli2009ResidueTwoOrder (K := K) d) ≤
      2 * ramificationIndex K - d := by
  unfold beli2009ResidueTwoOrder
  omega

/-- Every adjacent binary parameter in the first family is admissible. -/
theorem firstValues_adjacentAdmissible
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    BONG.IsBinaryParameterAdmissible
      (beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.succ /
        beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.castSucc) := by
  apply (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect _).2
  constructor
  · rw [firstValues_adjacentRatio_order]
    fin_cases i <;> simp [beli2009ResidueTwoOrder] <;> omega
  · rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le]
    unfold absoluteDefectThreshold
    rw [ordUnit_neg, firstValues_adjacentRatio_order,
      firstValues_negativeAdjacent_defect d epsilon eta hepsilon heta]
    fin_cases i
    · change (Int.toNat (-beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
        (d : ℕ∞)
      exact_mod_cast outer_absoluteThreshold_le (K := K) d hdlt
    · change (Int.toNat (-(-beli2009ResidueTwoOrder (K := K) d)) : ℕ∞) ≤
        (2 * ramificationIndex K - d : ℕ∞)
      simpa only [neg_neg] using (show
        (Int.toNat (beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
          (2 * ramificationIndex K - d : ℕ∞) by
        exact_mod_cast middle_absoluteThreshold_le (K := K) d hdpos hdlt)
    · change (Int.toNat (-beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
        (d : ℕ∞)
      exact_mod_cast outer_absoluteThreshold_le (K := K) d hdlt

/-- Every adjacent binary parameter in the second family is admissible. -/
theorem secondValues_adjacentAdmissible
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    BONG.IsBinaryParameterAdmissible
      (beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.succ /
        beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.castSucc) := by
  apply (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect _).2
  constructor
  · rw [secondValues_adjacentRatio_order]
    fin_cases i <;> simp [beli2009ResidueTwoOrder] <;> omega
  · rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le]
    unfold absoluteDefectThreshold
    rw [ordUnit_neg, secondValues_adjacentRatio_order,
      secondValues_negativeAdjacent_defect d epsilon eta hepsilon heta]
    fin_cases i
    · change (Int.toNat (-beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
        (d : ℕ∞)
      exact_mod_cast outer_absoluteThreshold_le (K := K) d hdlt
    · change (Int.toNat (-(-beli2009ResidueTwoOrder (K := K) d)) : ℕ∞) ≤
        (2 * ramificationIndex K - d : ℕ∞)
      simpa only [neg_neg] using (show
        (Int.toNat (beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
          (2 * ramificationIndex K - d : ℕ∞) by
        exact_mod_cast middle_absoluteThreshold_le (K := K) d hdpos hdlt)
    · change (Int.toNat (-beli2009ResidueTwoOrder (K := K) d) : ℕ∞) ≤
        (d : ℕ∞)
      exact_mod_cast outer_absoluteThreshold_le (K := K) d hdlt

/-- The two-step order inequalities required by goodness hold with equality
in the first family. -/
theorem firstValues_weakTwoStep
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) :
    BONG.CoefficientWeakTwoStep (K := K)
      (beli2009ResidueTwoFirstValues (K := K) d epsilon eta) := by
  intro i hi
  rw [firstValues_order, firstValues_order]
  fin_cases i <;> simp at hi ⊢ <;> omega

theorem secondValues_weakTwoStep
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) :
    BONG.CoefficientWeakTwoStep (K := K)
      (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) := by
  intro i hi
  rw [secondValues_order, secondValues_order]
  fin_cases i <;> simp at hi ⊢ <;> omega

/-- Package the indexed adjacent-parameter calculation in the form consumed
by the exact diagonal realization recursion. -/
theorem firstValues_coefficientAdjacentAdmissible
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    BONG.CoefficientAdjacentAdmissible
      (beli2009ResidueTwoFirstValues (K := K) d epsilon eta) := by
  intro i hi
  let j : Fin 3 := ⟨i.val, by omega⟩
  have h := firstValues_adjacentAdmissible d hdpos hdlt epsilon eta
    hepsilon heta j
  have hleft : i = j.castSucc := by
    apply Fin.ext
    rfl
  have hright : (⟨i.val + 1, hi⟩ : Fin 4) = j.succ := by
    apply Fin.ext
    rfl
  have hnum := congrArg
    (beli2009ResidueTwoFirstValues (K := K) d epsilon eta) hright
  have hden := congrArg
    (beli2009ResidueTwoFirstValues (K := K) d epsilon eta) hleft
  rw [hnum, hden]
  exact h

theorem secondValues_coefficientAdjacentAdmissible
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    BONG.CoefficientAdjacentAdmissible
      (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) := by
  intro i hi
  let j : Fin 3 := ⟨i.val, by omega⟩
  have h := secondValues_adjacentAdmissible d hdpos hdlt epsilon eta
    hepsilon heta j
  have hleft : i = j.castSucc := by
    apply Fin.ext
    rfl
  have hright : (⟨i.val + 1, hi⟩ : Fin 4) = j.succ := by
    apply Fin.ext
    rfl
  have hnum := congrArg
    (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) hright
  have hden := congrArg
    (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) hleft
  rw [hnum, hden]
  exact h

/-- The second coefficient family differs coordinatewise from the uniform
`eta`-multiple of the first family by squares. -/
theorem secondValues_pointwise_scaledFirst
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) (i : Fin 4) :
    beli2009ResidueTwoSecondValues (K := K) d epsilon eta i =
      (eta : Kˣ) *
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta i *
        ![(1 : Kˣ), 1, (eta : Kˣ)⁻¹, (eta : Kˣ)⁻¹] i ^ 2 := by
  fin_cases i
  · simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues]
  · simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues]
    ac_rfl
  · simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues, pow_two]
    exact (mul_mul_mul_inv_square (eta : Kˣ) (epsilon : Kˣ)).symm
  · simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues, pow_two]
    exact (mul_mul_mul_inv_square (eta : Kˣ)
      (uniformizerPowerUnit K
        (beli2009ResidueTwoOrder (K := K) d))).symm

/-- The two displayed rank-four coefficient families define isometric
quadratic spaces.  This supplies the ambient representation needed to put
their good BONG realizations on one lattice. -/
theorem secondValues_diagonalRepresents_firstValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) :
    DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients
        (beli2009ResidueTwoSecondValues (K := K) d epsilon eta))
      (BONG.GoodBONG.diagonalUnitCoefficients
        (beli2009ResidueTwoFirstValues (K := K) d epsilon eta)) := by
  let first := beli2009ResidueTwoFirstValues (K := K) d epsilon eta
  let second := beli2009ResidueTwoSecondValues (K := K) d epsilon eta
  let scaled : Fin 4 → Kˣ := fun i ↦ (eta : Kˣ) * first i
  let multipliers : Fin 4 → Kˣ :=
    ![(1 : Kˣ), 1, (eta : Kˣ)⁻¹, (eta : Kˣ)⁻¹]
  have hcoeff : ∀ i, second i = scaled i * multipliers i ^ 2 := by
    intro i
    exact secondValues_pointwise_scaledFirst d epsilon eta i
  have hsecondScaled : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients second)
      (BONG.GoodBONG.diagonalUnitCoefficients scaled) :=
    diagonalRepresents_of_pointwise_mul_square second scaled multipliers hcoeff
  have hhasseSecondScaled : diagonalHasseSymbol K second =
      diagonalHasseSymbol K scaled :=
    DiagonalIsometryInvariantLaws.hasse_eq second scaled hsecondScaled
  have hfirstDetSquare : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant first) := by
    let p := uniformizerPowerUnit K (beli2009ResidueTwoOrder (K := K) d)
    refine ⟨p * (epsilon : Kˣ) * (eta : Kˣ), ?_⟩
    apply Units.ext
    simp [first, p, BONG.GoodBONG.diagonalUnitDeterminant,
      Fin.prod_univ_four, beli2009ResidueTwoFirstValues,
      Units.val_mul, Units.val_neg]
    ring
  have hhilbert : hilbertSymbol K (eta : Kˣ)
      (BONG.GoodBONG.diagonalUnitDeterminant first) = 1 :=
    hilbertSymbol_eq_one_of_isSquare_right K hfirstDetSquare
  have hscale := QuaternaryHasse.diagonalHasseSymbol_fin_four_scale
    (K := K) first (eta : Kˣ)
  have hhasseScaledFirst : diagonalHasseSymbol K scaled =
      diagonalHasseSymbol K first := by
    change diagonalHasseSymbol K (fun i ↦ (eta : Kˣ) * first i) = _
    rw [hscale, hhilbert, one_mul]
  have hhasse : diagonalHasseSymbol K second =
      diagonalHasseSymbol K first :=
    hhasseSecondScaled.trans hhasseScaledFirst
  have hdetEq : BONG.GoodBONG.diagonalUnitDeterminant second =
      BONG.GoodBONG.diagonalUnitDeterminant first := by
    apply Units.ext
    simp [first, second, BONG.GoodBONG.diagonalUnitDeterminant,
      Fin.prod_univ_four, beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues, Units.val_mul, Units.val_neg]
    ring
  have hdetProductSquare : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant second *
        BONG.GoodBONG.diagonalUnitDeterminant first) := by
    refine ⟨BONG.GoodBONG.diagonalUnitDeterminant first, ?_⟩
    rw [hdetEq]
  exact DyadicDiagonalClassificationLaws.represents_of_invariants
    second first hdetProductSquare hhasse

private theorem negative_product_eq_negative_ratio_mul_square
    (a b : Kˣ) : -(a * b) = (-(b / a)) * a ^ 2 := by
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val]
  field_simp [Units.ne_zero a]

/-- The adjacent products used in Beli's alpha definition have the same
defect pattern as the negative adjacent ratios. -/
theorem firstValues_adjacentProduct_defect
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    quadraticDefect K
        (-(beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.castSucc *
          beli2009ResidueTwoFirstValues (K := K) d epsilon eta i.succ)) =
      ![(d : ℕ∞), (2 * ramificationIndex K - d : ℕ∞),
        (d : ℕ∞)] i := by
  rw [negative_product_eq_negative_ratio_mul_square,
    quadraticDefect_mul_square,
    firstValues_negativeAdjacent_defect d epsilon eta hepsilon heta]

theorem secondValues_adjacentProduct_defect
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (i : Fin 3) :
    quadraticDefect K
        (-(beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.castSucc *
          beli2009ResidueTwoSecondValues (K := K) d epsilon eta i.succ)) =
      ![(d : ℕ∞), (2 * ramificationIndex K - d : ℕ∞),
        (d : ℕ∞)] i := by
  rw [negative_product_eq_negative_ratio_mul_square,
    quadraticDefect_mul_square,
    secondValues_negativeAdjacent_defect d epsilon eta hepsilon heta]

section AlphaExt

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Equality of orders and adjacent defects is exactly the information on
which the alpha candidate set depends. -/
theorem alphaValue_eq_of_orders_adjacentDefects_eq
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (horders : ∀ i, a.order i = b.order i)
    (hdefects : ∀ i, a.adjacentDefect i = b.adjacentDefect i)
    (i : Fin n) : a.alphaValue i = b.alphaValue i := by
  have hhalf : a.halfGapCandidate i = b.halfGapCandidate i := by
    unfold BONG.GoodBONG.halfGapCandidate
    rw [horders i.succ, horders i.castSucc]
  have hleft : a.leftDefectCandidate i = b.leftDefectCandidate i := by
    funext j
    unfold BONG.GoodBONG.leftDefectCandidate
    rw [horders i.succ, horders j.castSucc, hdefects j]
  have hright : a.rightDefectCandidate i = b.rightDefectCandidate i := by
    funext j
    unfold BONG.GoodBONG.rightDefectCandidate
    rw [horders j.succ, horders i.castSucc, hdefects j]
  have hcandidates : a.alphaCandidates i = b.alphaCandidates i := by
    unfold BONG.GoodBONG.alphaCandidates
    rw [hhalf, hleft, hright]
  apply WithTop.coe_injective
  rw [a.coe_alphaValue, b.coe_alphaValue]
  unfold BONG.GoodBONG.alpha
  simpa only [hcandidates]

end AlphaExt

section ResidueTwoClassification

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A good BONG with the first displayed residue-two coefficient family has
the advertised order pattern. -/
theorem order_eq_firstValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (i : Fin 4) :
    a.order i = ![0, beli2009ResidueTwoOrder (K := K) d,
      0, beli2009ResidueTwoOrder (K := K) d] i := by
  change a.toBONG.order i = _
  rw [a.toBONG.order_eq_ordUnit]
  change ordUnit K (a.valueUnit i) = _
  rw [ha, firstValues_order]

/-- The analogous order formula for the second displayed family. -/
theorem order_eq_secondValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (b : BONG.GoodBONG r M 4)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 4) :
    b.order i = ![0, beli2009ResidueTwoOrder (K := K) d,
      0, beli2009ResidueTwoOrder (K := K) d] i := by
  change b.toBONG.order i = _
  rw [b.toBONG.order_eq_ordUnit]
  change ordUnit K (b.valueUnit i) = _
  rw [hb, secondValues_order]

theorem sameOrders_of_residueTwoValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i) :
    a.SameOrders b := by
  intro i
  rw [order_eq_firstValues d epsilon eta a ha,
    order_eq_secondValues d epsilon eta b hb]

theorem adjacentDefects_eq_of_residueTwoValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 3) : a.adjacentDefect i = b.adjacentDefect i := by
  unfold BONG.GoodBONG.adjacentDefect BONG.GoodBONG.adjacentProduct
  rw [ha i.castSucc, ha i.succ, hb i.castSucc, hb i.succ]
  unfold BONG.GoodBONG.defectOrder
  rw [
    firstValues_adjacentProduct_defect d epsilon eta hepsilon heta,
    secondValues_adjacentProduct_defect d epsilon eta hepsilon heta]

theorem sameAlphas_of_residueTwoValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i) :
    a.SameAlphas b := by
  intro i
  apply alphaValue_eq_of_orders_adjacentDefects_eq a b
  · exact sameOrders_of_residueTwoValues d epsilon eta a b ha hb
  · exact adjacentDefects_eq_of_residueTwoValues d epsilon eta
      hepsilon heta a b ha hb

/-- The half-gap upper bounds are `2e-d,d,2e-d`.  Keeping this as a
rational formula avoids accidental truncated subtraction in the use of
condition (iv). -/
theorem halfGapCandidate_eq_firstValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    a.halfGapCandidate i =
      ((![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i : ℚ) : WithTop ℚ) := by
  unfold BONG.GoodBONG.halfGapCandidate
  rw [order_eq_firstValues d epsilon eta a ha,
    order_eq_firstValues d epsilon eta a ha]
  fin_cases i <;> simp only [Fin.castSucc_mk, Fin.succ_mk] <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Fin.reduceFinMk] <;>
    simp only [Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero]
  all_goals
    rw [WithTop.coe_eq_coe]
    push_cast
    simp only [beli2009ResidueTwoOrder, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_subNatNat]
    ring

theorem halfGapCandidate_eq_secondValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (b : BONG.GoodBONG r M 4)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    b.halfGapCandidate i =
      ((![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i : ℚ) : WithTop ℚ) := by
  unfold BONG.GoodBONG.halfGapCandidate
  rw [order_eq_secondValues d epsilon eta b hb,
    order_eq_secondValues d epsilon eta b hb]
  fin_cases i <;> simp only [Fin.castSucc_mk, Fin.succ_mk] <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
      Fin.reduceFinMk] <;>
    simp only [Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero]
  all_goals
    rw [WithTop.coe_eq_coe]
    push_cast
    simp only [beli2009ResidueTwoOrder, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_subNatNat]
    ring

theorem alphaValue_le_residueTwoPattern_first
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    a.alphaValue i ≤
      ![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i := by
  have h : (a.alphaValue i : WithTop ℚ) ≤
      ((![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i : ℚ) : WithTop ℚ) := by
    rw [a.coe_alphaValue,
      ← halfGapCandidate_eq_firstValues d epsilon eta a ha i]
    exact a.alpha_le_halfGapCandidate i
  exact WithTop.coe_le_coe.mp h

theorem alphaValue_le_residueTwoPattern_second
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (b : BONG.GoodBONG r M 4)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    b.alphaValue i ≤
      ![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i := by
  have h : (b.alphaValue i : WithTop ℚ) ≤
      ((![(2 * (ramificationIndex K : ℚ) - (d : ℚ)), (d : ℚ),
        2 * (ramificationIndex K : ℚ) - (d : ℚ)] i : ℚ) : WithTop ℚ) := by
    rw [b.coe_alphaValue,
      ← halfGapCandidate_eq_secondValues d epsilon eta b hb i]
    exact b.alpha_le_halfGapCandidate i
  exact WithTop.coe_le_coe.mp h

/-- The three comparison prefix products are, respectively, `eta`, a
square, and `eta` times a square.  This is the square-class content of
condition (iii) for the displayed counterexample. -/
theorem comparisonPrefixProduct_eq_residueTwoPattern
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    a.comparisonPrefixProduct b i =
      let p := uniformizerPowerUnit K
        (beli2009ResidueTwoOrder (K := K) d)
      ![(eta : Kˣ), (p * (epsilon : Kˣ) * (eta : Kˣ)) ^ 2,
        (eta : Kˣ) * (p * (epsilon : Kˣ) ^ 2 * (eta : Kˣ)) ^ 2] i := by
  let p := uniformizerPowerUnit K
    (beli2009ResidueTwoOrder (K := K) d)
  unfold BONG.GoodBONG.comparisonPrefixProduct BONG.GoodBONG.prefixProduct
  fin_cases i
  · rw [a.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, b.toBONG.prefixProduct_zero]
    change (1 * a.valueUnit 0) * (1 * b.valueUnit 0) = _
    rw [ha, hb]
    simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues]
  · rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_succ 1 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, b.toBONG.prefixProduct_zero]
    change ((1 * a.valueUnit 0) * a.valueUnit 1) *
      ((1 * b.valueUnit 0) * b.valueUnit 1) = _
    rw [ha, ha, hb, hb]
    simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues, p, pow_two]
    ac_rfl
  · rw [a.toBONG.prefixProduct_succ 2 (by omega),
      a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega),
      b.toBONG.prefixProduct_succ 2 (by omega),
      b.toBONG.prefixProduct_succ 1 (by omega),
      b.toBONG.prefixProduct_succ 0 (by omega),
      a.toBONG.prefixProduct_zero, b.toBONG.prefixProduct_zero]
    change (((1 * a.valueUnit 0) * a.valueUnit 1) * a.valueUnit 2) *
      (((1 * b.valueUnit 0) * b.valueUnit 1) * b.valueUnit 2) = _
    rw [ha, ha, ha, hb, hb, hb]
    simp [beli2009ResidueTwoFirstValues,
      beli2009ResidueTwoSecondValues, p, pow_two]
    ac_rfl

theorem defectOrder_eq_natCast_of_quadraticDefect_eq
    (x : Kˣ) (n : Nat)
    (h : quadraticDefect K x = (n : ℕ∞)) :
    BONG.GoodBONG.defectOrder (K := K) x =
      (((n : Nat) : ℚ) : WithTop ℚ) := by
  unfold BONG.GoodBONG.defectOrder
  rw [h]
  exact WithTop.map_coe (fun m : Nat ↦ (m : ℚ)) n

theorem defectOrder_eta_eq_residueTwoOuter
    (d : Nat) (hdlt : d < 2 * ramificationIndex K)
    (eta : valuationUnitSubgroup K)
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    BONG.GoodBONG.defectOrder (K := K) (eta : Kˣ) =
      ((2 * (ramificationIndex K : ℚ) - (d : ℚ) : ℚ) : WithTop ℚ) := by
  have hdle : d ≤ 2 * ramificationIndex K := Nat.le_of_lt hdlt
  have hENat :
      (2 * (ramificationIndex K : ℕ∞) - (d : ℕ∞)) =
        ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
    norm_cast
  have heta' : quadraticDefect K (eta : Kˣ) =
      ((2 * ramificationIndex K - d : Nat) : ℕ∞) :=
    heta.trans hENat
  rw [defectOrder_eq_natCast_of_quadraticDefect_eq
    (K := K) (eta : Kˣ) (2 * ramificationIndex K - d) heta',
    WithTop.coe_eq_coe, Nat.cast_sub hdle, Nat.cast_mul]
  norm_num

/-- Embedded defects of the three comparison prefixes are
`2e-d, ∞, 2e-d`. -/
theorem comparisonPrefixDefect_eq_residueTwoPattern
    (d : Nat) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (i : Fin 3) :
    BONG.GoodBONG.defectOrder (K := K)
        (a.comparisonPrefixProduct b i) =
      ![((2 * (ramificationIndex K : ℚ) - (d : ℚ) : ℚ) : WithTop ℚ),
        (⊤ : WithTop ℚ),
        ((2 * (ramificationIndex K : ℚ) - (d : ℚ) : ℚ) : WithTop ℚ)] i := by
  rw [comparisonPrefixProduct_eq_residueTwoPattern d epsilon eta a b ha hb]
  let p := uniformizerPowerUnit K
    (beli2009ResidueTwoOrder (K := K) d)
  fin_cases i <;> simp only [Fin.isValue, Fin.reduceFinMk] <;>
    simp only [Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero]
  · simpa only using
      defectOrder_eta_eq_residueTwoOuter (K := K) d hdlt eta heta
  · apply BONG.GoodBONG.defectOrder_eq_top_of_isSquare
    exact ⟨p * (epsilon : Kˣ) * (eta : Kˣ), by rw [pow_two]⟩
  · rw [BONG.GoodBONG.defectOrder_mul_square,
      defectOrder_eta_eq_residueTwoOuter (K := K) d hdlt eta heta]

theorem prefixDefectBounds_of_residueTwoValues
    (d : Nat) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i) :
    a.PrefixDefectBounds b := by
  intro i
  rw [comparisonPrefixDefect_eq_residueTwoPattern d hdlt epsilon eta
    heta a b ha hb]
  have h := alphaValue_le_residueTwoPattern_first d epsilon eta a ha i
  fin_cases i
  · exact WithTop.coe_le_coe.mpr h
  · exact le_top
  · exact WithTop.coe_le_coe.mpr h

/-- For the displayed order pattern, the two adjacent alpha upper bounds
always add to at most `2e`.  Hence the strict hypothesis in condition (iv)
never occurs. -/
theorem internalRepresentationConditions_of_residueTwoValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) :
    a.InternalRepresentationConditions b := by
  intro i hi hstrict
  fin_cases i
  · norm_num at hi
  · have hzero : a.alphaValue (0 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ) - (d : ℚ) := by
      simpa using alphaValue_le_residueTwoPattern_first
        d epsilon eta a ha (0 : Fin 3)
    have hone : a.alphaValue (1 : Fin 3) ≤ (d : ℚ) := by
      simpa using alphaValue_le_residueTwoPattern_first
        d epsilon eta a ha (1 : Fin 3)
    have hstrict' : (2 * ramificationIndex K : ℚ) <
        a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) := by
      simpa using hstrict
    exfalso
    linarith
  · have hone : a.alphaValue (1 : Fin 3) ≤ (d : ℚ) := by
      simpa using alphaValue_le_residueTwoPattern_first
        d epsilon eta a ha (1 : Fin 3)
    have htwo : a.alphaValue (2 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ) - (d : ℚ) := by
      simpa using alphaValue_le_residueTwoPattern_first
        d epsilon eta a ha (2 : Fin 3)
    have hstrict' : (2 * ramificationIndex K : ℚ) <
        a.alphaValue (1 : Fin 3) + a.alphaValue (2 : Fin 3) := by
      simpa using hstrict
    exfalso
    linarith

theorem classificationConditions_of_residueTwoValues
    (d : Nat) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞))
    (a : BONG.GoodBONG q L 4) (b : BONG.GoodBONG r M 4)
    (ha : ∀ i, a.valueUnit i =
      beli2009ResidueTwoFirstValues (K := K) d epsilon eta i)
    (hb : ∀ i, b.valueUnit i =
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta i) :
    ClassificationConditions a b where
  sameOrders := sameOrders_of_residueTwoValues d epsilon eta a b ha hb
  sameAlphas := sameAlphas_of_residueTwoValues d epsilon eta hepsilon heta
    a b ha hb
  prefixDefectBounds := prefixDefectBounds_of_residueTwoValues d hdlt
    epsilon eta heta a b ha hb
  internalRepresentations :=
    internalRepresentationConditions_of_residueTwoValues d epsilon eta a b ha

/-- The two displayed value families, realized as good BONGs on one and the
same rank-four lattice.  Non-reachability is deliberately not included in
this structure; it is the separate binary-move argument below. -/
structure ResidueTwoIsometricGoodBONGData
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) where
  q : QuadraticSpace K (Fin 4 → K)
  L : Lattice K (Fin 4 → K)
  first : BONG.GoodBONG q L 4
  second : BONG.GoodBONG q L 4
  first_values : ∀ i, first.valueUnit i =
    beli2009ResidueTwoFirstValues (K := K) d epsilon eta i
  second_values : ∀ i, second.valueUnit i =
    beli2009ResidueTwoSecondValues (K := K) d epsilon eta i

/-- Concrete realization and isometry of the two rank-four families in
Beli's final residue-two example. -/
theorem exists_residueTwoIsometricGoodBONGData
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    Nonempty (ResidueTwoIsometricGoodBONGData
      (K := K) d epsilon eta) := by
  let firstValues :=
    beli2009ResidueTwoFirstValues (K := K) d epsilon eta
  let secondValues :=
    beli2009ResidueTwoSecondValues (K := K) d epsilon eta
  let firstRealization := BONG.diagonalBONGRealizationOfCriteria firstValues
    (firstValues_coefficientAdjacentAdmissible d hdpos hdlt epsilon eta
      hepsilon heta)
    (firstValues_weakTwoStep d epsilon eta)
  let first : BONG.GoodBONG
      (BONG.coefficientDiagonalSpace firstValues)
      firstRealization.lattice 4 :=
    ⟨firstRealization.bong,
      firstRealization.isGood (firstValues_weakTwoStep d epsilon eta)⟩
  have hfirstValues : ∀ i, first.valueUnit i = firstValues i := by
    intro i
    change firstRealization.bong.valueUnit i = firstValues i
    exact firstRealization.valueUnit_eq i
  have hrepresentation : DiagonalRepresents
      (BONG.GoodBONG.diagonalUnitCoefficients secondValues)
      first.toBONG.value := by
    have hspace := secondValues_diagonalRepresents_firstValues
      (K := K) d epsilon eta
    convert hspace using 1
    funext i
    rw [← first.toBONG.coe_valueUnit]
    exact congrArg Units.val (by
      simpa only [BONG.GoodBONG.valueUnit, firstValues] using hfirstValues i)
  have hexists := BONG.exists_prescribedValuesGoodBONGData
    first secondValues hrepresentation
      (secondValues_weakTwoStep d epsilon eta)
      (secondValues_coefficientAdjacentAdmissible d hdpos hdlt epsilon eta
        hepsilon heta)
  rcases hexists with ⟨secondData⟩
  have hconditions : ClassificationConditions first secondData.bong :=
    classificationConditions_of_residueTwoValues d hdlt epsilon eta
      hepsilon heta first secondData.bong hfirstValues secondData.values
  have hisometric : Lattice.IsIsometric
      (BONG.coefficientDiagonalSpace firstValues)
      (BONG.coefficientDiagonalSpace firstValues)
      firstRealization.lattice secondData.lattice :=
    (BONG.GoodBONG.beli2009Theorem31_concrete
      (QuadraticSpace.isIsometric_refl
        (BONG.coefficientDiagonalSpace firstValues))
      first secondData.bong).2 hconditions
  rcases hisometric with ⟨f⟩
  let second := secondData.bong.mapLatticeIsometry f.symm
  refine ⟨{
    q := BONG.coefficientDiagonalSpace firstValues
    L := firstRealization.lattice
    first := first
    second := second
    first_values := ?_
    second_values := ?_
  }⟩
  · intro i
    exact hfirstValues i
  · intro i
    change (secondData.bong.mapLatticeIsometry f.symm).valueUnit i = _
    rw [BONG.GoodBONG.valueUnit_mapLatticeIsometry, secondData.values]

end ResidueTwoClassification

section ResidueTwoNonreachability

/-- The invariant carried by every binary-transformation chain starting from
the first residue-two value sequence.  Besides the order and adjacent-defect
profiles, it records the one extra principal-unit layer at the left endpoint
which separates the two displayed sequences. -/
structure ResidueTwoBinaryInvariant
    (d : Nat) (a : Fin 4 → Kˣ) : Prop where
  orders : ∀ i,
    ordUnit K (a i) =
      ![0, beli2009ResidueTwoOrder (K := K) d,
        0, beli2009ResidueTwoOrder (K := K) d] i
  first_deep : squareClass K (a 0) ∈
    principalUnitSquareClassSubgroup K
      (2 * ramificationIndex K - d + 1)
  adjacent_defects : ∀ i,
    quadraticDefect K (-(a i.succ / a i.castSucc)) =
      ![(d : ℕ∞), (2 * ramificationIndex K - d : ℕ∞),
        (d : ℕ∞)] i

/-- Membership of a field square class in the principal-unit filtration gives
the corresponding lower bound on relative quadratic defect. -/
theorem quadraticDefect_ge_of_squareClass_mem_principalUnit
    (x : Kˣ) (n : Nat)
    (hx : squareClass K x ∈ principalUnitSquareClassSubgroup K n) :
    (n : ℕ∞) ≤ quadraticDefect K x := by
  rcases hx with ⟨v, hv, hclass⟩
  let vu : valuationUnitSubgroup K := ⟨v, hv.1⟩
  have hvClass : valuationUnitClassHom K vu ∈
      principalUnitValuationClassSubgroup K n := by
    refine ⟨vu, ?_, rfl⟩
    exact hv
  have hvDefect :=
    natCast_le_quadraticDefect_of_unitClass_mem vu n hvClass
  rw [← quadraticDefect_eq_of_squareClass_eq v x hclass]
  exact hvDefect

/-- The image definition of the unit norm-class subgroup can be reflected to
an actual norm statement for the chosen valuation-unit representative. -/
theorem isQuadraticNorm_of_unitClass_mem
    (parameter : Kˣ) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      quadraticNormValuationClassSubgroup K parameter) :
    IsQuadraticNorm K parameter (u : Kˣ) := by
  rcases hu with ⟨v, hv, hclass⟩
  change IsQuadraticNorm K parameter (v : Kˣ) at hv
  change
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) v =
      QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u
    at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨s, hs, hvsu⟩
  change IsSquare s at hs
  rcases hs with ⟨t, hst⟩
  have hsSquare : IsSquare (s : Kˣ) := by
    refine ⟨(t : Kˣ), ?_⟩
    have hstK := congrArg
      (fun z : valuationUnitSubgroup K => (z : Kˣ)) hst
    simpa [pow_two] using hstK
  have hproduct : IsQuadraticNorm K parameter
      ((v : Kˣ) * (s : Kˣ)) :=
    hv.mul K (isQuadraticNorm_of_isSquare_right K hsSquare)
  have hvsuK := congrArg
    (fun z : valuationUnitSubgroup K => (z : Kˣ)) hvsu
  simpa using hvsuK ▸ hproduct

/-- A valuation-unit class lying in exactly the `m`-th principal layer has
quadratic defect `m`. -/
theorem quadraticDefect_eq_of_mem_principalUnit_not_mem_succ
    (u : valuationUnitSubgroup K) (m : Nat)
    (hmem : valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K m)
    (hnot : valuationUnitClassHom K u ∉
      principalUnitValuationClassSubgroup K (m + 1)) :
    quadraticDefect K (u : Kˣ) = (m : ℕ∞) := by
  have hlower := natCast_le_quadraticDefect_of_unitClass_mem u m hmem
  have hupper : quadraticDefect K (u : Kˣ) < ((m + 1 : Nat) : ℕ∞) := by
    by_contra h
    have hnext : ((m + 1 : Nat) : ℕ∞) ≤
        quadraticDefect K (u : Kˣ) := le_of_not_gt h
    exact hnot
      (valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        K u (m + 1) hnext)
  have hfinite : quadraticDefect K (u : Kˣ) ≠ ⊤ :=
    ne_top_of_lt (hupper.trans (WithTop.coe_lt_top _))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [← hr] at hlower hupper ⊢
  have hmr : m ≤ r := WithTop.coe_le_coe.mp hlower
  have hrm : r < m + 1 := WithTop.coe_lt_coe.mp hupper
  congr 1
  omega

/-- At the defect boundary `m+n=2e` over the two-element residue field, the
norm condition in the low branch of `g(a)` removes the entire depth-`n`
layer.  Thus every permitted multiplier actually lies one layer deeper. -/
theorem normGeneratorClass_mem_principalUnit_succ_of_boundary
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (a : Kˣ) (u : valuationUnitSubgroup K) (m n : Nat)
    (hparameter : quadraticDefect K (-a) = (m : ℕ∞))
    (hsum : m + n = 2 * ramificationIndex K)
    (hnotAbove : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hlow : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞))
    (hexponent : beliLowDefectExponent K a = n)
    (hu : valuationUnitClassHom K u ∈ beliNormGeneratorGroup K a) :
    valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K (n + 1) := by
  rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow,
    hexponent] at hu
  by_contra hnotDeep
  have huDefect : quadraticDefect K (u : Kˣ) = (n : ℕ∞) :=
    quadraticDefect_eq_of_mem_principalUnit_not_mem_succ
      u n hu.1 hnotDeep
  have huNorm : IsQuadraticNorm K (-a) (u : Kˣ) :=
    isQuadraticNorm_of_unitClass_mem (-a) u hu.2
  have huHilbert : hilbertSymbol K (-a) (u : Kˣ) = 1 :=
    (hilbertSymbol_eq_one_iff K (-a) (u : Kˣ)).2 huNorm
  have hsumDefect :
      quadraticDefect K (-a) + quadraticDefect K (u : Kˣ) =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [hparameter, huDefect]
    exact_mod_cast hsum
  have hboundary :=
    (BONG.beli2019Lemma82_iii hres (-a) (u : Kˣ)).mp
      ⟨(u : Kˣ), rfl, huHilbert⟩
  exact hboundary hsumDefect

/-- The order of an adjacent parameter is read off from the four-entry order
profile in the residue-two invariant. -/
theorem ResidueTwoBinaryInvariant.adjacentRatio_order
    {d : Nat} {a : Fin 4 → Kˣ}
    (h : ResidueTwoBinaryInvariant (K := K) d a) (i : Fin 3) :
    ordUnit K (a i.succ / a i.castSucc) =
      ![beli2009ResidueTwoOrder (K := K) d,
        -beli2009ResidueTwoOrder (K := K) d,
        beli2009ResidueTwoOrder (K := K) d] i := by
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    h.orders, h.orders]
  fin_cases i <;> simp

private theorem residueTwo_outer_cutoff_eq
    (d : Nat) :
    Int.toNat (2 * (ramificationIndex K : Int) -
      beli2009ResidueTwoOrder (K := K) d) = 2 * d := by
  apply Int.ofNat_injective
  calc
    (Int.toNat (2 * (ramificationIndex K : Int) -
        beli2009ResidueTwoOrder (K := K) d) : Int) =
        2 * (ramificationIndex K : Int) -
          beli2009ResidueTwoOrder (K := K) d :=
      Int.toNat_of_nonneg (by
        simp only [beli2009ResidueTwoOrder]
        omega)
    _ = ((2 * d : Nat) : Int) := by
      simp only [beli2009ResidueTwoOrder]
      push_cast
      ring

private theorem residueTwo_middle_cutoff_eq
    (d : Nat) (hdlt : d < 2 * ramificationIndex K) :
    Int.toNat (2 * (ramificationIndex K : Int) -
      -beli2009ResidueTwoOrder (K := K) d) =
        2 * (2 * ramificationIndex K - d) := by
  apply Int.ofNat_injective
  calc
    (Int.toNat (2 * (ramificationIndex K : Int) -
        -beli2009ResidueTwoOrder (K := K) d) : Int) =
        2 * (ramificationIndex K : Int) -
          -beli2009ResidueTwoOrder (K := K) d :=
      Int.toNat_of_nonneg (by
        simp only [beli2009ResidueTwoOrder]
        omega)
    _ = ((2 * (2 * ramificationIndex K - d) : Nat) : Int) := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub hdlt.le]
      simp only [beli2009ResidueTwoOrder]
      push_cast
      ring

private theorem residueTwo_outer_lowExponent_eq
    (d : Nat) (hdlt : d < 2 * ramificationIndex K) :
    Int.toNat (beli2009ResidueTwoOrder (K := K) d + (d : Int)) =
      2 * ramificationIndex K - d := by
  apply Int.ofNat_injective
  calc
    (Int.toNat (beli2009ResidueTwoOrder (K := K) d + (d : Int)) : Int) =
        beli2009ResidueTwoOrder (K := K) d + (d : Int) :=
      Int.toNat_of_nonneg (by
        simp only [beli2009ResidueTwoOrder]
        omega)
    _ = ((2 * ramificationIndex K - d : Nat) : Int) := by
      rw [Nat.cast_sub hdlt.le]
      simp only [beli2009ResidueTwoOrder]
      push_cast
      ring

private theorem residueTwo_middle_lowExponent_eq
    (d : Nat) (hdlt : d < 2 * ramificationIndex K) :
    Int.toNat (-beli2009ResidueTwoOrder (K := K) d +
      (2 * ramificationIndex K - d : Nat)) = d := by
  apply Int.ofNat_injective
  calc
    (Int.toNat (-beli2009ResidueTwoOrder (K := K) d +
        (2 * ramificationIndex K - d : Nat)) : Int) =
        -beli2009ResidueTwoOrder (K := K) d +
          (2 * ramificationIndex K - d : Nat) :=
      Int.toNat_of_nonneg (by
        rw [Nat.cast_sub hdlt.le]
        simp only [beli2009ResidueTwoOrder]
        push_cast
        omega)
    _ = (d : Int) := by
      rw [Nat.cast_sub hdlt.le]
      simp only [beli2009ResidueTwoOrder]
      push_cast
      ring

/-- In each of the three adjacent positions, the residue-two boundary forces
an allowed binary multiplier one principal-unit layer deeper than the nominal
alpha depth. -/
theorem residueTwo_binaryMultiplier_mem_deep
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (a : Fin 4 → Kˣ) (ha : ResidueTwoBinaryInvariant (K := K) d a)
    (i : Fin 3) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K (a i.succ / a i.castSucc)) :
    valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K
        (![2 * ramificationIndex K - d + 1, d + 1,
          2 * ramificationIndex K - d + 1] i) := by
  fin_cases i
  · let parameter : Kˣ :=
      a (0 : Fin 3).succ / a (0 : Fin 3).castSucc
    have horder : ordUnit K parameter =
        beli2009ResidueTwoOrder (K := K) d := by
      simpa [parameter] using ha.adjacentRatio_order (0 : Fin 3)
    have hparameter : quadraticDefect K (-parameter) = (d : ℕ∞) := by
      simpa [parameter] using ha.adjacent_defects (0 : Fin 3)
    have hnotAbove : ¬2 * (ramificationIndex K : Int) <
        ordUnit K parameter := by
      rw [horder]
      simp only [beli2009ResidueTwoOrder]
      omega
    have hcutoff : beliDefectCutoff K parameter = 2 * d := by
      unfold beliDefectCutoff
      rw [horder]
      exact residueTwo_outer_cutoff_eq (K := K) d
    have hlow : 2 * beliParameterDefect K parameter ≤
        (beliDefectCutoff K parameter : ℕ∞) := by
      unfold beliParameterDefect
      rw [hparameter, hcutoff]
      exact_mod_cast (le_refl (2 * d))
    have hdefectNat : beliParameterDefectNat K parameter = d := by
      simp [beliParameterDefectNat, beliParameterDefect, hparameter]
    have hexponent : beliLowDefectExponent K parameter =
        2 * ramificationIndex K - d := by
      unfold beliLowDefectExponent
      rw [hdefectNat, horder]
      exact residueTwo_outer_lowExponent_eq (K := K) d hdlt
    apply normGeneratorClass_mem_principalUnit_succ_of_boundary
      hres parameter u d (2 * ramificationIndex K - d)
        hparameter (by omega) hnotAbove hlow hexponent
    simpa [parameter] using hu
  · let parameter : Kˣ :=
      a (1 : Fin 3).succ / a (1 : Fin 3).castSucc
    have horder : ordUnit K parameter =
        -beli2009ResidueTwoOrder (K := K) d := by
      simpa [parameter] using ha.adjacentRatio_order (1 : Fin 3)
    have hparameter : quadraticDefect K (-parameter) =
        (2 * ramificationIndex K - d : ℕ∞) := by
      simpa [parameter] using ha.adjacent_defects (1 : Fin 3)
    have hnotAbove : ¬2 * (ramificationIndex K : Int) <
        ordUnit K parameter := by
      rw [horder]
      simp only [beli2009ResidueTwoOrder]
      omega
    have hcutoff : beliDefectCutoff K parameter =
        2 * (2 * ramificationIndex K - d) := by
      unfold beliDefectCutoff
      rw [horder]
      exact residueTwo_middle_cutoff_eq (K := K) d hdlt
    have hlow : 2 * beliParameterDefect K parameter ≤
        (beliDefectCutoff K parameter : ℕ∞) := by
      unfold beliParameterDefect
      rw [hparameter, hcutoff]
      exact_mod_cast
        (le_refl (2 * (2 * ramificationIndex K - d)))
    have hdefectNat : beliParameterDefectNat K parameter =
        2 * ramificationIndex K - d := by
      unfold beliParameterDefectNat beliParameterDefect
      rw [hparameter]
      have hsub :
          (2 * ramificationIndex K - d : ℕ∞) =
            ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
        rw [ENat.coe_sub]
        norm_cast
      have hfinite : (2 * ramificationIndex K - d : ℕ∞) ≠ ⊤ := by
        rw [hsub]
        exact WithTop.coe_ne_top
      have hcoe := ENat.coe_toNat hfinite
      rw [hsub] at hcoe
      exact WithTop.coe_injective hcoe
    have hexponent : beliLowDefectExponent K parameter = d := by
      unfold beliLowDefectExponent
      rw [hdefectNat, horder]
      exact residueTwo_middle_lowExponent_eq (K := K) d hdlt
    apply normGeneratorClass_mem_principalUnit_succ_of_boundary
      hres parameter u (2 * ramificationIndex K - d) d
        hparameter (by omega) hnotAbove hlow hexponent
    simpa [parameter] using hu
  · let parameter : Kˣ :=
      a (2 : Fin 3).succ / a (2 : Fin 3).castSucc
    have horder : ordUnit K parameter =
        beli2009ResidueTwoOrder (K := K) d := by
      simpa [parameter] using ha.adjacentRatio_order (2 : Fin 3)
    have hparameter : quadraticDefect K (-parameter) = (d : ℕ∞) := by
      simpa [parameter] using ha.adjacent_defects (2 : Fin 3)
    have hnotAbove : ¬2 * (ramificationIndex K : Int) <
        ordUnit K parameter := by
      rw [horder]
      simp only [beli2009ResidueTwoOrder]
      omega
    have hcutoff : beliDefectCutoff K parameter = 2 * d := by
      unfold beliDefectCutoff
      rw [horder]
      exact residueTwo_outer_cutoff_eq (K := K) d
    have hlow : 2 * beliParameterDefect K parameter ≤
        (beliDefectCutoff K parameter : ℕ∞) := by
      unfold beliParameterDefect
      rw [hparameter, hcutoff]
      exact_mod_cast (le_refl (2 * d))
    have hdefectNat : beliParameterDefectNat K parameter = d := by
      simp [beliParameterDefectNat, beliParameterDefect, hparameter]
    have hexponent : beliLowDefectExponent K parameter =
        2 * ramificationIndex K - d := by
      unfold beliLowDefectExponent
      rw [hdefectNat, horder]
      exact residueTwo_outer_lowExponent_eq (K := K) d hdlt
    apply normGeneratorClass_mem_principalUnit_succ_of_boundary
      hres parameter u d (2 * ramificationIndex K - d)
        hparameter (by omega) hnotAbove hlow hexponent
    simpa [parameter] using hu

/-- The first displayed value sequence satisfies the reachability invariant. -/
theorem firstValues_residueTwoBinaryInvariant
    (d : Nat) (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    ResidueTwoBinaryInvariant (K := K) d
      (beli2009ResidueTwoFirstValues (K := K) d epsilon eta) where
  orders := firstValues_order d epsilon eta
  first_deep := by
    change squareClass K (1 : Kˣ) ∈
      principalUnitSquareClassSubgroup K
        (2 * ramificationIndex K - d + 1)
    exact Subgroup.one_mem _
  adjacent_defects :=
    firstValues_negativeAdjacent_defect d epsilon eta hepsilon heta

private theorem squareClass_inv_local (x : Kˣ) :
    squareClass K x⁻¹ = (squareClass K x)⁻¹ :=
  rfl

private theorem squareClass_neg_local (x : Kˣ) :
    squareClass K (-x) =
      squareClass K (-1 : Kˣ) * squareClass K x := by
  rw [show -x = (-1 : Kˣ) * x by simp, squareClass_mul_eq]

/-- Forgetting the valuation-unit refinement sends pointwise equivalence to
ordinary field-square-class equality. -/
theorem squareClass_eq_of_valueSequenceEquivalent
    {a b : Fin 4 → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) (i : Fin 4) :
    squareClass K (a i) = squareClass K (b i) := by
  have hmap := congrArg (unitSquareClassToSquareClass K) (h i)
  simpa only [unitSquareClassToSquareClass_apply] using hmap

/-- Pointwise equivalence also preserves the square class of every negative
adjacent parameter. -/
theorem negativeAdjacent_squareClass_eq_of_valueSequenceEquivalent
    {a b : Fin 4 → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) (i : Fin 3) :
    squareClass K (-(a i.succ / a i.castSucc)) =
      squareClass K (-(b i.succ / b i.castSucc)) := by
  have hleft := squareClass_eq_of_valueSequenceEquivalent h i.castSucc
  have hright := squareClass_eq_of_valueSequenceEquivalent h i.succ
  have hratio : squareClass K (a i.succ / a i.castSucc) =
      squareClass K (b i.succ / b i.castSucc) := by
    simp only [div_eq_mul_inv, squareClass_mul_eq, squareClass_inv_local]
    rw [hleft, hright]
  calc
    squareClass K (-(a i.succ / a i.castSucc)) =
        squareClass K (-1 : Kˣ) *
          squareClass K (a i.succ / a i.castSucc) :=
      squareClass_neg_local _
    _ = squareClass K (-1 : Kˣ) *
        squareClass K (b i.succ / b i.castSucc) :=
      congrArg (fun z => squareClass K (-1 : Kˣ) * z) hratio
    _ = squareClass K (-(b i.succ / b i.castSucc)) :=
      (squareClass_neg_local _).symm

/-- The residue-two invariant is insensitive to the paper's permitted change
of coefficient representatives by valuation-unit squares. -/
theorem ResidueTwoBinaryInvariant.of_valueSequenceEquivalent
    {d : Nat} {a b : Fin 4 → Kˣ}
    (ha : ResidueTwoBinaryInvariant (K := K) d a)
    (hab : Beli2009ValueSequenceEquivalent (K := K) a b) :
    ResidueTwoBinaryInvariant (K := K) d b where
  orders := by
    intro i
    exact (ordUnit_eq_of_unitSquareClass_eq (K := K) (hab i)).symm.trans
      (ha.orders i)
  first_deep := by
    rw [← squareClass_eq_of_valueSequenceEquivalent hab 0]
    exact ha.first_deep
  adjacent_defects := by
    intro i
    calc
      quadraticDefect K (-(b i.succ / b i.castSucc)) =
          quadraticDefect K (-(a i.succ / a i.castSucc)) :=
        quadraticDefect_eq_of_squareClass_eq _ _
          (negativeAdjacent_squareClass_eq_of_valueSequenceEquivalent
            hab i).symm
      _ = _ := ha.adjacent_defects i

/-- Multiplication by a class from the next principal-unit layer leaves an
exact finite defect unchanged. -/
theorem quadraticDefect_mul_eq_of_principalUnit_succ
    (x s : Kˣ) (m : Nat)
    (hx : quadraticDefect K x = (m : ℕ∞))
    (hs : ((m + 1 : Nat) : ℕ∞) ≤ quadraticDefect K s) :
    quadraticDefect K (x * s) = (m : ℕ∞) := by
  have hstrict : quadraticDefect K x < quadraticDefect K s := by
    rw [hx]
    exact (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m)).trans_le hs
  rw [quadraticDefect_mul_eq_left_of_lt_right (K := K) hstrict, hx]

/-- Multiplying the two selected coordinates by a valuation unit leaves every
coefficient order unchanged. -/
theorem ordUnit_beli2009BinaryTransformAt
    (a : Fin 4 → Kˣ) (i : Fin 3) (u : valuationUnitSubgroup K)
    (j : Fin 4) :
    ordUnit K (beli2009BinaryTransformAt a i (u : Kˣ) j) =
      ordUnit K (a j) := by
  have huOrder : ordUnit K (u : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
  fin_cases i <;> fin_cases j <;>
    simp [beli2009BinaryTransformAt, ordUnit_mul, huOrder]

private noncomputable def negativeAdjacentParameter
    (a : Fin 4 → Kˣ) (i : Fin 3) : Kˣ :=
  -(a i.succ / a i.castSucc)

/-- Exact algebraic effect of a binary move on the three negative adjacent
parameters.  The selected parameter is unchanged modulo a square; each
neighbor is multiplied by `u` or `u⁻¹`. -/
theorem negativeAdjacentParameter_beli2009BinaryTransformAt
    (a : Fin 4 → Kˣ) (i : Fin 3) (u : Kˣ) (j : Fin 3) :
    negativeAdjacentParameter
        (beli2009BinaryTransformAt a i u) j =
      ![
        ![negativeAdjacentParameter a 0,
          negativeAdjacentParameter a 1 * u⁻¹,
          negativeAdjacentParameter a 2],
        ![negativeAdjacentParameter a 0 * u,
          negativeAdjacentParameter a 1,
          negativeAdjacentParameter a 2 * u⁻¹],
        ![negativeAdjacentParameter a 0,
          negativeAdjacentParameter a 1 * u,
          negativeAdjacentParameter a 2]
      ] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [negativeAdjacentParameter, beli2009BinaryTransformAt,
      div_eq_mul_inv] <;>
    simp [mul_assoc, mul_comm, mul_left_comm] <;> try ac_rfl

theorem ResidueTwoBinaryInvariant.adjacentDefect_zero
    {d : Nat} {a : Fin 4 → Kˣ}
    (h : ResidueTwoBinaryInvariant (K := K) d a) :
    quadraticDefect K (negativeAdjacentParameter a 0) = (d : ℕ∞) := by
  simpa [negativeAdjacentParameter] using h.adjacent_defects (0 : Fin 3)

theorem ResidueTwoBinaryInvariant.adjacentDefect_one
    {d : Nat} (hdlt : d < 2 * ramificationIndex K)
    {a : Fin 4 → Kˣ}
    (h : ResidueTwoBinaryInvariant (K := K) d a) :
    quadraticDefect K (negativeAdjacentParameter a 1) =
      ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
  have hraw := h.adjacent_defects (1 : Fin 3)
  have hsub :
      (2 * ramificationIndex K - d : ℕ∞) =
        ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
    rw [ENat.coe_sub]
    norm_cast
  have hraw' :
      quadraticDefect K (negativeAdjacentParameter a 1) =
        (2 * ramificationIndex K - d : ℕ∞) := by
    simpa [negativeAdjacentParameter] using hraw
  exact hraw'.trans hsub

theorem ResidueTwoBinaryInvariant.adjacentDefect_two
    {d : Nat} {a : Fin 4 → Kˣ}
    (h : ResidueTwoBinaryInvariant (K := K) d a) :
    quadraticDefect K (negativeAdjacentParameter a 2) = (d : ℕ∞) := by
  simpa [negativeAdjacentParameter] using h.adjacent_defects (2 : Fin 3)

/-- A genuine adjacent binary transformation preserves the residue-two
reachability invariant.  The strict boundary lemma supplies exactly the depth
needed at each neighboring parameter. -/
theorem ResidueTwoBinaryInvariant.of_binaryTransformation
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    {d : Nat} (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    {a b : Fin 4 → Kˣ}
    (ha : ResidueTwoBinaryInvariant (K := K) d a)
    (hab : IsBeli2009BinaryTransformation (K := K) a b) :
    ResidueTwoBinaryInvariant (K := K) d b := by
  rcases hab with ⟨i, u, hu, rfl⟩
  have hdeep := residueTwo_binaryMultiplier_mem_deep
    hres d hdpos hdlt a ha i u hu
  have hdeepSquare : squareClass K (u : Kˣ) ∈
      principalUnitSquareClassSubgroup K
        (![2 * ramificationIndex K - d + 1, d + 1,
          2 * ramificationIndex K - d + 1] i) := by
    have hmapped := valuationUnitClassToSquareClass_mem_image
      (K := K) hdeep
    rw [valuationUnitClassSubgroupSquareImage_principalUnit] at hmapped
    simpa only [valuationUnitClassToSquareClass_apply] using hmapped
  have hsub :
      (2 * ramificationIndex K - d : ℕ∞) =
        ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
    rw [ENat.coe_sub]
    norm_cast
  refine {
    orders := ?_
    first_deep := ?_
    adjacent_defects := ?_
  }
  · intro j
    rw [ordUnit_beli2009BinaryTransformAt]
    exact ha.orders j
  · fin_cases i
    · have huSquare : squareClass K (u : Kˣ) ∈
          principalUnitSquareClassSubgroup K
            (2 * ramificationIndex K - d + 1) := by
        simpa using hdeepSquare
      change squareClass K ((u : Kˣ) * a 0) ∈
        principalUnitSquareClassSubgroup K
          (2 * ramificationIndex K - d + 1)
      rw [squareClass_mul_eq]
      exact (principalUnitSquareClassSubgroup K
        (2 * ramificationIndex K - d + 1)).mul_mem
          huSquare ha.first_deep
    · simpa [beli2009BinaryTransformAt] using ha.first_deep
    · simpa [beli2009BinaryTransformAt] using ha.first_deep
  · intro j
    change quadraticDefect K
        (negativeAdjacentParameter
          (beli2009BinaryTransformAt a i (u : Kˣ)) j) = _
    rw [negativeAdjacentParameter_beli2009BinaryTransformAt]
    fin_cases i
    · have huDepth :
          ((2 * ramificationIndex K - d + 1 : Nat) : ℕ∞) ≤
            quadraticDefect K (u : Kˣ) :=
        natCast_le_quadraticDefect_of_unitClass_mem u
          (2 * ramificationIndex K - d + 1) (by simpa using hdeep)
      have huInvDepth :
          ((2 * ramificationIndex K - d + 1 : Nat) : ℕ∞) ≤
            quadraticDefect K ((u : Kˣ)⁻¹) := by
        rwa [quadraticDefect_inv]
      fin_cases j
      · simpa using ha.adjacentDefect_zero
      · have hpres := quadraticDefect_mul_eq_of_principalUnit_succ
          (negativeAdjacentParameter a 1) (u : Kˣ)⁻¹
            (2 * ramificationIndex K - d)
              (ha.adjacentDefect_one hdlt) huInvDepth
        exact hpres.trans hsub.symm
      · simpa using ha.adjacentDefect_two
    · have huDepth : ((d + 1 : Nat) : ℕ∞) ≤
          quadraticDefect K (u : Kˣ) :=
        natCast_le_quadraticDefect_of_unitClass_mem u (d + 1)
          (by simpa using hdeep)
      have huInvDepth : ((d + 1 : Nat) : ℕ∞) ≤
          quadraticDefect K ((u : Kˣ)⁻¹) := by
        rwa [quadraticDefect_inv]
      fin_cases j
      · exact quadraticDefect_mul_eq_of_principalUnit_succ
          (negativeAdjacentParameter a 0) (u : Kˣ) d
            ha.adjacentDefect_zero huDepth
      · exact (ha.adjacentDefect_one hdlt).trans hsub.symm
      · exact quadraticDefect_mul_eq_of_principalUnit_succ
          (negativeAdjacentParameter a 2) (u : Kˣ)⁻¹ d
            ha.adjacentDefect_two huInvDepth
    · have huDepth :
          ((2 * ramificationIndex K - d + 1 : Nat) : ℕ∞) ≤
            quadraticDefect K (u : Kˣ) :=
        natCast_le_quadraticDefect_of_unitClass_mem u
          (2 * ramificationIndex K - d + 1) (by simpa using hdeep)
      fin_cases j
      · simpa using ha.adjacentDefect_zero
      · have hpres := quadraticDefect_mul_eq_of_principalUnit_succ
          (negativeAdjacentParameter a 1) (u : Kˣ)
            (2 * ramificationIndex K - d)
              (ha.adjacentDefect_one hdlt) huDepth
        exact hpres.trans hsub.symm
      · simpa using ha.adjacentDefect_two

/-- The target value sequence fails the endpoint layer of the invariant. -/
theorem secondValues_not_residueTwoBinaryInvariant
    (d : Nat) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    ¬ResidueTwoBinaryInvariant (K := K) d
      (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) := by
  intro h
  have hlower := quadraticDefect_ge_of_squareClass_mem_principalUnit
    (beli2009ResidueTwoSecondValues (K := K) d epsilon eta 0)
      (2 * ramificationIndex K - d + 1) h.first_deep
  have hvalue :
      beli2009ResidueTwoSecondValues (K := K) d epsilon eta 0 =
        (eta : Kˣ) := by
    simp [beli2009ResidueTwoSecondValues]
  rw [hvalue, heta] at hlower
  have hsub :
      (2 * ramificationIndex K - d : ℕ∞) =
        ((2 * ramificationIndex K - d : Nat) : ℕ∞) := by
    rw [ENat.coe_sub]
    norm_cast
  rw [hsub] at hlower
  have hnat := WithTop.coe_le_coe.mp hlower
  omega

/-- Either kind of permitted elementary step preserves the invariant. -/
theorem ResidueTwoBinaryInvariant.of_binaryStep
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    {d : Nat} (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    {a b : Fin 4 → Kˣ}
    (ha : ResidueTwoBinaryInvariant (K := K) d a)
    (hab : IsBeli2009BinaryStep (K := K) a b) :
    ResidueTwoBinaryInvariant (K := K) d b := by
  rcases hab with hab | hab
  · exact ha.of_valueSequenceEquivalent hab
  · exact ha.of_binaryTransformation hres hdpos hdlt hab

/-- Hence the invariant propagates through an arbitrary finite binary chain. -/
theorem ResidueTwoBinaryInvariant.of_binaryReachable
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    {d : Nat} (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    {a b : Fin 4 → Kˣ}
    (ha : ResidueTwoBinaryInvariant (K := K) d a)
    (hab : Beli2009BinaryReachable (K := K) a b) :
    ResidueTwoBinaryInvariant (K := K) d b := by
  induction hab with
  | refl => exact ha
  | tail hreach hstep ih =>
      exact ih.of_binaryStep hres hdpos hdlt hstep

/-- The two value sequences displayed by Beli over a residue field of order
two cannot be joined by binary transformations. -/
theorem residueTwoFirstValues_not_binaryReachable_secondValues
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [BONG.DyadicResidueDefectProductLaws K]
    [BONG.DyadicHilbertDefectChoiceLaws K]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    ¬Beli2009BinaryReachable (K := K)
      (beli2009ResidueTwoFirstValues (K := K) d epsilon eta)
      (beli2009ResidueTwoSecondValues (K := K) d epsilon eta) := by
  intro hreach
  have hinvariant :=
    (firstValues_residueTwoBinaryInvariant d epsilon eta hepsilon heta).of_binaryReachable
      hres hdpos hdlt hreach
  exact secondValues_not_residueTwoBinaryInvariant d hdlt epsilon eta heta
    hinvariant

/-- Concrete same-lattice counterexample, including the non-reachability
proof omitted from the source's final paragraph. -/
theorem exists_residueTwoBinaryTransformationCounterexample
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d) (hdlt : d < 2 * ramificationIndex K)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) = (d : ℕ∞))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : ℕ∞)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i =
        beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
      ∀ i, C.second.valueUnit i =
        beli2009ResidueTwoSecondValues (K := K) d epsilon eta i := by
  rcases exists_residueTwoIsometricGoodBONGData d hdpos hdlt epsilon eta
    hepsilon heta with ⟨D⟩
  let C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K) := {
    carrier := ModuleCat.of K (Fin 4 → K)
    q := D.q
    L := D.L
    first := D.first
    second := D.second
    not_reachable := by
      simpa only [D.first_values, D.second_values] using
        residueTwoFirstValues_not_binaryReachable_secondValues
          hres d hdpos hdlt epsilon eta hepsilon heta
  }
  exact ⟨C, D.first_values, D.second_values⟩

/-- Unconditional form of the parameterized residue-two counterexample in
Beli's final paragraph.  The oddness hypothesis belongs to the paper's
parameter range; the invariant proof only needs positivity and `d < 2e`. -/
theorem beli2009Section5_residueTwoParametricCounterexample_proved
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d)
    (hdlt : d < 2 * ramificationIndex K) (_hdodd : Odd d)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) =
      (d : WithTop Nat))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : WithTop Nat)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i =
        beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
      ∀ i, C.second.valueUnit i =
        beli2009ResidueTwoSecondValues (K := K) d epsilon eta i :=
  exists_residueTwoBinaryTransformationCounterexample
    hres d hdpos hdlt epsilon eta hepsilon heta

/-- Unconditional existence of a residue-two binary-transformation
counterexample, obtained from the proved parameterized family. -/
theorem beli2009Section5_residueTwoCounterexample_proved
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty
      (Beli2009BinaryTransformationCounterexample.{u, u} (K := K)) :=
  beli2009Section5_residueTwoCounterexample_of_parametric
    (fun hres d hdpos hdlt hdodd epsilon eta hepsilon heta ↦
      beli2009Section5_residueTwoParametricCounterexample_proved
        hres d hdpos hdlt hdodd epsilon eta hepsilon heta)
    hres

/-- Unconditional proof of the explicit
`⟨1,1,1,1⟩ ≅ ⟨7,7,7,7⟩` counterexample over an absolutely unramified
residue-two dyadic field (in particular over `ℚ₂`). -/
theorem beli2009Section5_q2Counterexample_proved
    (htwoAdic : ramificationIndex K = 1)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i = 1) ∧
        ∀ i, C.second.valueUnit i = beli2009SevenUnit (K := K) :=
  beli2009Section5_q2Counterexample_of_parametric
    (fun hres d hdpos hdlt hdodd epsilon eta hepsilon heta ↦
      beli2009Section5_residueTwoParametricCounterexample_proved
        hres d hdpos hdlt hdodd epsilon eta hepsilon heta)
    htwoAdic hres

end ResidueTwoNonreachability

end Beli2009FinalRemarksProof

end Bong
