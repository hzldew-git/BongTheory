/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NormalizedGeneratorOrders
import Bong.Lattice.Omeara9327FundamentalIdeal

/-!
# The first fundamental ideal in the normalized 93:28 calculation

O'Meara's Steps 4--7 use the orders `U₁,U₂` after the first Jordan
scale has been normalized to one.  This file translates those normalized
order cases back to the intrinsic fundamental data and specializes the
three formulas of 93:27 at the first boundary.  In particular, membership
in `f₁` is exposed as an actual scalar factorization, which is the input
needed by the coefficient changes of 93:13 and 93:19.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The valuation of the second modular parameter after normalizing the
first Jordan scale is the intrinsic first scale gap. -/
theorem relativeSecondScale_order :
    ordUnit K S.relativeSecondScale =
      S.sourceJordan.fundamentalScaleOrder 1 -
        S.sourceJordan.fundamentalScaleOrder 0 := by
  unfold relativeSecondScale fundamentalScaleOrder
  simp only [ordUnit_mul, ordUnit_inv, firstScale,
    sourceJordan_scaleGenerator]
  omega

/-- Equality of the normalized norm-generator orders is equality of the
first two intrinsic fundamental norm orders. -/
theorem fundamentalNormOrder_eq_of_normalized_eq
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) := by
  have h := S.normalizedNormOrderGap_eq_fundamentalGap
  omega

/-- A normalized gap of one is the corresponding intrinsic fundamental
norm-order gap. -/
theorem fundamentalNormOrder_eq_add_one_of_normalized_gap_one
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 1) :
    ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) + 1 := by
  have h := S.normalizedNormOrderGap_eq_fundamentalGap
  omega

/-- A normalized gap of two is the corresponding intrinsic fundamental
norm-order gap. -/
theorem fundamentalNormOrder_eq_add_two_of_normalized_gap_two
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2) :
    ordUnit K (S.sourceJordan.fundamentalNormGenerator 1) =
      ordUnit K (S.sourceJordan.fundamentalNormGenerator 0) + 2 := by
  have h := S.normalizedNormOrderGap_eq_fundamentalGap
  omega

/-- Relative second scale of order one is the adjacent-scale hypothesis
in the third case of 93:27. -/
theorem fundamentalScaleOrder_eq_add_one_of_relativeSecondScale_order_one
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    S.sourceJordan.fundamentalScaleOrder 1 =
      S.sourceJordan.fundamentalScaleOrder 0 + 1 := by
  have h := S.relativeSecondScale_order
  omega

/-- First case of 93:27 in the first-scale normalization:
`f₁ = a₂ w₁` when `U₂ = U₁`. -/
theorem firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator) :
    S.sourceJordan.fundamentalIdeal 0 =
      scalarIdeal
        (((S.firstScale⁻¹ * S.secondNormalizedNormGenerator : Kˣ) : K))
        (S.sourceJordan.fundamentalWeightIdeal 0) := by
  have hli : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by
    ext
    rfl
  have hri : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by
    ext
    rfl
  have hfund := S.fundamentalNormOrder_eq_of_normalized_eq hgap
  have h :=
    S.sourceJordan.fundamentalIdeal_eq_rightNorm_mul_leftWeight_of_equal_normOrder
      (0 : Fin (n + 1)) (by simpa only [hli, hri] using hfund)
  simpa only [hli, hri,
    sourceJordan_scaleGenerator, firstScale,
    secondNormalizedNormGenerator, pow_two, mul_assoc] using h

/-- Second case of 93:27 at the first boundary. -/
theorem firstFundamentalIdeal_eq_normProduct_of_normalized_gap_one
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 1)
    (hscale : S.sourceJordan.fundamentalScaleOrder 0 = 0) :
    S.sourceJordan.fundamentalIdeal 0 =
      principalIdeal (K := K)
        (((S.sourceJordan.fundamentalNormGenerator 0 *
          S.sourceJordan.fundamentalNormGenerator 1 : Kˣ) : K)) := by
  have hli : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by
    ext
    rfl
  have hri : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by
    ext
    rfl
  apply S.sourceJordan
    |>.fundamentalIdeal_eq_product_of_normOrder_succ_of_leftScale_zero
      (0 : Fin (n + 1))
  · simpa only [hli, hri] using
      S.fundamentalNormOrder_eq_add_one_of_normalized_gap_one hgap
  · simpa only [hli] using hscale

/-- Third case of 93:27 at the first boundary. -/
theorem firstFundamentalIdeal_eq_leftNorm_mul_rightWeight_of_normalized_gap_two
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    S.sourceJordan.fundamentalIdeal 0 =
      scalarIdeal
        (((S.firstScale⁻¹ ^ 2 *
          S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K))
        (S.sourceJordan.fundamentalWeightIdeal 1) := by
  have hli : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by
    ext
    rfl
  have hri : boundaryRightIndex (0 : Fin (n + 1)) =
      (1 : Fin (n + 2)) := by
    ext
    rfl
  have hnorm :=
    S.fundamentalNormOrder_eq_add_two_of_normalized_gap_two hgap
  have hscale' :=
    S.fundamentalScaleOrder_eq_add_one_of_relativeSecondScale_order_one hscale
  have h :=
    S.sourceJordan.fundamentalIdeal_eq_leftNorm_mul_rightWeight_of_gap_two
      (0 : Fin (n + 1)) (by simpa only [hli, hri] using hnorm)
      (by simpa only [hli, hri] using hscale')
  simpa only [hli, hri,
    sourceJordan_scaleGenerator, firstScale] using h

/-- Witness-level form of the first 93:27 case. -/
theorem exists_leftWeight_factor_of_mem_firstFundamentalIdeal_of_normalized_eq
    {z : K}
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    ∃ lambda : K,
      lambda ∈ S.sourceJordan.fundamentalWeightIdeal 0 ∧
      z = ((S.firstScale⁻¹ * S.secondNormalizedNormGenerator : Kˣ) : K) *
        lambda := by
  rw [S.firstFundamentalIdeal_eq_rightNorm_mul_leftWeight_of_normalized_eq
    hgap] at hz
  rcases hz with ⟨lambda, hlambda, hz⟩
  exact ⟨lambda, hlambda, hz.symm⟩

/-- A norm generator of the normalized unimodular first component is
integral. -/
theorem firstNormGenerator_integral :
    (S.firstNormGenerator : K) ∈ IntegerRing K := by
  have hnorm : (S.firstNormGenerator : K) ∈
      normIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice :=
    normGroupSet_subset_normIdeal _ _ S.firstNormGenerator_source.1
  have hscale : (S.firstNormGenerator : K) ∈
      scaleIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice :=
    normIdeal_le_scaleIdeal _ _ hnorm
  rw [S.sourceFirstNormalized_unimodular.scaleIdeal_eq_principal
    (by rw [S.sourceFirstNormalized_finrank]; omega)] at hscale
  have hord : (0 : WithTop Int) ≤ ord K (S.firstNormGenerator : K) := by
    simpa using ord_le_of_mem_principalIdeal
      (show (1 : K) ≠ 0 by simp) hscale
  rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit]
  simpa only [coe_ordUnit] using hord

/-- The normalized second fundamental generator already belongs to the
normalized first source norm group, by monotonicity of fundamental norm
groups and saturation. -/
theorem secondNormalizedNormGenerator_mem_sourceFirst :
    (S.secondNormalizedNormGenerator : K) ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
  have hunscaled :
      (S.sourceJordan.fundamentalNormGenerator 1 : K) ∈
        S.sourceJordan.fundamentalNormGroup 0 :=
    S.sourceJordan.fundamentalNormGroup_anti
      (show (0 : Fin (n + 2)) ≤ 1 by simp)
      (S.sourceJordan.fundamentalNormGenerator_spec 1).1
  have hcomponent :
      (S.sourceJordan.fundamentalNormGenerator 1 : K) ∈
        normGroupSet (S.sourceJordan.component 0).space
          (S.sourceJordan.component 0).lattice := by
    rw [S.sourceJordan_isSaturated 0]
    exact hunscaled
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [secondNormalizedNormGenerator, Units.val_mul,
    Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hcomponent

/-- The same normalized second generator belongs to the normalized target
first norm group. -/
theorem secondNormalizedNormGenerator_mem_targetFirst :
    (S.secondNormalizedNormGenerator : K) ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  have hunscaledSource :
      (S.sourceJordan.fundamentalNormGenerator 1 : K) ∈
        S.sourceJordan.fundamentalNormGroup 0 :=
    S.sourceJordan.fundamentalNormGroup_anti
      (show (0 : Fin (n + 2)) ≤ 1 by simp)
      (S.sourceJordan.fundamentalNormGenerator_spec 1).1
  have hgroups : S.targetJordan.fundamentalNormGroup 0 =
      S.sourceJordan.fundamentalNormGroup 0 := by
    simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
      S.residualFundamentalType.normGroup_eq (0 : Fin (n + 2))
  have hcomponent :
      (S.sourceJordan.fundamentalNormGenerator 1 : K) ∈
        normGroupSet (S.targetJordan.component 0).space
          (S.targetJordan.component 0).lattice := by
    rw [S.targetJordan_isSaturated 0, hgroups]
    exact hunscaledSource
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [secondNormalizedNormGenerator, Units.val_mul,
    Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using hcomponent

/-- Witness package used in the determinant-normalization calculation of
Steps 4 and 6.  The coefficient is normalized by the first Jordan scale;
it is integral, represented by either normalized first component, and lies
in the principal ideal generated by the normalized second norm generator. -/
structure EqualNormOrderErrorData (z : K) where
  /-- The normalized second norm generator used simultaneously in the
  fundamental-ideal factorization and in the 93:19 exchange. -/
  secondGenerator : Kˣ
  coefficient : K
  error_eq :
    z = (secondGenerator : K) * coefficient
  coefficient_integral : coefficient ∈ IntegerRing K
  coefficient_mem_sourceFirst : coefficient ∈
    normGroupSet S.sourceFirstNormalized
      (S.sourceJordan.component 0).lattice
  coefficient_mem_targetFirst : coefficient ∈
    normGroupSet S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
  coefficient_mul_relativeScale_sq_mem_secondGeneratorIdeal :
    coefficient * (S.relativeSecondScale : K) ^ 2 ∈
    principalIdeal (K := K) (secondGenerator : K)
  secondGenerator_integral :
    (secondGenerator : K) ∈ IntegerRing K
  secondGenerator_sourceSecond :
    IsNormGeneratorValue S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice secondGenerator
  secondGenerator_targetSecond :
    IsNormGeneratorValue S.targetSecondNormalized
      (S.targetJordan.component 1).lattice secondGenerator
  secondGenerator_mem_sourceFirst :
    (secondGenerator : K) ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice
  secondGenerator_mem_targetFirst :
    (secondGenerator : K) ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice

/-- Turn membership in the equal-order first fundamental ideal into all
scalar facts needed by the 93:13/93:19 determinant correction. -/
noncomputable def equalNormOrderErrorData
    (z : K)
    (hgap : ordUnit K S.secondNormalizedNormGenerator =
      ordUnit K S.firstNormGenerator)
    (hz : z ∈ S.sourceJordan.fundamentalIdeal 0) :
    S.EqualNormOrderErrorData z := by
  let hexists :=
    S.exists_leftWeight_factor_of_mem_firstFundamentalIdeal_of_normalized_eq
      hgap hz
  let lambda : K := Classical.choose hexists
  have hlambda : lambda ∈
      S.sourceJordan.fundamentalWeightIdeal 0 :=
    (Classical.choose_spec hexists).1
  have hzEq : z =
      ((S.firstScale⁻¹ * S.secondNormalizedNormGenerator : Kˣ) : K) *
        lambda :=
    (Classical.choose_spec hexists).2
  let coefficient : K := ((S.firstScale⁻¹ : Kˣ) : K) * lambda
  have hfundGap := S.fundamentalNormOrder_eq_of_normalized_eq hgap
  have hlambdaGroupSource : lambda ∈
      S.sourceJordan.fundamentalNormGroup 0 := by
    exact weightIdeal_subset_normGroupSet
      (S.sourceJordan.fundamentalNormGenerator 0)
      (S.sourceJordan.fundamentalNormGenerator_spec 0) hlambda
  have hlambdaGroupTarget : lambda ∈
      normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice := by
    rw [S.targetJordan_isSaturated 0]
    have hgroups : S.targetJordan.fundamentalNormGroup 0 =
        S.sourceJordan.fundamentalNormGroup 0 := by
      simpa only [S.residualFundamentalType.indexEquiv_apply_eq_self] using
        S.residualFundamentalType.normGroup_eq (0 : Fin (n + 2))
    rw [hgroups]
    exact hlambdaGroupSource
  have hlambdaGroupSourceComponent : lambda ∈
      normGroupSet (S.sourceJordan.component 0).space
        (S.sourceJordan.component 0).lattice := by
    rw [S.sourceJordan_isSaturated 0]
    exact hlambdaGroupSource
  have hcoefficientSource : coefficient ∈
      normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaGroupSourceComponent
  have hcoefficientTarget : coefficient ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [coefficient, Units.val_inv_eq_inv_val,
      inv_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero S.firstScale),
      one_mul] using hlambdaGroupTarget
  have hlambdaPrincipal : lambda ∈ principalIdeal (K := K)
      (S.sourceJordan.fundamentalNormGenerator 0 : K) :=
    weightIdeal_le_principalIdeal
      (S.sourceJordan.fundamentalNormGenerator 0)
      (S.sourceJordan.fundamentalNormGenerator_spec 0) hlambda
  have hcoefficientPrincipal0 : coefficient ∈ principalIdeal (K := K)
      (((S.firstScale⁻¹ *
        S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K)) := by
    rw [← scalarIdeal_principalIdeal_units]
    exact ⟨lambda, hlambdaPrincipal, rfl⟩
  have hprincipalEq : principalIdeal (K := K)
        (((S.firstScale⁻¹ *
          S.sourceJordan.fundamentalNormGenerator 0 : Kˣ) : K)) =
      principalIdeal (K := K) (S.secondNormalizedNormGenerator : K) := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mpr
    unfold secondNormalizedNormGenerator
    simp only [ordUnit_mul, ordUnit_inv]
    rw [hfundGap]
  have hcoefficientPrincipal : coefficient ∈ principalIdeal (K := K)
      (S.secondNormalizedNormGenerator : K) := by
    rw [← hprincipalEq]
    exact hcoefficientPrincipal0
  have hdeltaIntegral : (S.secondNormalizedNormGenerator : K) ∈
      IntegerRing K := by
    have hdeltaOrder : 0 ≤ ordUnit K S.secondNormalizedNormGenerator := by
      have hfirst := S.firstNormGenerator_integral
      rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit] at hfirst
      rw [hgap]
      exact WithTop.coe_nonneg.mp hfirst
    rw [mem_integerRing_iff, Dyadic.IsIntegral, ← coe_ordUnit]
    exact WithTop.coe_nonneg.mpr hdeltaOrder
  have hcoefficientIntegral : coefficient ∈ IntegerRing K := by
    have hlower := ord_le_of_mem_principalIdeal
      (Units.ne_zero S.secondNormalizedNormGenerator)
      hcoefficientPrincipal
    have hdeltaNonneg : (0 : WithTop Int) ≤
        ord K (S.secondNormalizedNormGenerator : K) := by
      rw [← coe_ordUnit]
      simpa only [Dyadic.IsIntegral, coe_ordUnit] using
        (mem_integerRing_iff K).1 hdeltaIntegral
    rw [mem_integerRing_iff]
    exact hdeltaNonneg.trans hlower
  exact
    { secondGenerator := S.secondNormalizedNormGenerator
      coefficient := coefficient
      error_eq := by
        dsimp only [coefficient]
        rw [hzEq]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        ring
      coefficient_integral := hcoefficientIntegral
      coefficient_mem_sourceFirst := hcoefficientSource
      coefficient_mem_targetFirst := hcoefficientTarget
      coefficient_mul_relativeScale_sq_mem_secondGeneratorIdeal := by
        let c : IntegerRing K :=
          ⟨(S.relativeSecondScale : K) ^ 2,
            (IntegerRing K).toSubring.pow_mem
              ((mem_integerRing_iff K).2
                (le_of_lt S.relativeSecondScale_isInMaximalIdeal)) 2⟩
        have h := (principalIdeal (K := K)
          (S.secondNormalizedNormGenerator : K)).smul_mem c
            hcoefficientPrincipal
        change (S.relativeSecondScale : K) ^ 2 * coefficient ∈
          principalIdeal (K := K)
            (S.secondNormalizedNormGenerator : K) at h
        simpa only [mul_comm] using h
      secondGenerator_integral := hdeltaIntegral
      secondGenerator_sourceSecond :=
        S.secondNormalizedNormGenerator_source
      secondGenerator_targetSecond :=
        S.secondNormalizedNormGenerator_target
      secondGenerator_mem_sourceFirst :=
        S.secondNormalizedNormGenerator_mem_sourceFirst
      secondGenerator_mem_targetFirst :=
        S.secondNormalizedNormGenerator_mem_targetFirst }

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
