/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma310
import Bong.Bong.HeHu2022SectionThreeSharp
import Bong.Bong.Beli2019Lemma712
import Bong.Bong.AdjacentNormGeneratorChange
import Bong.Bong.Beli2009FinalRemarksProof

/-!
# He--Hu (2024), Lemma 3.9

This file supplies exact good-BONG models for every coefficient list in
Lemma 3.9.  In particular, the discriminant endpoint is not recorded only up
to ordinary square class: its second coefficient is literally
`-Delta * pi^(R-2e)`.  The ternary clause similarly keeps the published
`pi^(2-2e)` normalization.
-/

namespace Bong

open Dyadic Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG.GoodBONG

/-- The two coefficients of the discriminant endpoint, with first order
`R`.  For `R=0` and `R=1` these are the two non-hyperbolic pairs displayed in
Lemma 3.9(i). -/
noncomputable def heHuDiscriminantEndpointValues
    [laws : DyadicDiscriminantClassLaws K] (R : Int) : Fin 2 → Kˣ :=
  ![uniformizerPowerUnit K R,
    -(laws.discriminantUnit *
      uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int)))]

@[simp]
theorem heHuDiscriminantEndpointValues_zero
    [DyadicDiscriminantClassLaws K] (R : Int) :
    heHuDiscriminantEndpointValues (K := K) R 0 =
      uniformizerPowerUnit K R := by
  rfl

@[simp]
theorem heHuDiscriminantEndpointValues_one
    [laws : DyadicDiscriminantClassLaws K] (R : Int) :
    heHuDiscriminantEndpointValues (K := K) R 1 =
      -(laws.discriminantUnit *
        uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int))) := by
  rfl

/-- The valuation unit `2*pi^(-e)` which converts `-Delta/4` to the
published endpoint parameter `-Delta*pi^(-2e)`. -/
noncomputable def heHuEndpointSquareUnit : Kˣ :=
  Lattice.dyadicTwoUnit (K := K) *
    uniformizerPowerUnit K (-(ramificationIndex K : Int))

theorem heHuEndpointSquareUnit_isValuationUnit :
    IsValuationUnit K (heHuEndpointSquareUnit (K := K) : K) := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K
    (heHuEndpointSquareUnit (K := K))).2
  rw [heHuEndpointSquareUnit, ordUnit_mul,
    ordUnit_uniformizerPowerUnit]
  have htwo : ordUnit K (Lattice.dyadicTwoUnit (K := K)) =
      (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact (ramificationIndex_spec K).symm
  rw [htwo]
  omega

/-- The exact endpoint parameter is the standard discriminant parameter
times the square of a valuation unit. -/
theorem heHuDiscriminantEndpoint_parameter_eq (R : Int)
    [laws : DyadicDiscriminantClassLaws K] :
    heHuDiscriminantEndpointValues (K := K) R 1 /
        heHuDiscriminantEndpointValues (K := K) R 0 =
      (negativeQuarterUnit K * laws.discriminantUnit) *
        heHuEndpointSquareUnit (K := K) ^ 2 := by
  rw [heHuDiscriminantEndpointValues_one,
    heHuDiscriminantEndpointValues_zero, heHuEndpointSquareUnit]
  have hpow :
      uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) =
        uniformizerPowerUnit K R *
          uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    ring
  have htwoQuarter :
      negativeQuarterUnit K *
          Lattice.dyadicTwoUnit (K := K) ^ 2 = (-1 : Kˣ) := by
    apply Units.ext
    simp [negativeQuarterUnit, Lattice.dyadicTwoUnit]
    norm_num
  have hrhs :
      (negativeQuarterUnit K * laws.discriminantUnit) *
          (Lattice.dyadicTwoUnit (K := K) *
            uniformizerPowerUnit K
              (-(ramificationIndex K : Int))) ^ 2 =
        -(laws.discriminantUnit *
          uniformizerPowerUnit K
            (-(ramificationIndex K : Int)) ^ 2) := by
    rw [mul_pow]
    calc
      (negativeQuarterUnit K * laws.discriminantUnit) *
          (Lattice.dyadicTwoUnit (K := K) ^ 2 *
            uniformizerPowerUnit K
              (-(ramificationIndex K : Int)) ^ 2) =
        (negativeQuarterUnit K *
          Lattice.dyadicTwoUnit (K := K) ^ 2) *
            laws.discriminantUnit *
              uniformizerPowerUnit K
                (-(ramificationIndex K : Int)) ^ 2 := by ac_rfl
      _ = -(laws.discriminantUnit *
          uniformizerPowerUnit K
            (-(ramificationIndex K : Int)) ^ 2) := by
        rw [htwoQuarter]
        simp
  calc
    -(laws.discriminantUnit *
        uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int))) /
        uniformizerPowerUnit K R =
      -(laws.discriminantUnit *
        uniformizerPowerUnit K
          (-(ramificationIndex K : Int)) ^ 2) := by
        rw [hpow]
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = (negativeQuarterUnit K * laws.discriminantUnit) *
        (Lattice.dyadicTwoUnit (K := K) *
          uniformizerPowerUnit K
            (-(ramificationIndex K : Int))) ^ 2 := hrhs.symm

/-- Admissibility of the literal endpoint pair. -/
theorem heHuDiscriminantEndpoint_admissible (R : Int)
    [laws : DyadicDiscriminantClassLaws K] :
    IsBinaryParameterAdmissible
      (heHuDiscriminantEndpointValues (K := K) R 1 /
        heHuDiscriminantEndpointValues (K := K) R 0) := by
  rw [heHuDiscriminantEndpoint_parameter_eq (K := K) R]
  apply (isBinaryParameterAdmissible_mul_valuationUnit_square_iff
    (negativeQuarterUnit K * laws.discriminantUnit)
    (heHuEndpointSquareUnit (K := K))
    (heHuEndpointSquareUnit_isValuationUnit (K := K))).2
  simpa [lemma712DiscriminantParameter] using
    (lemma712_sourceBinaryAdmissible (K := K) 1)

/-- The exact discriminant-endpoint good BONG. -/
noncomputable def heHuDiscriminantEndpointGoodBONG (R : Int)
    [DyadicDiscriminantClassLaws K] :
    GoodBONG
      (binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) R 0)
        (heHuDiscriminantEndpointValues (K := K) R 1)
        (heHuDiscriminantEndpoint_admissible (K := K) R))
      (binaryDiagonalModelLattice (K := K)) 2 :=
  binaryDiagonalExactGoodBONG
    (heHuDiscriminantEndpointValues (K := K) R 0)
    (heHuDiscriminantEndpointValues (K := K) R 1)
    (heHuDiscriminantEndpoint_admissible (K := K) R)

@[simp]
theorem heHuDiscriminantEndpointGoodBONG_valueUnit
    [DyadicDiscriminantClassLaws K] (R : Int) (i : Fin 2) :
    (heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit i =
      heHuDiscriminantEndpointValues (K := K) R i := by
  have h := binaryDiagonalExactGoodBONG_valueUnit
    (heHuDiscriminantEndpointValues (K := K) R 0)
    (heHuDiscriminantEndpointValues (K := K) R 1)
    (heHuDiscriminantEndpoint_admissible (K := K) R) i
  change
    (heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit i = _
  calc
    _ = ![heHuDiscriminantEndpointValues (K := K) R 0,
          heHuDiscriminantEndpointValues (K := K) R 1] i := by
      exact h
    _ = heHuDiscriminantEndpointValues (K := K) R i := by
      fin_cases i <;> rfl

@[simp]
theorem heHuDiscriminantEndpointGoodBONG_order
    [laws : DyadicDiscriminantClassLaws K] (R : Int) (i : Fin 2) :
    (heHuDiscriminantEndpointGoodBONG (K := K) R).order i =
      ![R, R - 2 * (ramificationIndex K : Int)] i := by
  change (heHuDiscriminantEndpointGoodBONG (K := K) R).toBONG.order i = _
  rw [BONG.order_eq_ordUnit]
  change ordUnit K
    ((heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit i) = _
  rw [heHuDiscriminantEndpointGoodBONG_valueUnit]
  fin_cases i
  · change ordUnit K (uniformizerPowerUnit K R) = R
    rw [ordUnit_uniformizerPowerUnit]
  · change ordUnit K
      (-(laws.discriminantUnit * uniformizerPowerUnit K
        (R - 2 * (ramificationIndex K : Int)))) =
        R - 2 * (ramificationIndex K : Int)
    rw [ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit]
    have hdelta : ordUnit K laws.discriminantUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
        laws.discriminant_isValuationUnit
    rw [hdelta]
    simp

/-- The literal endpoint model belongs to the fixed standard
`2^-1*pi^R*A(2,2rho)` lattice. -/
theorem heHuDiscriminantEndpoint_isIsometric_standard (R : Int)
    [laws : DyadicDiscriminantClassLaws K] :
    Lattice.IsIsometric
      (binaryDiagonalModelSpace
        (heHuDiscriminantEndpointValues (K := K) R 0)
        (heHuDiscriminantEndpointValues (K := K) R 1)
        (heHuDiscriminantEndpoint_admissible (K := K) R))
      ((heHuDiscriminantEndpointGoodBONG (K := K) R).toBONG
        |>.standardEndpointModelSpace
          (negativeQuarterUnit K * laws.discriminantUnit))
      (binaryDiagonalModelLattice (K := K))
      (binaryModelLattice (K := K)) := by
  let b := heHuDiscriminantEndpointGoodBONG (K := K) R
  apply b.toBONG.isIsometric_standardEndpointModel
  · dsimp only [b]
    unfold BONG.binaryUnitSquareClass BONG.binaryParameter
    change unitSquareClass K
        ((heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit 1 /
          (heHuDiscriminantEndpointGoodBONG (K := K) R).valueUnit 0) = _
    rw [heHuDiscriminantEndpointGoodBONG_valueUnit,
      heHuDiscriminantEndpointGoodBONG_valueUnit]
    rw [heHuDiscriminantEndpoint_parameter_eq (K := K) R]
    exact unitSquareClass_mul_unit_square K
      (negativeQuarterUnit K * laws.discriminantUnit)
      (heHuEndpointSquareUnit (K := K))
      (heHuEndpointSquareUnit_isValuationUnit (K := K))
  · exact standardEndpointShear_two_integral (K := K)
  · exact discriminant_standardEndpointShear_diagonal_integral (K := K)

/-- A diagonal binary pair occurring in Lemma 3.9(ii). -/
noncomputable def heHuUnitUniformizerPairValues
    (a δ : Kˣ) : Fin 2 → Kˣ :=
  ![a, -(a * δ * uniformizerPowerUnit K 1)]

@[simp]
theorem heHuUnitUniformizerPairValues_zero (a δ : Kˣ) :
    heHuUnitUniformizerPairValues (K := K) a δ 0 = a := by
  rfl

@[simp]
theorem heHuUnitUniformizerPairValues_one (a δ : Kˣ) :
    heHuUnitUniformizerPairValues (K := K) a δ 1 =
      -(a * δ * uniformizerPowerUnit K 1) := by
  rfl

theorem heHuUnitUniformizerPair_admissible (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) :
    IsBinaryParameterAdmissible
      (heHuUnitUniformizerPairValues (K := K) a δ 1 /
        heHuUnitUniformizerPairValues (K := K) a δ 0) := by
  apply isBinaryParameterAdmissible_of_ordUnit_nonneg
  rw [heHuUnitUniformizerPairValues_one,
    heHuUnitUniformizerPairValues_zero, div_eq_mul_inv,
    ordUnit_mul, ordUnit_neg, ordUnit_mul, ordUnit_mul,
    ordUnit_inv, ordUnit_uniformizerPowerUnit]
  have ha0 := (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha
  have hδ0 := (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ
  rw [ha0, hδ0]
  norm_num

/-- Exact good BONG for either diagonal pair in Lemma 3.9(ii). -/
noncomputable def heHuUnitUniformizerPairGoodBONG (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) :
    GoodBONG
      (binaryDiagonalModelSpace
        (heHuUnitUniformizerPairValues (K := K) a δ 0)
        (heHuUnitUniformizerPairValues (K := K) a δ 1)
        (heHuUnitUniformizerPair_admissible a δ ha hδ))
      (binaryDiagonalModelLattice (K := K)) 2 :=
  binaryDiagonalExactGoodBONG
    (heHuUnitUniformizerPairValues (K := K) a δ 0)
    (heHuUnitUniformizerPairValues (K := K) a δ 1)
    (heHuUnitUniformizerPair_admissible a δ ha hδ)

@[simp]
theorem heHuUnitUniformizerPairGoodBONG_valueUnit (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) (i : Fin 2) :
    (heHuUnitUniformizerPairGoodBONG a δ ha hδ).valueUnit i =
      heHuUnitUniformizerPairValues (K := K) a δ i := by
  have h := binaryDiagonalExactGoodBONG_valueUnit
    (heHuUnitUniformizerPairValues (K := K) a δ 0)
    (heHuUnitUniformizerPairValues (K := K) a δ 1)
    (heHuUnitUniformizerPair_admissible a δ ha hδ) i
  calc
    _ = ![heHuUnitUniformizerPairValues (K := K) a δ 0,
          heHuUnitUniformizerPairValues (K := K) a δ 1] i := h
    _ = heHuUnitUniformizerPairValues (K := K) a δ i := by
      fin_cases i <;> rfl

@[simp]
theorem heHuUnitUniformizerPairGoodBONG_orders (a δ : Kˣ)
    (ha : IsValuationUnit K (a : K))
    (hδ : IsValuationUnit K (δ : K)) (i : Fin 2) :
    (heHuUnitUniformizerPairGoodBONG a δ ha hδ).order i =
      ![0, 1] i := by
  change (heHuUnitUniformizerPairGoodBONG a δ ha hδ).toBONG.order i = _
  rw [BONG.order_eq_ordUnit]
  change ordUnit K
    ((heHuUnitUniformizerPairGoodBONG a δ ha hδ).valueUnit i) = _
  rw [heHuUnitUniformizerPairGoodBONG_valueUnit]
  fin_cases i
  · change ordUnit K a = 0
    exact (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha
  · change ordUnit K (-(a * δ * uniformizerPowerUnit K 1)) = 1
    rw [ordUnit_neg, ordUnit_mul, ordUnit_mul,
      ordUnit_uniformizerPowerUnit,
      (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha,
      (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ]
    norm_num

/-- Lemma 3.9(i), with all three literal coefficient lists and both endpoint
isometry identifications exposed in one checked result. -/
theorem heHu2022Lemma39i
    [laws : DyadicDiscriminantClassLaws K] :
    ((heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 0 = 1 ∧
      (heHuHyperbolicHeadGoodBONG (K := K)).valueUnit 1 =
        -(uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int))))) ∧
    ((heHuDiscriminantEndpointGoodBONG (K := K) 0).valueUnit 0 = 1 ∧
      (heHuDiscriminantEndpointGoodBONG (K := K) 0).valueUnit 1 =
        -(laws.discriminantUnit * uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int))))) ∧
    ((heHuDiscriminantEndpointGoodBONG (K := K) 1).valueUnit 0 =
        uniformizerPowerUnit K 1 ∧
      (heHuDiscriminantEndpointGoodBONG (K := K) 1).valueUnit 1 =
        -(laws.discriminantUnit * uniformizerPowerUnit K
          (1 - 2 * (ramificationIndex K : Int)))) := by
  constructor
  · exact ⟨heHuHyperbolicHeadGoodBONG_value_zero (K := K),
      heHuHyperbolicHeadGoodBONG_value_one (K := K)⟩
  constructor
  · constructor <;>
      rw [heHuDiscriminantEndpointGoodBONG_valueUnit] <;>
      simp [heHuDiscriminantEndpointValues, uniformizerPowerUnit]
  · constructor <;>
      rw [heHuDiscriminantEndpointGoodBONG_valueUnit] <;>
      simp [heHuDiscriminantEndpointValues]

/-- Lemma 3.9(ii), simultaneously for `[1,-delta*pi]` and
`[Delta,-Delta*delta*pi]`. -/
theorem heHu2022Lemma39ii
    [laws : DyadicDiscriminantClassLaws K]
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) :
    ((heHuUnitUniformizerPairGoodBONG (1 : Kˣ) δ
        (by simp [IsValuationUnit]) hδ).valueUnit 0 = 1 ∧
      (heHuUnitUniformizerPairGoodBONG (1 : Kˣ) δ
        (by simp [IsValuationUnit]) hδ).valueUnit 1 =
          -(δ * uniformizerPowerUnit K 1)) ∧
    ((heHuUnitUniformizerPairGoodBONG laws.discriminantUnit δ
        laws.discriminant_isValuationUnit hδ).valueUnit 0 =
          laws.discriminantUnit ∧
      (heHuUnitUniformizerPairGoodBONG laws.discriminantUnit δ
        laws.discriminant_isValuationUnit hδ).valueUnit 1 =
          -(laws.discriminantUnit * δ * uniformizerPowerUnit K 1)) := by
  constructor
  · constructor <;>
      rw [heHuUnitUniformizerPairGoodBONG_valueUnit] <;>
      simp [heHuUnitUniformizerPairValues]
  · constructor <;>
      rw [heHuUnitUniformizerPairGoodBONG_valueUnit] <;>
      simp [heHuUnitUniformizerPairValues]

/-! ## The exact ternary clause -/

/-- The two Beli parameters obtained from the published `kappa#` and
`kappa` after removing the two discriminant factors in Lemma 7.12(ii). -/
noncomputable def heHuLemma39iiiEpsilon
    [laws : DyadicDiscriminantClassLaws K] (κSharp : Kˣ) : Kˣ :=
  κSharp / laws.discriminantUnit

noncomputable def heHuLemma39iiiEta
    [laws : DyadicDiscriminantClassLaws K] (κ : Kˣ) : Kˣ :=
  κ / laws.discriminantUnit

/-- The coefficient list printed in He--Hu, Lemma 3.9(iii). -/
noncomputable def heHuLemma39iiiValues
    (δ κ κSharp : Kˣ) : Fin 3 → Kˣ :=
  ![δ * κSharp,
    -(δ * κSharp * κ *
      uniformizerPowerUnit K
        (2 - 2 * (ramificationIndex K : Int))),
    δ * κ]

@[simp]
theorem heHuLemma39iiiValues_zero (δ κ κSharp : Kˣ) :
    heHuLemma39iiiValues (K := K) δ κ κSharp 0 =
      δ * κSharp := by
  rfl

@[simp]
theorem heHuLemma39iiiValues_one (δ κ κSharp : Kˣ) :
    heHuLemma39iiiValues (K := K) δ κ κSharp 1 =
      -(δ * κSharp * κ *
        uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int))) := by
  rfl

@[simp]
theorem heHuLemma39iiiValues_two (δ κ κSharp : Kˣ) :
    heHuLemma39iiiValues (K := K) δ κ κSharp 2 =
      δ * κ := by
  rfl

/-- The source unary coefficient in Lemma 7.12 is `Delta*delta`. -/
noncomputable def heHuLemma39iiiSourceUnary
    [laws : DyadicDiscriminantClassLaws K] (δ : Kˣ) : Kˣ :=
  laws.discriminantUnit * δ

/-- Coordinate factors converting Beli's normalized target to the literal
He--Hu target. -/
noncomputable def heHuLemma39iiiSquareFactors : Fin 3 → Kˣ :=
  ![1, heHuEndpointSquareUnit (K := K), 1]

/-- The published coefficient list differs from the normalized Beli 7.12
list exactly by the indicated valuation-unit squares. -/
theorem heHuLemma39iiiValues_eq_normalized_mul_square
    [laws : DyadicDiscriminantClassLaws K] (δ κ κSharp : Kˣ) (i : Fin 3) :
    heHuLemma39iiiValues (K := K) δ κ κSharp i =
      lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ) i *
        heHuLemma39iiiSquareFactors (K := K) i ^ 2 := by
  have htwoQuarter :
      negativeQuarterUnit K *
          Lattice.dyadicTwoUnit (K := K) ^ 2 = (-1 : Kˣ) := by
    apply Units.ext
    simp [negativeQuarterUnit, Lattice.dyadicTwoUnit]
    norm_num
  have hpowers :
      uniformizerPowerUnit K 2 *
          uniformizerPowerUnit K (-(ramificationIndex K : Int)) ^ 2 =
        uniformizerPowerUnit K
          (2 - 2 * (ramificationIndex K : Int)) := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    ring
  fin_cases i
  · simp [heHuLemma39iiiValues, heHuLemma39iiiSourceUnary,
      heHuLemma39iiiEpsilon, heHuLemma39iiiEta,
      heHuLemma39iiiSquareFactors, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]
  · change
      -(δ * κSharp * κ *
          uniformizerPowerUnit K
            (2 - 2 * (ramificationIndex K : Int))) =
        (lemma712DiscriminantParameter (K := K) *
          uniformizerPowerUnit K 2 *
          (laws.discriminantUnit * δ) *
          (κSharp / laws.discriminantUnit) *
          (κ / laws.discriminantUnit)) *
            heHuEndpointSquareUnit (K := K) ^ 2
    rw [lemma712DiscriminantParameter, heHuEndpointSquareUnit, mul_pow]
    symm
    calc
      (negativeQuarterUnit K * laws.discriminantUnit *
          uniformizerPowerUnit K 2 *
          (laws.discriminantUnit * δ) *
          (κSharp / laws.discriminantUnit) *
          (κ / laws.discriminantUnit)) *
          (Lattice.dyadicTwoUnit (K := K) ^ 2 *
            uniformizerPowerUnit K
              (-(ramificationIndex K : Int)) ^ 2) =
        (negativeQuarterUnit K *
          Lattice.dyadicTwoUnit (K := K) ^ 2) *
          (δ * κSharp * κ) *
          (uniformizerPowerUnit K 2 *
            uniformizerPowerUnit K
              (-(ramificationIndex K : Int)) ^ 2) := by
        simp only [div_eq_mul_inv]
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = -(δ * κSharp * κ *
          uniformizerPowerUnit K
            (2 - 2 * (ramificationIndex K : Int))) := by
        rw [htwoQuarter, hpowers]
        simp
  · simp [heHuLemma39iiiValues, heHuLemma39iiiSourceUnary,
      heHuLemma39iiiEpsilon, heHuLemma39iiiEta,
      heHuLemma39iiiSquareFactors, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]

/-- All three coordinate factors are valuation units. -/
theorem heHuLemma39iiiSquareFactors_isValuationUnit (i : Fin 3) :
    IsValuationUnit K (heHuLemma39iiiSquareFactors (K := K) i : K) := by
  fin_cases i
  · simp [heHuLemma39iiiSquareFactors, IsValuationUnit]
  · simpa [heHuLemma39iiiSquareFactors] using
      heHuEndpointSquareUnit_isValuationUnit (K := K)
  · simp [heHuLemma39iiiSquareFactors, IsValuationUnit]

/-- Hence the published diagonal space represents the normalized target
diagonal space. -/
theorem heHuLemma39iiiValues_diagonalRepresents_normalized
    [DyadicDiscriminantClassLaws K] (δ κ κSharp : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma39iiiValues (K := K) δ κ κSharp))
      (diagonalUnitCoefficients
        (lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ))) :=
  Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heHuLemma39iiiValues (K := K) δ κ κSharp)
    (lemma712TargetValues
      (heHuLemma39iiiSourceUnary (K := K) δ)
      (heHuLemma39iiiEpsilon (K := K) κSharp)
      (heHuLemma39iiiEta (K := K) κ))
    (heHuLemma39iiiSquareFactors (K := K))
    (heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp)

theorem heHuLemma39iiiEpsilon_isValuationUnit
    [laws : DyadicDiscriminantClassLaws K] (κSharp : Kˣ)
    (hκSharp : IsValuationUnit K (κSharp : K)) :
    IsValuationUnit K (heHuLemma39iiiEpsilon (K := K) κSharp : K) := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K
    (heHuLemma39iiiEpsilon (K := K) κSharp)).2
  rw [heHuLemma39iiiEpsilon, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    (isValuationUnit_iff_ordUnit_eq_zero K κSharp).1 hκSharp,
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit]
  simp

theorem heHuLemma39iiiEta_isValuationUnit
    [laws : DyadicDiscriminantClassLaws K] (κ : Kˣ)
    (hκ : IsValuationUnit K (κ : K)) :
    IsValuationUnit K (heHuLemma39iiiEta (K := K) κ : K) := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K
    (heHuLemma39iiiEta (K := K) κ)).2
  rw [heHuLemma39iiiEta, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
    (isValuationUnit_iff_ordUnit_eq_zero K κ).1 hκ,
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit]
  simp

private theorem heHuDiscriminant_defectOrder
    [laws : DyadicDiscriminantClassLaws K] :
    defectOrder (K := K) laws.discriminantUnit =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  unfold defectOrder
  rw [laws.discriminant_defect]
  rfl

/-- Division by `Delta` does not change the complementary defect `1`. -/
theorem heHuLemma39iiiEpsilon_defect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K] (κSharp : Kˣ)
    (hκSharpDefect : defectOrder (K := K) κSharp = (1 : WithTop ℚ)) :
    defectOrder (K := K)
        (heHuLemma39iiiEpsilon (K := K) κSharp) =
      (1 : WithTop ℚ) := by
  rw [heHuLemma39iiiEpsilon, div_eq_mul_inv,
    defectOrder_mul_eq_left_of_lt_right]
  exact hκSharpDefect
  rw [defectOrder_inv, hκSharpDefect,
    heHuDiscriminant_defectOrder (K := K)]
  have hePos := ramificationIndex_pos (K := K)
  exact_mod_cast (show (1 : ℚ) < 2 * (ramificationIndex K : ℚ) by
    norm_cast
    omega)

/-- Division by `Delta` does not change the defect `2e-1`. -/
theorem heHuLemma39iiiEta_defect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K] (κ : Kˣ)
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    defectOrder (K := K) (heHuLemma39iiiEta (K := K) κ) =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
  rw [heHuLemma39iiiEta, div_eq_mul_inv,
    defectOrder_mul_eq_left_of_lt_right]
  exact hκDefect
  rw [defectOrder_inv, hκDefect,
    heHuDiscriminant_defectOrder (K := K)]
  exact_mod_cast (show
    2 * (ramificationIndex K : ℚ) - 1 <
      2 * (ramificationIndex K : ℚ) by linarith)

/-- Removing the two discriminant factors preserves the negative Hilbert
symbol required by Beli's ternary realization. -/
theorem heHuLemma39iiiEpsilonEta_hilbert
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K] [HilbertSymbolLaws K]
    (κ κSharp : Kˣ)
    (hκ : IsValuationUnit K (κ : K))
    (hκSharp : IsValuationUnit K (κSharp : K))
    (hhilbert : hilbertSymbol K κSharp κ = -1) :
    hilbertSymbol K
        (heHuLemma39iiiEpsilon (K := K) κSharp)
        (heHuLemma39iiiEta (K := K) κ) = -1 := by
  have hinvLeft (a b : Kˣ) :
      hilbertSymbol K a⁻¹ b = hilbertSymbol K a b := by
    have hinv := map_inv (hilbertCharacter K b) a
    change hilbertSymbol K b a⁻¹ = (hilbertSymbol K b a)⁻¹ at hinv
    calc
      hilbertSymbol K a⁻¹ b = hilbertSymbol K b a⁻¹ :=
        hilbertSymbol_comm K _ _
      _ = (hilbertSymbol K b a)⁻¹ := hinv
      _ = (hilbertSymbol K a b)⁻¹ := by
        rw [hilbertSymbol_comm K b a]
      _ = hilbertSymbol K a b := by
        rcases Int.units_eq_one_or (hilbertSymbol K a b) with h | h <;>
          rw [h] <;> norm_num
  have hdelta (x : Kˣ) (hx : IsValuationUnit K (x : K)) :
      hilbertSymbol K laws.discriminantUnit x = 1 := by
    apply (hilbertSymbol_discriminant_eq_one_iff_even_order x).2
    rw [(isValuationUnit_iff_ordUnit_eq_zero K x).1 hx]
    exact ⟨0, by omega⟩
  rw [heHuLemma39iiiEpsilon, heHuLemma39iiiEta,
    div_eq_mul_inv]
  calc
    hilbertSymbol K (κSharp * laws.discriminantUnit⁻¹)
        (κ * laws.discriminantUnit⁻¹) =
      hilbertSymbol K κSharp (κ * laws.discriminantUnit⁻¹) *
        hilbertSymbol K laws.discriminantUnit⁻¹
          (κ * laws.discriminantUnit⁻¹) :=
      hilbertSymbol_mul_left K κSharp laws.discriminantUnit⁻¹
        (κ * laws.discriminantUnit⁻¹)
    _ = (hilbertSymbol K κSharp κ *
          hilbertSymbol K κSharp laws.discriminantUnit⁻¹) *
        (hilbertSymbol K laws.discriminantUnit⁻¹ κ *
          hilbertSymbol K laws.discriminantUnit⁻¹
            laws.discriminantUnit⁻¹) := by
      rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
    _ = hilbertSymbol K κSharp κ := by
      rw [hilbertSymbol_comm K κSharp laws.discriminantUnit⁻¹,
        hinvLeft,
        hdelta κSharp hκSharp,
        hinvLeft, hdelta κ hκ,
        hinvLeft,
        hilbertSymbol_comm K laws.discriminantUnit
          laws.discriminantUnit⁻¹,
        hinvLeft,
        hdelta laws.discriminantUnit laws.discriminant_isValuationUnit]
      simp
    _ = -1 := hhilbert

/-- Orders of the three literal coefficients in Lemma 3.9(iii). -/
theorem heHuLemma39iiiValues_orders
    (δ κ κSharp : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκSharp : IsValuationUnit K (κSharp : K)) (i : Fin 3) :
    ordUnit K (heHuLemma39iiiValues (K := K) δ κ κSharp i) =
      ![0, 2 - 2 * (ramificationIndex K : Int), 0] i := by
  have hδ0 := (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ
  have hκ0 := (isValuationUnit_iff_ordUnit_eq_zero K κ).1 hκ
  have hκSharp0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K κSharp).1 hκSharp
  fin_cases i
  · change ordUnit K (δ * κSharp) = 0
    rw [ordUnit_mul, hδ0, hκSharp0]
    simp
  · change ordUnit K
      (- (δ * κSharp * κ * uniformizerPowerUnit K
        (2 - 2 * (ramificationIndex K : Int)))) = _
    rw [ordUnit_neg, ordUnit_mul, ordUnit_mul, ordUnit_mul,
      ordUnit_uniformizerPowerUnit, hδ0, hκ0, hκSharp0]
    simp
  · change ordUnit K (δ * κ) = 0
    rw [ordUnit_mul, hδ0, hκ0]
    simp

theorem heHuLemma39iii_firstParameter_eq_normalized
    [DyadicDiscriminantClassLaws K] (δ κ κSharp : Kˣ) :
    heHuLemma39iiiValues (K := K) δ κ κSharp 1 /
        heHuLemma39iiiValues (K := K) δ κ κSharp 0 =
      (lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ) 1 /
        lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ) 0) *
        heHuEndpointSquareUnit (K := K) ^ 2 := by
  rw [heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 1,
    heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 0]
  simp [heHuLemma39iiiSquareFactors, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

theorem heHuLemma39iii_secondParameter_eq_normalized
    [DyadicDiscriminantClassLaws K] (δ κ κSharp : Kˣ) :
    heHuLemma39iiiValues (K := K) δ κ κSharp 2 /
        heHuLemma39iiiValues (K := K) δ κ κSharp 1 =
      (lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ) 2 /
        lemma712TargetValues
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (heHuLemma39iiiEpsilon (K := K) κSharp)
          (heHuLemma39iiiEta (K := K) κ) 1) *
        ((heHuEndpointSquareUnit (K := K))⁻¹) ^ 2 := by
  rw [heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 2,
    heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 1]
  simp [heHuLemma39iiiSquareFactors, div_eq_mul_inv, mul_inv_rev,
    inv_pow, mul_assoc, mul_comm, mul_left_comm]

/-- Both literal adjacent ratios are admissible. -/
theorem heHuLemma39iiiValues_binaryAdmissible
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (δ κ κSharp : Kˣ)
    (hκ : IsValuationUnit K (κ : K))
    (hκSharp : IsValuationUnit K (κSharp : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
      IsBinaryParameterAdmissible
        (heHuLemma39iiiValues (K := K) δ κ κSharp
            ⟨i.1 + 1, hi⟩ /
          heHuLemma39iiiValues (K := K) δ κ κSharp i) := by
  let ε := heHuLemma39iiiEpsilon (K := K) κSharp
  let η := heHuLemma39iiiEta (K := K) κ
  have hεUnit : IsValuationUnit K (ε : K) :=
    heHuLemma39iiiEpsilon_isValuationUnit κSharp hκSharp
  have hηUnit : IsValuationUnit K (η : K) :=
    heHuLemma39iiiEta_isValuationUnit κ hκ
  have hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) :=
    heHuLemma39iiiEta_defect κ hκDefect
  have hnormalized := lemma712TargetValues_binaryAdmissible
    (heHuLemma39iiiSourceUnary (K := K) δ) ε η
      hεUnit hηUnit hηDefect
  intro i hi
  have hiCases : i = (0 : Fin 3) ∨ i = (1 : Fin 3) := by
    have hval : i.val = 0 ∨ i.val = 1 := by omega
    rcases hval with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hiCases with rfl | rfl
  · change IsBinaryParameterAdmissible
      (heHuLemma39iiiValues (K := K) δ κ κSharp 1 /
        heHuLemma39iiiValues (K := K) δ κ κSharp 0)
    rw [heHuLemma39iii_firstParameter_eq_normalized]
    apply (isBinaryParameterAdmissible_mul_valuationUnit_square_iff
      _ (heHuEndpointSquareUnit (K := K))
      (heHuEndpointSquareUnit_isValuationUnit (K := K))).2
    simpa [ε, η] using hnormalized (0 : Fin 3) (by omega)
  · change IsBinaryParameterAdmissible
      (heHuLemma39iiiValues (K := K) δ κ κSharp 2 /
        heHuLemma39iiiValues (K := K) δ κ κSharp 1)
    rw [heHuLemma39iii_secondParameter_eq_normalized]
    have hinvUnit : IsValuationUnit K
        (((heHuEndpointSquareUnit (K := K))⁻¹ : Kˣ) : K) := by
      rw [IsValuationUnit, Units.val_inv_eq_inv_val,
        AddValuation.map_inv,
        heHuEndpointSquareUnit_isValuationUnit (K := K)]
      simp
    apply (isBinaryParameterAdmissible_mul_valuationUnit_square_iff
      _ ((heHuEndpointSquareUnit (K := K))⁻¹) hinvUnit).2
    simpa [ε, η] using hnormalized (1 : Fin 3) (by omega)

/-- The first literal signed adjacent product has defect `2e-1`. -/
theorem heHuLemma39iiiValues_firstAdjacentDefect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (δ κ κSharp : Kˣ)
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    defectOrder (K := K)
        (-(heHuLemma39iiiValues (K := K) δ κ κSharp 0 *
          heHuLemma39iiiValues (K := K) δ κ κSharp 1)) =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
  let a := heHuLemma39iiiSourceUnary (K := K) δ
  let ε := heHuLemma39iiiEpsilon (K := K) κSharp
  let η := heHuLemma39iiiEta (K := K) κ
  have hfactor :
      -(heHuLemma39iiiValues (K := K) δ κ κSharp 0 *
          heHuLemma39iiiValues (K := K) δ κ κSharp 1) =
        (-(lemma712TargetValues a ε η 0 *
          lemma712TargetValues a ε η 1)) *
            heHuEndpointSquareUnit (K := K) ^ 2 := by
    rw [heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 0,
      heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 1]
    simp [heHuLemma39iiiSquareFactors, a, ε, η,
      mul_assoc, mul_comm, mul_left_comm]
  rw [hfactor, defectOrder_mul_square]
  apply lemma712TargetValues_firstAdjacentDefect
  exact heHuLemma39iiiEta_defect κ hκDefect

/-- The second literal signed adjacent product has defect `1`. -/
theorem heHuLemma39iiiValues_secondAdjacentDefect
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    (δ κ κSharp : Kˣ)
    (hκSharpDefect : defectOrder (K := K) κSharp = (1 : WithTop ℚ)) :
    defectOrder (K := K)
        (-(heHuLemma39iiiValues (K := K) δ κ κSharp 1 *
          heHuLemma39iiiValues (K := K) δ κ κSharp 2)) =
      (1 : WithTop ℚ) := by
  let a := heHuLemma39iiiSourceUnary (K := K) δ
  let ε := heHuLemma39iiiEpsilon (K := K) κSharp
  let η := heHuLemma39iiiEta (K := K) κ
  have hfactor :
      -(heHuLemma39iiiValues (K := K) δ κ κSharp 1 *
          heHuLemma39iiiValues (K := K) δ κ κSharp 2) =
        (-(lemma712TargetValues a ε η 1 *
          lemma712TargetValues a ε η 2)) *
            heHuEndpointSquareUnit (K := K) ^ 2 := by
    rw [heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 1,
      heHuLemma39iiiValues_eq_normalized_mul_square δ κ κSharp 2]
    simp [heHuLemma39iiiSquareFactors, a, ε, η,
      mul_assoc, mul_comm, mul_left_comm]
  rw [hfactor, defectOrder_mul_square]
  apply lemma712TargetValues_secondAdjacentDefect
  exact heHuLemma39iiiEpsilon_defect κSharp hκSharpDefect

/-- He--Hu, Lemma 3.9(iii), first in a form allowing any representative
`kappaSharp` with the three properties supplied by Proposition 3.2.  The
source is the reordered literal lattice
`<Delta*delta> ⊥ 2^-1*pi*A(2,2rho)` and the resulting good BONG has the
three coefficients printed in the published paper. -/
theorem exists_heHu2022Lemma39iii_goodBONG
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ κSharp : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκSharp : IsValuationUnit K (κSharp : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hκSharpDefect : defectOrder (K := K) κSharp = (1 : WithTop ℚ))
    (hhilbert : hilbertSymbol K κSharp κ = -1) :
    ∃ b : GoodBONG
        (unaryBinaryModelSpace
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (uniformizerPowerUnit K 1)
          (uniformizerPowerUnit K 1 *
            lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible
            (uniformizerPowerUnit K 1)))
        (unaryBinaryModelLattice (K := K)) 3,
      ∀ i, b.valueUnit i = heHuLemma39iiiValues (K := K) δ κ κSharp i := by
  let a := heHuLemma39iiiSourceUnary (K := K) δ
  let p := uniformizerPowerUnit K 1
  let ε := heHuLemma39iiiEpsilon (K := K) κSharp
  let η := heHuLemma39iiiEta (K := K) κ
  let values := heHuLemma39iiiValues (K := K) δ κ κSharp
  have hdeltaOrder : ordUnit K laws.discriminantUnit = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K laws.discriminantUnit).1
      laws.discriminant_isValuationUnit
  have hδOrder : ordUnit K δ = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ
  have haOrder : ordUnit K a = 0 := by
    dsimp [a, heHuLemma39iiiSourceUnary]
    rw [ordUnit_mul, hdeltaOrder, hδOrder]
    simp
  have hp : ordUnit K p = ordUnit K a + 1 := by
    dsimp [p]
    rw [ordUnit_uniformizerPowerUnit, haOrder]
    simp
  have hεUnit : IsValuationUnit K (ε : K) :=
    heHuLemma39iiiEpsilon_isValuationUnit κSharp hκSharp
  have hηUnit : IsValuationUnit K (η : K) :=
    heHuLemma39iiiEta_isValuationUnit κ hκ
  have hεDefect : defectOrder (K := K) ε = (1 : WithTop ℚ) :=
    heHuLemma39iiiEpsilon_defect κSharp hκSharpDefect
  have hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) :=
    heHuLemma39iiiEta_defect κ hκDefect
  have hεηHilbert : hilbertSymbol K ε η = -1 :=
    heHuLemma39iiiEpsilonEta_hilbert κ κSharp hκ hκSharp hhilbert
  let sourceData := lemma712SourceJordanData a p hp
  let reference := sourceData.goodBONG
  have hpublishedNormalized :=
    heHuLemma39iiiValues_diagonalRepresents_normalized
      (K := K) δ κ κSharp
  have hnormalizedSource := lemma712Target_diagonalRepresents_source
    a p ε η hp hεUnit hηUnit hεηHilbert
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients values)
      (diagonalUnitCoefficients reference.valueUnit) := by
    have hsourceBasis : DiagonalRepresents
        (diagonalUnitCoefficients (lemma712SourceValues a p))
        (diagonalUnitCoefficients reference.valueUnit) := by
      let sourceBasis := lemma712SourceOrthogonalBasisData a p
      have h := sourceBasis.diagonalRepresents_bong reference.toBONG
      have hx : sourceBasis.valueUnit = lemma712SourceValues a p := by
        funext i
        exact lemma712SourceOrthogonalBasisData_valueUnit a p i
      rw [hx] at h
      exact h
    exact hpublishedNormalized.trans_exact
      (hnormalizedSource.trans_exact hsourceBasis)
  let R : Int := 0
  let S : Int := 2 - 2 * (ramificationIndex K : Int)
  have horders : ∀ i, ordUnit K (values i) = ![R, S, R] i := by
    intro i
    simpa [values, R, S] using
      heHuLemma39iiiValues_orders δ κ κSharp hδ hκ hκSharp i
  have hadmissible : ∀ (i : Fin 3) (hi : i.1 + 1 < 3),
      IsBinaryParameterAdmissible
        (values ⟨i.1 + 1, hi⟩ / values i) := by
    simpa [values] using
      heHuLemma39iiiValues_binaryAdmissible
        δ κ κSharp hκ hκSharp hκDefect
  have hhalf :
      (((((S - R : Int) : ℚ) / 2 + ramificationIndex K : ℚ)) :
          WithTop ℚ) = (((1 : Int) : ℚ) : WithTop ℚ) := by
    apply congrArg WithTop.some
    dsimp [S, R]
    push_cast
    ring
  have hleft :
      ((((S - R : Int) : ℚ) : WithTop ℚ) +
          defectOrder (K := K) (-(values 0 * values 1))) =
        (((1 : Int) : ℚ) : WithTop ℚ) := by
    rw [show defectOrder (K := K) (-(values 0 * values 1)) =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) by
      simpa [values] using
        heHuLemma39iiiValues_firstAdjacentDefect
          δ κ κSharp hκDefect]
    apply congrArg WithTop.some
    dsimp [S, R]
    push_cast
    ring
  have hright : defectOrder (K := K) (-(values 1 * values 2)) =
      (((1 : Int) : ℚ) : WithTop ℚ) := by
    simpa [values] using
      heHuLemma39iiiValues_secondAdjacentDefect
        δ κ κSharp hκSharpDefect
  rcases exists_exactTernaryRealization reference values R S 1
      hrep horders hadmissible hhalf hleft hright with ⟨target⟩
  have hsameOrders : reference.SameOrders target.bong := by
    intro i
    calc
      reference.order i =
          ![ordUnit K a,
            ordUnit K a + 2 - 2 * (ramificationIndex K : Int),
            ordUnit K a] i := by
        simpa [reference, sourceData] using
          lemma712SourceGoodBONG_order a p hp i
      _ = ![R, S, R] i := by
        rw [haOrder]
        fin_cases i <;> rfl
      _ = target.bong.order i := (target.orders i).symm
  have houter : reference.order (0 : Fin 3) = reference.order 2 := by
    rw [hsameOrders (0 : Fin 3), hsameOrders (2 : Fin 3),
      target.orders (0 : Fin 3), target.orders (2 : Fin 3)]
    rfl
  have halpha : reference.alphaValue (0 : Fin 2) =
      target.bong.alphaValue 0 := by
    calc
      reference.alphaValue (0 : Fin 2) = 1 := by
        simpa [reference, sourceData] using
          lemma712SourceGoodBONG_alpha a p hp
      _ = target.bong.alphaValue 0 := by
        simpa using target.firstAlpha.symm
  have hisometric : Lattice.IsIsometric
      (unaryBinaryModelSpace a p
        (p * lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible p))
      (unaryBinaryModelSpace a p
        (p * lemma712DiscriminantParameter (K := K))
        (lemma712_sourceBinaryAdmissible p))
      (unaryBinaryModelLattice (K := K)) target.lattice :=
    (reference.beli2019Lemma711 target.bong hsameOrders houter).2 halpha
  rcases hisometric with ⟨f⟩
  let result := target.bong.mapLatticeIsometry f.symm
  refine ⟨result, ?_⟩
  intro i
  apply Units.ext
  change (target.bong.toBONG.mapLatticeIsometry f.symm).value i =
    ((values i : Kˣ) : K)
  rw [BONG.value_mapLatticeIsometry]
  exact congrArg Units.val (target.valueUnits i)

/-- A unit of defect `2e-1` lies in the domain on which He--Hu define
`kappa#`. -/
theorem heHuSharpDomain_of_defect_twoE_sub_one
    [QuadraticDefectLaws K] (κ : Kˣ)
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    HeHuSharpDomain κ := by
  constructor
  · intro hsquare
    have htop := defectOrder_eq_top_of_isSquare (K := K) hsquare
    rw [hκDefect] at htop
    exact WithTop.coe_ne_top htop
  · intro hdiscriminantSquare
    rcases hdiscriminantSquare with ⟨s, hs⟩
    have hκEq : κ =
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit *
          s ^ 2 := by
      calc
        κ = (κ /
            (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit) *
            (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit := by
          simp
        _ = (s * s) *
            (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit :=
          congrArg (fun t : Kˣ => t *
            (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit) hs
        _ = (Dyadic.dyadicDiscriminantClassLawsProved
              (K := K)).discriminantUnit *
            s ^ 2 := by
          simp [pow_two, mul_comm, mul_assoc]
    have h := hκDefect
    rw [hκEq, defectOrder_mul_square,
      heHuDiscriminant_defectOrder (K := K)
        (laws := Dyadic.dyadicDiscriminantClassLawsProved)] at h
    have hq := WithTop.coe_eq_coe.mp h
    push_cast at hq
    linarith

/-- The canonical `kappa#` chosen in Definition 3.1 has defect `1` when
`d(kappa)=2e-1`. -/
theorem heHuSharp_defect_one_of_defect_twoE_sub_one
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (κ : Kˣ)
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
    defectOrder (K := K) (heHuSharp κ hc) = (1 : WithTop ℚ) := by
  let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
  have hsourceTop :
      (((heHuSharpData κ hc).sourceDefect : ℚ) : WithTop ℚ) =
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) :=
    (heHuSharpData κ hc).source_defectOrder.symm.trans hκDefect
  have hsource : (heHuSharpData κ hc).sourceDefect =
      2 * (ramificationIndex K : ℚ) - 1 :=
    WithTop.coe_eq_coe.mp hsourceTop
  dsimp only
  rw [(heHu2022Proposition32 κ hc).2.1, hsource]
  congr 1
  ring

/-- Direct canonical form of He--Hu, Lemma 3.9(iii). -/
theorem heHu2022Lemma39iii
    [laws : DyadicDiscriminantClassLaws K]
    [QuadraticDefectLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    (δ κ : Kˣ)
    (hδ : IsValuationUnit K (δ : K))
    (hκ : IsValuationUnit K (κ : K))
    (hκDefect : defectOrder (K := K) κ =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
    ∃ b : GoodBONG
        (unaryBinaryModelSpace
          (heHuLemma39iiiSourceUnary (K := K) δ)
          (uniformizerPowerUnit K 1)
          (uniformizerPowerUnit K 1 *
            lemma712DiscriminantParameter (K := K))
          (lemma712_sourceBinaryAdmissible
            (uniformizerPowerUnit K 1)))
        (unaryBinaryModelLattice (K := K)) 3,
      ∀ i, b.valueUnit i =
        heHuLemma39iiiValues (K := K) δ κ (heHuSharp κ hc) i := by
  let hc := heHuSharpDomain_of_defect_twoE_sub_one κ hκDefect
  have hsharp := heHu2022Proposition32 κ hc
  apply exists_heHu2022Lemma39iii_goodBONG
    δ κ (heHuSharp κ hc) hδ hκ hsharp.1 hκDefect
  · exact heHuSharp_defect_one_of_defect_twoE_sub_one κ hκDefect
  · exact hsharp.2.2

end BONG.GoodBONG

end Bong
