/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.BinaryReflectionCoordinates

/-!
# Spinor classes transported from a scaled sheared binary model

Let `a = a' t^2`.  In orthogonal coordinates the integral model with
parameter `a'` and shear `c` maps to the diagonal model with parameter `a`
by

`(x,y) \mapsto (t (x + c y), y)`.

This file isolates the elementary lattice and reflection calculation behind
the shifted-model arguments in Beli (2003), Lemma 3.13.  The five explicit
integrality assumptions are later discharged by the relevant valuation
inequalities.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A valuation unit and its inverse both belong to the valuation ring. -/
theorem valuationUnit_inv_mem_integerRing (u : Kˣ)
    (hu : IsValuationUnit K (u : K)) :
    ((u : K)⁻¹ : K) ∈ IntegerRing K := by
  apply (mem_integerRing_iff K).2
  change (0 : WithTop Int) ≤ ord K ((u : K)⁻¹)
  rw [AddValuation.map_inv, hu]
  simp

/--
The geometric half of the shifted-model spinor argument.

Every norm-generator unit class of the sheared model `a',c` is represented
by an integral reflection of the diagonal model `a,0` after the coordinate
change `(x,y) ↦ (t(x+cy),y)`.  The result uses only the displayed scalar
integrality conditions; no spinor formula is assumed.
-/
theorem beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryDiagonal_of_scaledShear
    (a shifted t : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiagShifted : c ^ 2 + (shifted : K) ∈ IntegerRing K)
    (haIntegral : (a : K) ∈ IntegerRing K)
    (hfactor : shifted * t ^ 2 = a)
    (htIntegral : (t : K) ∈ IntegerRing K)
    (htcIntegral : (t : K) * c ∈ IntegerRing K)
    (htwoDivT : (2 : K) / (t : K) ∈ IntegerRing K)
    (htwoCDivT : (2 : K) * c / (t : K) ∈ IntegerRing K)
    (htwoADivTSq : (2 : K) * (a : K) / (t : K) ^ 2 ∈ IntegerRing K) :
    beliNormGeneratorSquareClassGroup K shifted ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) := by
  letI : BinaryNormGeneratorLocalLaws.{u, u} K :=
    binaryNormGeneratorLocalLawsProved
  let b := binaryExactModelBONG shifted c htwo hdiagShifted
  intro A hA
  rcases hA with ⟨C, hC, rfl⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep C
  change valuationUnitClassHom K u ∈
    beliNormGeneratorGroup K shifted at hC
  have hC' : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.binaryParameter := by
    rw [binaryExactModelBONG_binaryParameter]
    exact hC
  rcases b.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
      u hC' with ⟨y, hy, hratio⟩
  have hyMem := hy.mem
  have hyZeroIntegral : y 0 ∈ IntegerRing K :=
    (mem_binaryModelLattice_iff y).1 hyMem 0
  have hyOneIntegral : y 1 ∈ IntegerRing K :=
    (mem_binaryModelLattice_iff y).1 hyMem 1
  have huInvIntegral : (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
    valuationUnit_inv_mem_integerRing (u : Kˣ) u.property
  have hmodelValue :
      (QuadraticSpace.binaryModel shifted c).quadratic y =
        (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
    have hratioK := congrArg Units.val hratio
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit] at hratioK
    rw [binaryExactModelBONG_value_zero, div_one] at hratioK
    simpa [b] using hratioK
  let z : Fin 2 → K :=
    ![(t : K) * (y 0 + c * y 1), y 1]
  have hzZero : z 0 = (t : K) * (y 0 + c * y 1) := by simp [z]
  have hzOne : z 1 = y 1 := by simp [z]
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · have hfirst : (t : K) * y 0 ∈ IntegerRing K :=
        (IntegerRing K).mul_mem _ _ htIntegral hyZeroIntegral
      have hsecond : ((t : K) * c) * y 1 ∈ IntegerRing K :=
        (IntegerRing K).mul_mem _ _ htcIntegral hyOneIntegral
      have hadd := (IntegerRing K).add_mem _ _ hfirst hsecond
      simpa [z, mul_add, mul_assoc] using hadd
    · simpa [z] using hyOneIntegral
  have hfactorK : (shifted : K) * (t : K) ^ 2 = (a : K) := by
    exact congrArg Units.val hfactor
  have hvalue :
      (QuadraticSpace.binaryModel a 0).quadratic z =
        (t : K) ^ 2 * (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
    rw [QuadraticSpace.binaryModel_quadratic_apply]
    simp only [hzZero, hzOne]
    norm_num only [zero_mul, zero_pow, zero_add, add_zero]
    calc
      ((t : K) * (y 0 + c * y 1)) ^ 2 +
            (a : K) * y 1 ^ 2 =
          (t : K) ^ 2 *
            ((QuadraticSpace.binaryModel shifted c).quadratic y) := by
        rw [QuadraticSpace.binaryModel_quadratic_apply, ← hfactorK]
        ring
      _ = (t : K) ^ 2 *
          (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
        rw [hmodelValue]
  have hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z := by
    rw [QuadraticSpace.IsAnisotropic, hvalue]
    exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero t))
      (Units.ne_zero (u : Kˣ))
  have hfirstCoefficient :
      2 * z 0 /
          (QuadraticSpace.binaryModel a 0).quadratic z ∈
        IntegerRing K := by
    have hfirstTerm :
        ((2 : K) / (t : K)) * y 0 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoDivT hyZeroIntegral)
        huInvIntegral
    have hsecondTerm :
        ((2 : K) * c / (t : K)) * y 1 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoCDivT hyOneIntegral)
        huInvIntegral
    have hadd := (IntegerRing K).add_mem _ _ hfirstTerm hsecondTerm
    rw [hzZero, hvalue]
    convert hadd using 1
    field_simp [Units.ne_zero t, Units.ne_zero (u : Kˣ)]
  have hsecondCoefficient :
      2 * (a : K) * z 1 /
          (QuadraticSpace.binaryModel a 0).quadratic z ∈
        IntegerRing K := by
    have hterm :
        ((2 : K) * (a : K) / (t : K) ^ 2) * y 1 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoADivTSq hyOneIntegral)
        huInvIntegral
    rw [hzOne, hvalue]
    convert hterm using 1
    field_simp [Units.ne_zero t, Units.ne_zero (u : Kˣ)]
  have hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hz := by
    apply Lattice.isIntegralReflection_of_coefficient_mem_integerRing hz hzMem
    intro w hw
    have hwCoords := (mem_binaryModelLattice_iff w).1 hw
    have hcoefficient :
        2 * (QuadraticSpace.binaryModel a 0).bilin z w /
            (QuadraticSpace.binaryModel a 0).quadratic z =
          w 0 * (2 * z 0 /
            (QuadraticSpace.binaryModel a 0).quadratic z) +
          w 1 * (2 * (a : K) * z 1 /
            (QuadraticSpace.binaryModel a 0).quadratic z) := by
      rw [QuadraticSpace.binaryModel_bilin_apply]
      field_simp [hz]
      ring
    rw [hcoefficient]
    exact (IntegerRing K).add_mem _ _
      ((IntegerRing K).mul_mem _ _ (hwCoords 0) hfirstCoefficient)
      ((IntegerRing K).mul_mem _ _ (hwCoords 1) hsecondCoefficient)
  have htwoZero : (2 : K) * 0 ∈ IntegerRing K := by simp
  have hdiagA : (0 : K) ^ 2 + (a : K) ∈ IntegerRing K := by
    simpa using haIntegral
  let hbase := binaryModelFirst_isAnisotropic a 0
  let hbaseIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K)) hbase :=
    (binaryModelFirst_isNormGenerator a 0 htwoZero hdiagA)
      |>.isIntegralReflection hbase
  change squareClass K (u : Kˣ) ∈
    Lattice.spinorNormImage
      (q := QuadraticSpace.binaryModel a 0)
      (L := binaryModelLattice (K := K))
  refine ⟨Lattice.integralReflectionProduct
    hbase hbaseIntegral hz hzIntegral, ?_⟩
  change Lattice.integralSpinorNorm
      (Lattice.integralReflection hbase hbaseIntegral *
        Lattice.integralReflection hz hzIntegral) = squareClass K (u : Kˣ)
  rw [Lattice.integralSpinorNorm_mul,
    Lattice.integralSpinorNorm_integralReflection,
    Lattice.integralSpinorNorm_integralReflection]
  have hbaseClass : Lattice.reflectionSpinorClass hbase = 1 := by
    unfold Lattice.reflectionSpinorClass
    have hunit : Units.mk0
        ((QuadraticSpace.binaryModel a 0).quadratic
          QuadraticSpace.binaryModelFirst) hbase = (1 : Kˣ) := by
      apply Units.ext
      simp
    rw [hunit]
    rfl
  rw [hbaseClass, one_mul]
  unfold Lattice.reflectionSpinorClass
  have hzUnit : Units.mk0
      ((QuadraticSpace.binaryModel a 0).quadratic z) hz =
        t ^ 2 * (u : Kˣ) := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0] using hvalue
  rw [hzUnit]
  calc
    squareClass K (t ^ 2 * (u : Kˣ)) =
        squareClass K ((u : Kˣ) * t ^ 2) := by
      congr 1
      ac_rfl
    _ = squareClass K (u : Kˣ) :=
      squareClass_mul_square K (u : Kˣ) t

end BONG

end Bong
