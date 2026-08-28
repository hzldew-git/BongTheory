/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryScaledShearSpinor
import Bong.Bong.BinaryDefectAdaptedShear
import Bong.Bong.BinarySpinorPositiveReduction
import Bong.Bong.BinaryDiagonalEvenShiftSpinor

/-!
# Shifted norm generators in a modular binary model

Suppose `a = shifted * t²` and a target shear `c` is divisible by `t` in
the fractional sense needed below.  Multiplication of the first coordinate

`(x,y) ↦ (t x,y)`

then carries the source model with shear `c/t` to the target model with
shear `c`, multiplying every quadratic value by `t²`.  The displayed five
integrality assumptions are exactly the two target reflection coefficients.
This is the modular counterpart of the diagonal scaled-shear construction.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Geometric shifted-model inclusion for a sheared target. -/
theorem beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryModel_of_scaledFirst
    (a shifted t : Kˣ) (c : K)
    (hsourceTwo : (2 : K) * (c / (t : K)) ∈ IntegerRing K)
    (hsourceDiag : (c / (t : K)) ^ 2 + (shifted : K) ∈ IntegerRing K)
    (htargetTwo : (2 : K) * c ∈ IntegerRing K)
    (htargetDiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hfactor : shifted * t ^ 2 = a)
    (htIntegral : (t : K) ∈ IntegerRing K)
    (htwoDivT : (2 : K) / (t : K) ∈ IntegerRing K)
    (htwoCDivTSq : (2 : K) * c / (t : K) ^ 2 ∈ IntegerRing K)
    (htwoCDivT : (2 : K) * c / (t : K) ∈ IntegerRing K)
    (htwoDDivTSq :
      (2 : K) * (c ^ 2 + (a : K)) / (t : K) ^ 2 ∈ IntegerRing K) :
    beliNormGeneratorSquareClassGroup K shifted ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) := by
  letI : BinaryNormGeneratorLocalLaws.{u, u} K :=
    binaryNormGeneratorLocalLawsProved
  let source := binaryExactModelBONG shifted (c / (t : K))
    hsourceTwo hsourceDiag
  intro A hA
  rcases hA with ⟨C, hC, rfl⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep C
  change valuationUnitClassHom K u ∈
    beliNormGeneratorGroup K shifted at hC
  have hCsource : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K source.binaryParameter := by
    rw [binaryExactModelBONG_binaryParameter]
    exact hC
  rcases source.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
      u hCsource with ⟨y, hy, hratio⟩
  have hyCoords := (mem_binaryModelLattice_iff y).1 hy.mem
  have huInvIntegral : (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
    valuationUnit_inv_mem_integerRing (u : Kˣ) u.property
  have hsourceValue :
      (QuadraticSpace.binaryModel shifted (c / (t : K))).quadratic y =
        (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
    have hratioK := congrArg Units.val hratio
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit] at hratioK
    rw [binaryExactModelBONG_value_zero, div_one] at hratioK
    simpa [source] using hratioK
  let z : Fin 2 → K := ![(t : K) * y 0, y 1]
  have hzZero : z 0 = (t : K) * y 0 := by simp [z]
  have hzOne : z 1 = y 1 := by simp [z]
  have hzMem : z ∈ binaryModelLattice (K := K) := by
    rw [mem_binaryModelLattice_iff]
    intro i
    fin_cases i
    · exact (IntegerRing K).mul_mem _ _ htIntegral (hyCoords 0)
    · exact hyCoords 1
  have hfactorK : (shifted : K) * (t : K) ^ 2 = (a : K) :=
    congrArg Units.val hfactor
  have hvalue :
      (QuadraticSpace.binaryModel a c).quadratic z =
        (t : K) ^ 2 * (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
    calc
      (QuadraticSpace.binaryModel a c).quadratic z =
          (t : K) ^ 2 *
            (QuadraticSpace.binaryModel shifted (c / (t : K))).quadratic y := by
        rw [QuadraticSpace.binaryModel_quadratic_apply,
          QuadraticSpace.binaryModel_quadratic_apply]
        simp only [hzZero, hzOne]
        rw [← hfactorK]
        field_simp [Units.ne_zero t]
      _ = (t : K) ^ 2 *
          (((u : valuationUnitSubgroup K) : Kˣ) : K) := by
        rw [hsourceValue]
  have hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z := by
    rw [QuadraticSpace.IsAnisotropic, hvalue]
    exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero t))
      (Units.ne_zero (u : Kˣ))
  have hfirstCoefficient :
      2 * (z 0 + c * z 1) /
          (QuadraticSpace.binaryModel a c).quadratic z ∈
        IntegerRing K := by
    have hfirstTerm :
        ((2 : K) / (t : K)) * y 0 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoDivT (hyCoords 0))
        huInvIntegral
    have hsecondTerm :
        ((2 : K) * c / (t : K) ^ 2) * y 1 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoCDivTSq (hyCoords 1))
        huInvIntegral
    have hadd := (IntegerRing K).add_mem _ _ hfirstTerm hsecondTerm
    rw [hzZero, hzOne, hvalue]
    convert hadd using 1
    field_simp [Units.ne_zero t, Units.ne_zero (u : Kˣ)]
  have hsecondCoefficient :
      2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
          (QuadraticSpace.binaryModel a c).quadratic z ∈
        IntegerRing K := by
    have hfirstTerm :
        ((2 : K) * c / (t : K)) * y 0 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoCDivT (hyCoords 0))
        huInvIntegral
    have hsecondTerm :
        ((2 : K) * (c ^ 2 + (a : K)) / (t : K) ^ 2) * y 1 *
            (((u : Kˣ) : K)⁻¹ : K) ∈ IntegerRing K :=
      (IntegerRing K).mul_mem _ _
        ((IntegerRing K).mul_mem _ _ htwoDDivTSq (hyCoords 1))
        huInvIntegral
    have hadd := (IntegerRing K).add_mem _ _ hfirstTerm hsecondTerm
    rw [hzZero, hzOne, hvalue]
    convert hadd using 1
    field_simp [Units.ne_zero t, Units.ne_zero (u : Kˣ)]
  have hzIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hz := by
    apply Lattice.isIntegralReflection_of_coefficient_mem_integerRing hz hzMem
    intro w hw
    have hwCoords := (mem_binaryModelLattice_iff w).1 hw
    have hcoefficient :
        2 * (QuadraticSpace.binaryModel a c).bilin z w /
            (QuadraticSpace.binaryModel a c).quadratic z =
          w 0 * (2 * (z 0 + c * z 1) /
            (QuadraticSpace.binaryModel a c).quadratic z) +
          w 1 * (2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
            (QuadraticSpace.binaryModel a c).quadratic z) := by
      rw [QuadraticSpace.binaryModel_bilin_apply]
      field_simp [hz]
      ring
    rw [hcoefficient]
    exact (IntegerRing K).add_mem _ _
      ((IntegerRing K).mul_mem _ _ (hwCoords 0) hfirstCoefficient)
      ((IntegerRing K).mul_mem _ _ (hwCoords 1) hsecondCoefficient)
  let hbase := binaryModelFirst_isAnisotropic a c
  let hbaseIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hbase :=
    (binaryModelFirst_isNormGenerator a c htargetTwo htargetDiag)
      |>.isIntegralReflection hbase
  change squareClass K (u : Kˣ) ∈
    Lattice.spinorNormImage
      (q := QuadraticSpace.binaryModel a c)
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
        ((QuadraticSpace.binaryModel a c).quadratic
          QuadraticSpace.binaryModelFirst) hbase = (1 : Kˣ) := by
      apply Units.ext
      simp
    rw [hunit]
    rfl
  rw [hbaseClass, one_mul]
  unfold Lattice.reflectionSpinorClass
  have hzUnit : Units.mk0
      ((QuadraticSpace.binaryModel a c).quadratic z) hz =
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

/-- The even shift of Lemma 3.13 maps into any admissible model of the
original parameter.  This version uses the target shear `t*c`, so it remains
valid when the original parameter has negative order. -/
theorem evenShiftedNormGeneratorGroup_le_spinorNormImage_binaryModel
    (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (c₀ : K)
    (hc₀Two : (2 : K) * c₀ ∈ IntegerRing K)
    (hc₀Diag : c₀ ^ 2 +
      ((uniformizerPowerUnit K R * ε : Kˣ) : K) ∈ IntegerRing K) :
    beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * ε) ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel
          (uniformizerPowerUnit K R * ε) c₀)
        (L := binaryModelLattice (K := K)) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rcases hEven with ⟨r, hr⟩
  let j : Int :=
    (2 * (ramificationIndex K : Int) - R) / 4
  let T : Int := beliLemma313EvenShift (K := K) R
  let s : Int := R / 2 + j
  let source : Kˣ := uniformizerPowerUnit K R * ε
  let shifted : Kˣ := uniformizerPowerUnit K T * ε
  let t : Kˣ := uniformizerPowerUnit K s
  have heNonneg : 0 ≤ (ramificationIndex K : Int) := by positivity
  have hRhalf : R / 2 = r := by omega
  have hsourceOrder : ordUnit K source = R := by
    dsimp only [source]
    exact ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have h := ha.ordUnit_ge_neg_two_mul_e
    rwa [hsourceOrder] at h
  have hnumeratorNonneg :
      0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
  have hjNonneg : 0 ≤ j := by
    exact Int.ediv_nonneg hnumeratorNonneg (by omega)
  have hdivisionLower :=
    Int.ediv_mul_le (2 * (ramificationIndex K : Int) - R)
      (by norm_num : (4 : Int) ≠ 0)
  have hdivisionUpper :
      2 * (ramificationIndex K : Int) - R <
        ((2 * (ramificationIndex K : Int) - R) / 4 + 1) * 4 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hjBound :
      2 * j ≤ (ramificationIndex K : Int) - R / 2 := by
    dsimp only [j]
    omega
  have hT : T = -2 * j := by rfl
  have hEvenT : Even T := by
    refine ⟨-j, ?_⟩
    omega
  have hsNonneg : 0 ≤ s := by
    dsimp only [s, j]
    omega
  have hsLeE : s ≤ (ramificationIndex K : Int) := by
    dsimp only [s]
    omega
  have hsLeEsubJ :
      s ≤ (ramificationIndex K : Int) - j := by
    dsimp only [s]
    omega
  have hshiftedOrder : ordUnit K shifted = T := by
    dsimp only [shifted]
    exact ordUnit_uniformizerPower_mul_valuationUnit ε hε T
  have htOrder : ordUnit K t = s := by
    exact ordUnit_uniformizerPowerUnit (K := K) s
  have hshiftedAdmissible : IsBinaryParameterAdmissible shifted := by
    dsimp only [shifted, T]
    exact beliLemma313EvenShift_isBinaryParameterAdmissible
      (K := K) R ε hε ha hRupper hdLower
  rcases exists_defectAdaptedShear shifted hshiftedAdmissible
      (by rw [hshiftedOrder]; exact hEvenT) with
    ⟨c, htwo, hdiag, hcross, _hsecond⟩
  have hcNe : c ≠ 0 := by
    intro hc
    rw [hc, mul_zero, ord_zero] at hcross
    have : (⊤ : WithTop Int) =
        (((ramificationIndex K : Int) + ordUnit K shifted / 2 : Int) :
          WithTop Int) := hcross
    exact WithTop.top_ne_coe this
  let cU : Kˣ := Units.mk0 c hcNe
  have hcOrder : ordUnit K cU = -j := by
    apply WithTop.coe_injective
    have hcross' := hcross
    rw [ord_mul, ← ramificationIndex_spec] at hcross'
    have hcOrd : ord K c = (ordUnit K cU : WithTop Int) := by
      simpa [cU] using (coe_ordUnit K cU).symm
    rw [hcOrd, hshiftedOrder, hT] at hcross'
    norm_cast at hcross' ⊢
    omega
  have hfactor : shifted * t ^ 2 = source := by
    have hpower :
        uniformizerPowerUnit K T * uniformizerPowerUnit K s ^ 2 =
          uniformizerPowerUnit K R := by
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add, ← zpow_add]
      congr 1
      dsimp only [s]
      omega
    dsimp only [shifted, t, source]
    calc
      (uniformizerPowerUnit K T * ε) *
            uniformizerPowerUnit K s ^ 2 =
          (uniformizerPowerUnit K T *
            uniformizerPowerUnit K s ^ 2) * ε := by ac_rfl
      _ = uniformizerPowerUnit K R * ε := by rw [hpower]
  have htIntegral : (t : K) ∈ IntegerRing K :=
    unit_mem_integerRing_of_ordUnit_nonneg t
      (by rw [htOrder]; exact hsNonneg)
  let targetC : K := (t : K) * c
  have htargetTwo : (2 : K) * targetC ∈ IntegerRing K := by
    have hmem := (IntegerRing K).mul_mem _ _ htIntegral htwo
    convert hmem using 1 <;> simp [targetC] <;> ring
  have htargetDiagIdentity :
      targetC ^ 2 + (source : K) =
        (t : K) ^ 2 * (c ^ 2 + (shifted : K)) := by
    have hfactorK : (shifted : K) * (t : K) ^ 2 = (source : K) :=
      congrArg Units.val hfactor
    dsimp only [targetC]
    rw [← hfactorK]
    ring
  have htSqIntegral : (t : K) ^ 2 ∈ IntegerRing K :=
    by simpa [pow_two] using
      (IntegerRing K).mul_mem _ _ htIntegral htIntegral
  have htargetDiag :
      targetC ^ 2 + (source : K) ∈ IntegerRing K := by
    rw [htargetDiagIdentity]
    exact (IntegerRing K).mul_mem _ _ htSqIntegral hdiag
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, ramificationIndex_spec]
    rfl
  have htwoDivTOrder : ordUnit K (twoU * t⁻¹) =
      (ramificationIndex K : Int) - s := by
    simp only [ordUnit_mul, ordUnit_inv, htwoOrder, htOrder]
    omega
  have htwoDivT : (2 : K) / (t : K) ∈ IntegerRing K := by
    have hmem := unit_mem_integerRing_of_ordUnit_nonneg (twoU * t⁻¹)
      (by rw [htwoDivTOrder]; omega)
    simpa [twoU, div_eq_mul_inv] using hmem
  have htwoCDivTOrder : ordUnit K (twoU * cU * t⁻¹) =
      (ramificationIndex K : Int) - j - s := by
    simp only [ordUnit_mul, ordUnit_inv, htwoOrder, hcOrder, htOrder]
    omega
  have htwoCDivT : (2 : K) * c / (t : K) ∈ IntegerRing K := by
    have hmem := unit_mem_integerRing_of_ordUnit_nonneg
      (twoU * cU * t⁻¹)
      (by rw [htwoCDivTOrder]; exact sub_nonneg.mpr hsLeEsubJ)
    simpa [twoU, cU, div_eq_mul_inv, mul_assoc] using hmem
  have htwoTargetCDivTSq :
      (2 : K) * targetC / (t : K) ^ 2 ∈ IntegerRing K := by
    convert htwoCDivT using 1
    dsimp only [targetC]
    field_simp [Units.ne_zero t]
  have htwoTargetCDivT :
      (2 : K) * targetC / (t : K) ∈ IntegerRing K := by
    convert htwo using 1
    dsimp only [targetC]
    field_simp [Units.ne_zero t]
  have htwoTargetDDivTSq :
      (2 : K) * (targetC ^ 2 + (source : K)) / (t : K) ^ 2 ∈
        IntegerRing K := by
    have htwoDiag : (2 : K) * (c ^ 2 + (shifted : K)) ∈
        IntegerRing K :=
      (IntegerRing K).mul_mem _ _ (by norm_num) hdiag
    convert htwoDiag using 1
    rw [htargetDiagIdentity]
    field_simp [Units.ne_zero t]
  have hsourceTwo :
      (2 : K) * (targetC / (t : K)) ∈ IntegerRing K := by
    convert htwo using 1
    dsimp only [targetC]
    field_simp [Units.ne_zero t]
  have hsourceDiag :
      (targetC / (t : K)) ^ 2 + (shifted : K) ∈ IntegerRing K := by
    convert hdiag using 1
    dsimp only [targetC]
    field_simp [Units.ne_zero t]
  have hinclusion :=
    beliNormGeneratorSquareClassGroup_le_spinorNormImage_binaryModel_of_scaledFirst
      source shifted t targetC hsourceTwo hsourceDiag htargetTwo htargetDiag
        hfactor htIntegral htwoDivT htwoTargetCDivTSq
          htwoTargetCDivT htwoTargetDDivTSq
  have hsub : targetC - c₀ ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing source targetC c₀
      htargetTwo htargetDiag hc₀Two hc₀Diag
  rcases binaryModel_isIsometric_of_shear_sub_integral
      source targetC c₀ hsub with ⟨f⟩
  have hspinor :
      Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel source targetC)
          (L := binaryModelLattice (K := K)) =
        Lattice.spinorNormImage
          (q := QuadraticSpace.binaryModel source c₀)
          (L := binaryModelLattice (K := K)) :=
    Lattice.spinorNormImage_eq_of_isometry f
  intro A hA
  have hmem := hinclusion hA
  change A ∈ Lattice.spinorNormImage
    (q := QuadraticSpace.binaryModel source targetC)
    (L := binaryModelLattice (K := K)) at hmem
  rw [hspinor] at hmem
  exact hmem

end BONG

end Bong
