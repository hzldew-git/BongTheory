/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAuxiliarySpinorGroup
import Bong.Bong.BinaryNormGeneratorSquareClass
import Bong.Bong.BinarySpinorMonotonicity

/-!
# Beli 2003, Lemma 3.13

This file begins the comparison between the auxiliary spinor group `G'` and
the norm-generator group `g`.  All exponent shifts are performed on integers
before conversion to natural filtration depths.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- Removing the valuation power from `πᴿ ε` recovers the valuation-unit
factor `ε`. -/
theorem normalizedUnitPart_uniformizerPower_mul_valuationUnit
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K)) :
    normalizedUnitPart K (uniformizerPowerUnit K R * ε) = ε := by
  rw [normalizedUnitPart,
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
  unfold uniformizerPowerUnit
  simp [mul_assoc, mul_comm]

/-- At even exponent, Beli's defect `d(-πᴿε)` equals `d(-ε)`. -/
theorem beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
    (R : Int) (ε : Kˣ) (_hε : IsValuationUnit K (ε : K))
    (hEven : Even R) :
    beliParameterDefect K (uniformizerPowerUnit K R * ε) =
      quadraticDefect K (-ε) := by
  rcases hEven with ⟨r, hr⟩
  unfold beliParameterDefect
  have hnegative : -(uniformizerPowerUnit K R * ε) =
      (-ε) * uniformizerPowerUnit K r ^ 2 := by
    have hpower : uniformizerPowerUnit K R =
        uniformizerPowerUnit K r ^ 2 := by
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add]
      congr 1
    rw [hpower]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hnegative, quadraticDefect_mul_square]

/-- Multiplying `πᴿ ε` by the square `(πᵉ)²` shifts its exponent by
`2e`. -/
theorem uniformizerParameter_shift_two_e_square
    (R : Int) (ε : Kˣ) :
    -(uniformizerPowerUnit K R * ε) =
      (-(uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) * ε)) *
        uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 := by
  have hpower : uniformizerPowerUnit K R =
      uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) *
        uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega
  rw [hpower]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- Beli (2003), Lemma 3.13(i), equality statement. -/
theorem beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hR : 2 * (ramificationIndex K : Int) < R) :
    beliAuxiliarySpinorGroup K
        (uniformizerPowerUnit K R * ε)
        (by
          rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
          exact hR) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (R - 2 * (ramificationIndex K : Int)) * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let shifted : Kˣ :=
    uniformizerPowerUnit K
      (R - 2 * (ramificationIndex K : Int)) * ε
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hshiftedOrder :
      ordUnit K shifted = R - 2 * (ramificationIndex K : Int) :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε
      (R - 2 * (ramificationIndex K : Int))
  have hdefect :
      beliParameterDefect K a = beliParameterDefect K shifted := by
    unfold beliParameterDefect
    have hsquare := uniformizerParameter_shift_two_e_square
      (K := K) R ε
    change -a = -shifted *
      uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 at hsquare
    rw [hsquare, quadraticDefect_mul_square]
  have hdefectNat :
      beliParameterDefectNat K a =
        beliParameterDefectNat K shifted := by
    unfold beliParameterDefectNat
    rw [hdefect]
  have hcutoff :
      beliSpinorCaseIICutoff K a =
        beliDefectCutoff K shifted := by
    unfold beliSpinorCaseIICutoff beliDefectCutoff
    rw [haOrder, hshiftedOrder]
    congr 1
    omega
  have hlowExponent :
      beliSpinorCaseIILowExponent K a =
        beliLowDefectExponent K shifted := by
    unfold beliSpinorCaseIILowExponent beliLowDefectExponent
    rw [haOrder, hshiftedOrder, hdefectNat]
    congr 1
    omega
  have hhighExponent :
      beliSpinorCaseIIHighExponent K a =
        beliHighDefectExponent K shifted := by
    unfold beliSpinorCaseIIHighExponent beliHighDefectExponent
    rw [haOrder, hshiftedOrder]
    congr 1
    omega
  have hnorm :
      quadraticNormSquareClassSubgroup K (-a) =
        quadraticNormSquareClassSubgroup K (-shifted) := by
    have hsquare := uniformizerParameter_shift_two_e_square
      (K := K) R ε
    change -a = -shifted *
      uniformizerPowerUnit K (ramificationIndex K : Int) ^ 2 at hsquare
    rw [hsquare, quadraticNormSquareClassSubgroup_mul_square]
  have hRrep : 2 * (ramificationIndex K : Int) < ordUnit K a := by
    rwa [haOrder]
  by_cases hRhigh : 4 * (ramificationIndex K : Int) < R
  · have hRhighRep :
        4 * (ramificationIndex K : Int) < ordUnit K a := by
      rwa [haOrder]
    have hshiftedHigh :
        2 * (ramificationIndex K : Int) < ordUnit K shifted := by
      rw [hshiftedOrder]
      omega
    rw [beliAuxiliarySpinorGroup_caseI K a hRrep hRhighRep]
    exact
      (beliNormGeneratorSquareClassGroup_of_two_e_lt
        K shifted hshiftedHigh).symm
  · have hRhighRep :
        ordUnit K a ≤ 4 * (ramificationIndex K : Int) := by
      rw [haOrder]
      omega
    have hshiftedNotHigh :
        ¬2 * (ramificationIndex K : Int) < ordUnit K shifted := by
      rw [hshiftedOrder]
      omega
    by_cases hd : 2 * beliParameterDefect K a ≤
        (beliSpinorCaseIICutoff K a : ℕ∞)
    · have hdShifted : 2 * beliParameterDefect K shifted ≤
          (beliDefectCutoff K shifted : ℕ∞) := by
        rwa [hdefect, hcutoff] at hd
      rw [beliAuxiliarySpinorGroup_caseII_low K a hRrep
        hRhighRep hd]
      rw [beliNormGeneratorSquareClassGroup_of_low_defect
        K shifted hshiftedNotHigh hdShifted]
      rw [hlowExponent, hnorm]
    · have hdShifted : ¬2 * beliParameterDefect K shifted ≤
          (beliDefectCutoff K shifted : ℕ∞) := by
        rwa [hdefect, hcutoff] at hd
      rw [beliAuxiliarySpinorGroup_caseII_high K a hRrep
        hRhighRep hd]
      rw [beliNormGeneratorSquareClassGroup_of_high_defect
        K shifted hshiftedNotHigh hdShifted]
      rw [hhighExponent]

/-- Beli (2003), Lemma 3.13(i), principal-unit upper bound. -/
theorem beliAuxiliarySpinorGroup_le_principalUnitSquareClassSubgroup
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hR : 2 * (ramificationIndex K : Int) < R) :
    beliAuxiliarySpinorGroup K
        (uniformizerPowerUnit K R * ε)
        (by
          rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
          exact hR) ≤
      principalUnitSquareClassSubgroup K
        (Int.toNat (R - 2 * (ramificationIndex K : Int))) := by
  let shifted : Kˣ :=
    uniformizerPowerUnit K
      (R - 2 * (ramificationIndex K : Int)) * ε
  have hshiftedOrder :
      ordUnit K shifted = R - 2 * (ramificationIndex K : Int) :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε
      (R - 2 * (ramificationIndex K : Int))
  have hpositive : 0 < ordUnit K shifted := by
    rw [hshiftedOrder]
    omega
  have hle :=
    beliNormGeneratorSquareClassGroup_le_principalUnitSquareClassSubgroup
      K shifted hpositive
  rw [hshiftedOrder] at hle
  rw [beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
    (K := K) R ε hε hR]
  exact hle

end Dyadic

end Bong
