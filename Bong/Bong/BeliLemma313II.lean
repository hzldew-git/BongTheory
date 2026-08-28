/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma313

/-!
# Beli 2003, Lemma 3.13(ii)

This file treats the even-order comparison between `G(πᴿε)` and the shifted
norm-generator group.  The two local inputs are the parity classification of
unit defects and the even-step collapse of the principal-unit filtration.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- The exponent `-2⌊e/2-R/4⌋` in Beli (2003), Lemma 3.13(ii), written
without fractions. -/
noncomputable def beliLemma313EvenShift (R : Int) : Int :=
  -2 * ((2 * (ramificationIndex K : Int) - R) / 4)

/-- A change of uniformizer exponent by an even integer is multiplication by
a square. -/
theorem uniformizerParameter_eq_mul_square_of_eq_add_two_mul
    (R T s : Int) (ε : Kˣ) (hR : R = T + 2 * s) :
    -(uniformizerPowerUnit K R * ε) =
      (-(uniformizerPowerUnit K T * ε)) *
        uniformizerPowerUnit K s ^ 2 := by
  have hpower : uniformizerPowerUnit K R =
      uniformizerPowerUnit K T * uniformizerPowerUnit K s ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega
  rw [hpower]
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- The negative of `-1/4` is a square, so its Beli parameter defect is
infinite. -/
theorem beliParameterDefect_negativeQuarterUnit :
    beliParameterDefect K (negativeQuarterUnit K) = ⊤ := by
  unfold beliParameterDefect
  apply quadraticDefect_eq_top_of_isSquare
  let twoUnit : Kˣ := Units.mk0 (2 : K) (by norm_num)
  refine ⟨twoUnit⁻¹, ?_⟩
  apply Units.ext
  change -(-(4 : K)⁻¹) = (2 : K)⁻¹ * (2 : K)⁻¹
  norm_num

/-- The exceptional class in Lemma 3.13(ii) satisfies the same shifted
identity; both sides are the full valuation-unit square-class subgroup. -/
theorem beliSpinorGroupRepresentative_eq_evenShift_normGenerator_of_quarter
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hquarter : unitSquareClass K (uniformizerPowerUnit K R * ε) =
      unitSquareClass K (negativeQuarterUnit K)) :
    beliSpinorGroupRepresentative K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K (beliLemma313EvenShift (K := K) R) * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let T : Int := beliLemma313EvenShift (K := K) R
  let shifted : Kˣ := uniformizerPowerUnit K T * ε
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
  have hR : R = -(2 * (ramificationIndex K : Int)) := by
    rw [haOrder, ordUnit_negativeQuarterUnit] at horder
    exact horder
  have hT : T = R := by
    dsimp [T, beliLemma313EvenShift]
    rw [hR]
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hshifted : shifted = a := by
    dsimp [shifted, a]
    rw [hT]
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hquarter with ⟨s, hs, has⟩
  have hdefectScaled :=
    beliParameterDefect_mul_valuationUnit_square K a s hs
  have hdefectA : beliParameterDefect K a = ⊤ := by
    rw [has, beliParameterDefect_negativeQuarterUnit] at hdefectScaled
    exact hdefectScaled.symm
  have hshiftedNotHigh :
      ¬2 * (ramificationIndex K : Int) < ordUnit K shifted := by
    rw [hshifted, haOrder, hR]
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hdShifted :
      ¬2 * beliParameterDefect K shifted ≤
        (beliDefectCutoff K shifted : ℕ∞) := by
    rw [hshifted, hdefectA]
    simp
  have hhighExponent : beliHighDefectExponent K shifted = 0 := by
    unfold beliHighDefectExponent
    rw [hshifted, haOrder, hR]
    omega
  rw [beliSpinorGroupRepresentative_of_negativeQuarter K a ha hquarter]
  rw [beliNormGeneratorSquareClassGroup_of_high_defect
    K shifted hshiftedNotHigh hdShifted]
  rw [hhighExponent, principalUnitSquareClassSubgroup_zero]

/-- Beli (2003), Lemma 3.13(ii), away from the separately specified
exceptional class `-1/4`. -/
theorem beliSpinorGroupRepresentative_eq_evenShift_normGenerator_of_ne_quarter
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hquarter : unitSquareClass K (uniformizerPowerUnit K R * ε) ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K (beliLemma313EvenShift (K := K) R) * ε) := by
  rcases hEven with ⟨r, hr⟩
  let q : Int := (2 * (ramificationIndex K : Int) - R) / 4
  let x : Int := (ramificationIndex K : Int) - r
  let T : Int := beliLemma313EvenShift (K := K) R
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let shifted : Kˣ := uniformizerPowerUnit K T * ε
  have he : 0 ≤ (ramificationIndex K : Int) := by positivity
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hshiftedOrder : ordUnit K shifted = T :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε T
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have h := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at h
  have hn0 : 0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
  have hq0 : 0 ≤ q := by
    exact Int.ediv_nonneg hn0 (by omega)
  have hqle : q ≤ (ramificationIndex K : Int) := by
    rw [← Int.lt_add_one_iff]
    apply (Int.ediv_lt_iff_lt_mul (by omega)).2
    omega
  have hx0 : 0 ≤ x := by
    dsimp [x]
    omega
  have hxle : x ≤ 2 * (ramificationIndex K : Int) := by
    dsimp [x]
    omega
  have hdivisionLower :=
    Int.ediv_mul_le (2 * (ramificationIndex K : Int) - R)
      (by norm_num : (4 : Int) ≠ 0)
  have hdivisionUpper :
      2 * (ramificationIndex K : Int) - R <
        ((2 * (ramificationIndex K : Int) - R) / 4 + 1) * 4 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega)).1
    omega
  have hxqLower : 2 * q ≤ x := by
    dsimp [q, x]
    omega
  have hxqUpper : x ≤ 2 * q + 1 := by
    dsimp [q, x]
    omega
  have hT : T = -2 * q := by
    rfl
  have hEvenR : Even R := ⟨r, hr⟩
  have hEvenT : Even T := by
    refine ⟨-q, ?_⟩
    omega
  have hTnonpos : T ≤ 0 := by omega
  have hshiftedNotHigh :
      ¬2 * (ramificationIndex K : Int) < ordUnit K shifted := by
    rw [hshiftedOrder]
    omega
  have hdefectA : beliParameterDefect K a = quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε hEvenR
  have hdefectShifted :
      beliParameterDefect K shifted = quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) T ε hε hEvenT
  have hdefectNatA :
      beliParameterDefectNat K a = (quadraticDefect K (-ε)).toNat := by
    unfold beliParameterDefectNat
    rw [hdefectA]
  have hdefectNatShifted :
      beliParameterDefectNat K shifted =
        (quadraticDefect K (-ε)).toNat := by
    unfold beliParameterDefectNat
    rw [hdefectShifted]
  have hRrep : ordUnit K a ≤ 2 * (ramificationIndex K : Int) := by
    rwa [haOrder]
  have hdLowRep :
      ¬2 * beliParameterDefect K a ≤
        (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [haOrder, hdefectA]
    exact hdLower
  have hsquareParameter :
      -a = -shifted * uniformizerPowerUnit K (r + q) ^ 2 := by
    apply uniformizerParameter_eq_mul_square_of_eq_add_two_mul
      (K := K) R T (r + q) ε
    omega
  have hnorm : quadraticNormSquareClassSubgroup K (-a) =
      quadraticNormSquareClassSubgroup K (-shifted) := by
    rw [hsquareParameter, quadraticNormSquareClassSubgroup_mul_square]
  have hhighExponent : beliSpinorCaseIIIHighExponent K a =
      beliHighDefectExponent K shifted := by
    unfold beliSpinorCaseIIIHighExponent beliHighDefectExponent
    rw [haOrder, hshiftedOrder]
    congr 1
    dsimp [q] at hT
    omega
  by_cases htop : quadraticDefect K (-ε) = ⊤
  · have hdUpperRep :
        ¬4 * beliParameterDefect K a ≤
          (beliSpinorCaseIIIUpperCutoff K a : ℕ∞) := by
      rw [hdefectA, htop]
      simp
    have hdShifted :
        ¬2 * beliParameterDefect K shifted ≤
          (beliDefectCutoff K shifted : ℕ∞) := by
      rw [hdefectShifted, htop]
      simp
    rw [beliSpinorGroupRepresentative_caseIII_high K a ha
      hquarter hRrep hdLowRep hdUpperRep]
    rw [beliNormGeneratorSquareClassGroup_of_high_defect
      K shifted hshiftedNotHigh hdShifted]
    rw [hhighExponent]
  · let d : Nat := (quadraticDefect K (-ε)).toNat
    have hdLowerNat := hdLower
    rw [← ENat.coe_toNat htop] at hdLowerNat
    norm_cast at hdLowerNat
    have hdx : Int.toNat x < d := by
      dsimp [d]
      omega
    have hbranch :
        (4 * beliParameterDefect K a ≤
          (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)) ↔
        (2 * beliParameterDefect K shifted ≤
          (beliDefectCutoff K shifted : ℕ∞)) := by
      unfold beliSpinorCaseIIIUpperCutoff beliDefectCutoff
      rw [haOrder, hshiftedOrder, hdefectA, hdefectShifted,
        ← ENat.coe_toNat htop]
      norm_cast
      omega
    by_cases hdUpper : 4 * beliParameterDefect K a ≤
        (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)
    · have hdShifted := hbranch.mp hdUpper
      rw [beliSpinorGroupRepresentative_caseIII_middle K a ha
        hquarter hRrep hdLowRep hdUpper]
      rw [beliNormGeneratorSquareClassGroup_of_low_defect
        K shifted hshiftedNotHigh hdShifted]
      have hspinorExponent : beliSpinorCaseIIIMiddleExponent K a =
          d - Int.toNat x := by
        unfold beliSpinorCaseIIIMiddleExponent
        rw [haOrder, hdefectNatA]
        dsimp [d]
        omega
      by_cases hxEven : x = 2 * q
      · have hgeneratorExponent : beliLowDefectExponent K shifted =
            d - Int.toNat x := by
          unfold beliLowDefectExponent
          rw [hshiftedOrder, hdefectNatShifted]
          dsimp [d]
          omega
        rw [hspinorExponent, hgeneratorExponent, hnorm]
      · have hxOdd : x = 2 * q + 1 := by omega
        have hgeneratorExponent : beliLowDefectExponent K shifted =
            d - Int.toNat x + 1 := by
          unfold beliLowDefectExponent
          rw [hshiftedOrder, hdefectNatShifted]
          dsimp [d]
          omega
        have hdUpperNat := hdUpper
        rw [hdefectA, ← ENat.coe_toNat htop] at hdUpperNat
        unfold beliSpinorCaseIIIUpperCutoff at hdUpperNat
        rw [haOrder] at hdUpperNat
        norm_cast at hdUpperNat
        have hdLt : quadraticDefect K (-ε) <
            ((2 * ramificationIndex K : Nat) : ℕ∞) := by
          rw [← ENat.coe_toNat htop]
          norm_cast
          dsimp [d] at hdUpperNat ⊢
          omega
        have hdOdd : Odd d := by
          dsimp [d]
          apply quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
            (K := K) (-ε)
          · simpa [IsValuationUnit] using hε
          · exact hdLt
        have hxOddNat : Odd (Int.toNat x) := by
          refine ⟨Int.toNat q, ?_⟩
          omega
        have hkEven : Even (d - Int.toNat x) :=
          Nat.Odd.sub_odd hdOdd hxOddNat
        have hkPos : 0 < d - Int.toNat x := by omega
        have hkLt : d - Int.toNat x <
            2 * ramificationIndex K := by
          dsimp [d] at hdUpperNat ⊢
          omega
        have hfiltration :=
          principalUnitSquareClassSubgroup_eq_succ_of_even
            K (d - Int.toNat x) hkPos hkLt hkEven
        rw [hspinorExponent, hgeneratorExponent, hnorm,
          hfiltration]
    · have hdShifted :
          ¬2 * beliParameterDefect K shifted ≤
            (beliDefectCutoff K shifted : ℕ∞) := by
        exact fun h => hdUpper (hbranch.mpr h)
      rw [beliSpinorGroupRepresentative_caseIII_high K a ha
        hquarter hRrep hdLowRep hdUpper]
      rw [beliNormGeneratorSquareClassGroup_of_high_defect
        K shifted hshiftedNotHigh hdShifted]
      rw [hhighExponent]

/-- Beli (2003), Lemma 3.13(ii), including the exceptional class `-1/4`. -/
theorem beliSpinorGroupRepresentative_eq_evenShift_normGenerator
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorSquareClassGroup K
        (uniformizerPowerUnit K
          (beliLemma313EvenShift (K := K) R) * ε) := by
  by_cases hquarter :
      unitSquareClass K (uniformizerPowerUnit K R * ε) =
        unitSquareClass K (negativeQuarterUnit K)
  · exact
      beliSpinorGroupRepresentative_eq_evenShift_normGenerator_of_quarter
        R ε hε ha hquarter
  · exact
      beliSpinorGroupRepresentative_eq_evenShift_normGenerator_of_ne_quarter
        R ε hε ha hquarter hRupper hEven hdLower

end Dyadic

end Bong
