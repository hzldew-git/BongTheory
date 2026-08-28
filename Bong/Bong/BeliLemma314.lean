/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma313II
import Bong.Dyadic.HilbertCongruenceProof

/-!
# Beli 2003, Lemma 3.14

This file proves the product formula for Beli's norm-generator groups.  The
proof follows the three cases in the paper and uses Lemmas 1.2(iii), 1.3(i),
and 1.3(ii) through `BeliHilbertCongruenceLaws`.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

/-- The factor `(1 + 𝔭^(R+d))Kˣ²/Kˣ²` in Lemma 3.14.  At infinite
defect the paper's congruence factor consists only of squares. -/
noncomputable def beliLemma314CongruenceFactor
    (R : Int) (d : ℕ∞) : Subgroup (SquareClass K) :=
  if d = ⊤ then ⊥ else
    principalUnitSquareClassSubgroup K
      (Int.toNat (R + (d.toNat : Int)))

@[simp]
theorem beliLemma314CongruenceFactor_top (R : Int) :
    beliLemma314CongruenceFactor (K := K) R ⊤ = ⊥ := by
  simp [beliLemma314CongruenceFactor]

theorem beliLemma314CongruenceFactor_of_ne_top
    (R : Int) (d : ℕ∞) (hd : d ≠ ⊤) :
    beliLemma314CongruenceFactor (K := K) R d =
      principalUnitSquareClassSubgroup K
        (Int.toNat (R + (d.toNat : Int))) := by
  simp [beliLemma314CongruenceFactor, hd]

end Dyadic

namespace BONG

/-- The finite-defect part of Beli's admissibility criterion implies
`ord(a) + d(-a) ≥ 0`. -/
theorem IsBinaryParameterAdmissible.order_add_parameterDefect_nonneg
    [QuadraticDefectLaws K] {a : Kˣ}
    (ha : BONG.IsBinaryParameterAdmissible a)
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    0 ≤ ordUnit K a + ((beliParameterDefect K a).toNat : Int) := by
  have habsolute :=
    (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      a).1 ha |>.2
  have hthreshold :=
    (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le (-a)).1
      habsolute
  have hfiniteDefect : quadraticDefect K (-a) ≠ ⊤ := by
    simpa [beliParameterDefect] using hfinite
  have horderNeg : ordUnit K (-a) = ordUnit K a := by
    apply WithTop.coe_injective
    simpa using ord_neg K (a : K)
  by_cases hnonneg : 0 ≤ ordUnit K a
  · positivity
  · have hneg : ordUnit K a < 0 := lt_of_not_ge hnonneg
    have hthresholdInt :
        (absoluteDefectThreshold (-a) : Int) = -ordUnit K a := by
      have h := coe_absoluteDefectThreshold_eq_neg_of_neg
        (K := K) (a := -a) (by rwa [horderNeg])
      rwa [horderNeg] at h
    rw [← ENat.coe_toNat hfiniteDefect] at hthreshold
    norm_cast at hthreshold
    have hthresholdIntLe :
        (absoluteDefectThreshold (-a) : Int) ≤
          ((quadraticDefect K (-a)).toNat : Int) := by
      exact_mod_cast hthreshold
    rw [hthresholdInt] at hthresholdIntLe
    change 0 ≤ ordUnit K a +
      ((quadraticDefect K (-a)).toNat : Int)
    omega

/-- Below the maximal finite defect, Beli's low-branch exponent is strictly
positive.  The excluded depth-zero case would force an even valuation to be
the negative of an odd unit-defect depth. -/
theorem IsBinaryParameterAdmissible.lowDefectExponent_pos_of_lt_twoE
    [QuadraticDefectLaws K] {a : Kˣ}
    (ha : BONG.IsBinaryParameterAdmissible a)
    (hlt : beliParameterDefect K a <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    0 < Int.toNat
      (ordUnit K a + ((beliParameterDefect K a).toNat : Int)) := by
  have hfinite : beliParameterDefect K a ≠ ⊤ :=
    ne_top_of_lt (hlt.trans (ENat.coe_lt_top _))
  have hnonneg := ha.order_add_parameterDefect_nonneg hfinite
  by_contra hnotPos
  have hzero : Int.toNat
      (ordUnit K a + ((beliParameterDefect K a).toNat : Int)) = 0 :=
    Nat.eq_zero_of_not_pos hnotPos
  have hsumZero :
      ordUnit K a + ((beliParameterDefect K a).toNat : Int) = 0 := by
    have hnonpos := Int.toNat_eq_zero.mp hzero
    omega
  have horderNeg : ordUnit K (-a) = ordUnit K a := by
    apply WithTop.coe_injective
    simpa using ord_neg K (a : K)
  rcases Int.even_or_odd (ordUnit K (-a)) with heven | hodd
  · have hdefectOdd :=
        quadraticDefect_toNat_odd_of_even_ordUnit_of_lt_two_mul_e
          (K := K) (-a) heven (by
            simpa [beliParameterDefect] using hlt)
    have horderEven : Even (ordUnit K a) := by
      rwa [horderNeg] at heven
    have hdefectOddInt :
        Odd ((beliParameterDefect K a).toNat : Int) := by
      exact_mod_cast hdefectOdd
    have hsumOdd := horderEven.add_odd hdefectOddInt
    rw [hsumZero] at hsumOdd
    norm_num at hsumOdd
  · have hdefectZero :=
        quadraticDefect_eq_zero_of_odd_ordUnit (-a) hodd
    have hparameterZero : beliParameterDefect K a = 0 := by
      simpa [beliParameterDefect] using hdefectZero
    rw [hparameterZero] at hsumZero
    simp only [ENat.toNat_zero, Nat.cast_zero, add_zero] at hsumZero
    rw [horderNeg, hsumZero] at hodd
    norm_num at hodd

end BONG

namespace Dyadic

/-- The product of the two norm parameters differs from `εη` by the square
of `πᴿ`. -/
theorem negative_uniformizerParameters_mul_eq_unitProduct_mul_square
    (R : Int) (ε η : Kˣ) :
    (-(uniformizerPowerUnit K R * η)) *
        (-(uniformizerPowerUnit K R * ε)) =
      (ε * η) * uniformizerPowerUnit K R ^ 2 := by
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

/-- Consequently the product norm parameter has defect `d(εη)`. -/
theorem quadraticDefect_negative_uniformizerParameters_mul
    (R : Int) (ε η : Kˣ) :
    quadraticDefect K
        ((-(uniformizerPowerUnit K R * η)) *
          (-(uniformizerPowerUnit K R * ε))) =
      quadraticDefect K (ε * η) := by
  rw [negative_uniformizerParameters_mul_eq_unitProduct_mul_square,
    quadraticDefect_mul_square]

/-- The same square change identifies the corresponding norm subgroups. -/
theorem quadraticNorm_negative_uniformizerParameters_mul
    (R : Int) (ε η : Kˣ) :
    quadraticNormSquareClassSubgroup K
        ((-(uniformizerPowerUnit K R * η)) *
          (-(uniformizerPowerUnit K R * ε))) =
      quadraticNormSquareClassSubgroup K (ε * η) := by
  rw [negative_uniformizerParameters_mul_eq_unitProduct_mul_square,
    quadraticNormSquareClassSubgroup_mul_square]

/-- Exact defect domination identifies `d(εη)` with the smaller parameter
defect when the two parameter defects differ. -/
theorem quadraticDefect_unitProduct_eq_parameterDefect_of_lt
    (R : Int) (ε η : Kˣ)
    (hdefect :
      beliParameterDefect K (uniformizerPowerUnit K R * ε) <
        beliParameterDefect K (uniformizerPowerUnit K R * η)) :
    quadraticDefect K (ε * η) =
      beliParameterDefect K (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  have hAB : beliParameterDefect K a < beliParameterDefect K b := by
    simpa [a, b] using hdefect
  have hexact : quadraticDefect K ((-a) * (-b)) =
      beliParameterDefect K a := by
    unfold beliParameterDefect at hAB ⊢
    exact quadraticDefect_mul_eq_left_of_lt_right (K := K) hAB
  calc
    quadraticDefect K (ε * η) =
        quadraticDefect K ((-b) * (-a)) :=
      (quadraticDefect_negative_uniformizerParameters_mul
        (K := K) R ε η).symm
    _ = quadraticDefect K ((-a) * (-b)) := by rw [mul_comm]
    _ = beliParameterDefect K a := hexact
    _ = beliParameterDefect K
        (uniformizerPowerUnit K R * ε) := rfl

/-- The unequal-defect case of Lemma 3.14.  The smaller defect is placed
first; its low branch and the second generator span the full congruence
layer at depth `R + d(-a)`. -/
theorem beliNormGeneratorSquareClassGroup_sup_eq_principal_of_defect_lt
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hdefect :
      beliParameterDefect K (uniformizerPowerUnit K R * ε) <
        beliParameterDefect K (uniformizerPowerUnit K R * η))
    (hlow :
      2 * beliParameterDefect K (uniformizerPowerUnit K R * ε) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * η) =
      principalUnitSquareClassSubgroup K
        (Int.toNat
          (R + ((beliParameterDefect K
            (uniformizerPowerUnit K R * ε)).toNat : Int))) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  let dA : Nat := (beliParameterDefect K a).toNat
  let dB : Nat := (beliParameterDefect K b).toNat
  let kA : Nat := Int.toNat (R + (dA : Int))
  let kB : Nat := Int.toNat (R + (dB : Int))
  let high : Nat := Int.toNat
    ((ramificationIndex K : Int) + R / 2)
  let H : Subgroup (SquareClass K) :=
    principalUnitSquareClassSubgroup K kA
  have hdefectAB : beliParameterDefect K a <
      beliParameterDefect K b := by
    simpa [a, b] using hdefect
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hbOrder : ordUnit K b = R :=
    ordUnit_uniformizerPower_mul_valuationUnit η hη R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have hbound := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at hbound
  have hnotHighA : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rwa [haOrder, not_lt]
  have hnotHighB : ¬2 * (ramificationIndex K : Int) < ordUnit K b := by
    rwa [hbOrder, not_lt]
  have hfiniteA : beliParameterDefect K a ≠ ⊤ :=
    ne_top_of_lt hdefectAB
  have hnonnegA : 0 ≤ R + (dA : Int) := by
    dsimp [dA]
    rw [← haOrder]
    exact ha.order_add_parameterDefect_nonneg hfiniteA
  have hlowA :
      2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
    unfold beliDefectCutoff
    rwa [haOrder]
  have hlowExponentA : beliLowDefectExponent K a = kA := by
    unfold beliLowDefectExponent beliParameterDefectNat
    rw [haOrder]
  have hgA : beliNormGeneratorSquareClassGroup K a =
      H ⊓ quadraticNormSquareClassSubgroup K (-a) := by
    rw [beliNormGeneratorSquareClassGroup_of_low_defect
      K a hnotHighA hlowA]
    rw [hlowExponentA]
  have hproductDefect : quadraticDefect K ((-b) * (-a)) =
      beliParameterDefect K a := by
    unfold beliParameterDefect at hdefectAB ⊢
    simpa [mul_comm] using
      quadraticDefect_mul_eq_left_of_lt_right (K := K) hdefectAB
  by_cases hlowB :
      2 * beliParameterDefect K b ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞)
  · have hfiniteB : beliParameterDefect K b ≠ ⊤ := by
      intro htop
      rw [htop] at hlowB
      simp at hlowB
    have hnonnegB : 0 ≤ R + (dB : Int) := by
      dsimp [dB]
      rw [← hbOrder]
      exact hb.order_add_parameterDefect_nonneg hfiniteB
    have hlowB' :
        2 * beliParameterDefect K b ≤
          (beliDefectCutoff K b : ℕ∞) := by
      unfold beliDefectCutoff
      rwa [hbOrder]
    have hlowExponentB : beliLowDefectExponent K b = kB := by
      unfold beliLowDefectExponent beliParameterDefectNat
      rw [hbOrder]
    have hgB : beliNormGeneratorSquareClassGroup K b =
        principalUnitSquareClassSubgroup K kB ⊓
          quadraticNormSquareClassSubgroup K (-b) := by
      rw [beliNormGeneratorSquareClassGroup_of_low_defect
        K b hnotHighB hlowB']
      rw [hlowExponentB]
    have hdefectNat : dA < dB := by
      have h := hdefectAB
      rw [← ENat.coe_toNat hfiniteA,
        ← ENat.coe_toNat hfiniteB] at h
      exact_mod_cast h
    have hk : kA ≤ kB := by
      dsimp [kA, kB]
      omega
    have hgBleH : beliNormGeneratorSquareClassGroup K b ≤ H := by
      rw [hgB]
      exact inf_le_left.trans
        (principalUnitSquareClassSubgroup_anti K hk)
    have hlowBNat := hlowB
    rw [← ENat.coe_toNat hfiniteB] at hlowBNat
    norm_cast at hlowBNat
    have hkBpos : 0 < kB := by
      dsimp [kB, dA, dB] at hnonnegA hnonnegB hdefectNat ⊢
      omega
    have hnotPA :
        ¬principalUnitSquareClassSubgroup K kB ≤
          quadraticNormSquareClassSubgroup K (-a) := by
      rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff K (-a) kB hkBpos]
      change ¬((2 * ramificationIndex K : Nat) : ℕ∞) <
        beliParameterDefect K a + kB
      rw [← ENat.coe_toNat hfiniteA]
      norm_cast
      dsimp [kB, dB] at hnonnegB ⊢
      omega
    have hnotPProduct :
        ¬principalUnitSquareClassSubgroup K kB ≤
          quadraticNormSquareClassSubgroup K ((-b) * (-a)) := by
      rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K ((-b) * (-a)) kB hkBpos,
        hproductDefect, ← ENat.coe_toNat hfiniteA]
      norm_cast
      dsimp [kB, dB] at hnonnegB ⊢
      omega
    have hnotgB :
        ¬beliNormGeneratorSquareClassGroup K b ≤
          quadraticNormSquareClassSubgroup K (-a) := by
      intro hcontra
      have hinclusion :
          quadraticNormSquareClassSubgroup K (-b) ⊓
              principalUnitSquareClassSubgroup K kB ≤
            quadraticNormSquareClassSubgroup K (-a) := by
        simpa [hgB, inf_comm] using hcontra
      rcases
          (quadraticNorm_inf_le_quadraticNorm_iff
            K (-b) (-a)
              (principalUnitSquareClassSubgroup K kB)).1 hinclusion with
        hfirst | hsecond
      · exact hnotPA hfirst
      · exact hnotPProduct hsecond
    have hnotKer :
        ¬beliNormGeneratorSquareClassGroup K b ≤
          (squareClassHilbertCharacter K (-a)).ker := by
      rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
      exact hnotgB
    rw [hgA, quadraticNormSquareClassSubgroup_eq_ker]
    exact inf_ker_sup_eq_of_le_of_not_le
      (squareClassHilbertCharacter K (-a)) H
        (beliNormGeneratorSquareClassGroup K b) hgBleH hnotKer
  · have hgB : beliNormGeneratorSquareClassGroup K b =
        principalUnitSquareClassSubgroup K high := by
      rw [beliNormGeneratorSquareClassGroup_of_high_defect
        K b hnotHighB]
      · unfold beliHighDefectExponent
        rw [hbOrder]
      · unfold beliDefectCutoff
        rwa [hbOrder]
    have hlowNat := hlow
    rw [← ENat.coe_toNat hfiniteA] at hlowNat
    norm_cast at hlowNat
    have hk : kA ≤ high := by
      dsimp [kA, high, dA] at hnonnegA ⊢
      omega
    have hgBleH : beliNormGeneratorSquareClassGroup K b ≤ H := by
      rw [hgB]
      exact principalUnitSquareClassSubgroup_anti K hk
    by_cases hhighZero : high = 0
    · have hkAZero : kA = 0 := Nat.eq_zero_of_le_zero (by
        simpa [hhighZero] using hk)
      change beliNormGeneratorSquareClassGroup K a ⊔
          beliNormGeneratorSquareClassGroup K b = H
      rw [hgA, hgB, hhighZero]
      rw [show H = principalUnitSquareClassSubgroup K 0 by
        simp [H, hkAZero]]
      exact sup_eq_right.mpr inf_le_left
    · have hhighPos : 0 < high := Nat.pos_of_ne_zero hhighZero
      have hnotgB :
          ¬beliNormGeneratorSquareClassGroup K b ≤
            quadraticNormSquareClassSubgroup K (-a) := by
        rw [hgB,
          principalUnitSquareClassSubgroup_le_quadraticNorm_iff
            K (-a) high hhighPos]
        change ¬((2 * ramificationIndex K : Nat) : ℕ∞) <
          beliParameterDefect K a + high
        rw [← ENat.coe_toNat hfiniteA]
        norm_cast
        dsimp [high, dA] at hnonnegA ⊢
        omega
      have hnotKer :
          ¬beliNormGeneratorSquareClassGroup K b ≤
            (squareClassHilbertCharacter K (-a)).ker := by
        rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
        exact hnotgB
      rw [hgA, quadraticNormSquareClassSubgroup_eq_ker]
      exact inf_ker_sup_eq_of_le_of_not_le
        (squareClassHilbertCharacter K (-a)) H
          (beliNormGeneratorSquareClassGroup K b) hgBleH hnotKer

/-- Case (1) of Beli's proof: if both parameter defects are above the
Definition 6 cutoff, both groups are the same high principal-unit layer and
the product-defect factor is contained in it. -/
theorem beliNormGeneratorSquareClassGroup_sup_high_high
    [QuadraticDefectLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hhighA :
      ¬2 * beliParameterDefect K (uniformizerPowerUnit K R * ε) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hhighB :
      ¬2 * beliParameterDefect K (uniformizerPowerUnit K R * η) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  let D : ℕ∞ := quadraticDefect K (ε * η)
  let high : Nat := Int.toNat
    ((ramificationIndex K : Int) + R / 2)
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hbOrder : ordUnit K b = R :=
    ordUnit_uniformizerPower_mul_valuationUnit η hη R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have hbound := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at hbound
  have hnotOrderA : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rwa [haOrder, not_lt]
  have hnotOrderB : ¬2 * (ramificationIndex K : Int) < ordUnit K b := by
    rwa [hbOrder, not_lt]
  have hhighA' :
      ¬2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
    unfold beliDefectCutoff
    rwa [haOrder]
  have hhighB' :
      ¬2 * beliParameterDefect K b ≤
        (beliDefectCutoff K b : ℕ∞) := by
    unfold beliDefectCutoff
    rwa [hbOrder]
  have hgA : beliNormGeneratorSquareClassGroup K a =
      principalUnitSquareClassSubgroup K high := by
    rw [beliNormGeneratorSquareClassGroup_of_high_defect
      K a hnotOrderA hhighA']
    unfold beliHighDefectExponent
    rw [haOrder]
  have hgB : beliNormGeneratorSquareClassGroup K b =
      principalUnitSquareClassSubgroup K high := by
    rw [beliNormGeneratorSquareClassGroup_of_high_defect
      K b hnotOrderB hhighB']
    unfold beliHighDefectExponent
    rw [hbOrder]
  by_cases hDtop : D = ⊤
  · rw [hgA, hgB, sup_idem]
    simp [D, hDtop]
  · let dD : Nat := D.toNat
    let kD : Nat := Int.toNat (R + (dD : Int))
    have hproductDefect : quadraticDefect K ((-b) * (-a)) = D := by
      dsimp [D]
      exact quadraticDefect_negative_uniformizerParameters_mul
        (K := K) R ε η
    have hdom : min (beliParameterDefect K a)
          (beliParameterDefect K b) ≤ D := by
      unfold beliParameterDefect
      rw [← hproductDefect]
      simpa [min_comm] using quadraticDefect_mul_ge_min K (-b) (-a)
    have hcutD :
        (Int.toNat
            (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
          2 * D := by
      rcases le_total (beliParameterDefect K a)
          (beliParameterDefect K b) with hAB | hBA
      · have hAD : beliParameterDefect K a ≤ D := by
          simpa [min_eq_left hAB] using hdom
        have htwice : 2 * beliParameterDefect K a ≤ 2 * D := by
          gcongr
        exact (lt_of_not_ge hhighA).trans_le
          htwice
      · have hBD : beliParameterDefect K b ≤ D := by
          simpa [min_eq_right hBA] using hdom
        have htwice : 2 * beliParameterDefect K b ≤ 2 * D := by
          gcongr
        exact (lt_of_not_ge hhighB).trans_le
          htwice
    have hcutDNat := hcutD
    rw [← ENat.coe_toNat hDtop] at hcutDNat
    norm_cast at hcutDNat
    have hk : high ≤ kD := by
      dsimp [high, kD, dD] at hcutDNat ⊢
      omega
    rw [hgA, hgB, sup_idem]
    rw [beliLemma314CongruenceFactor_of_ne_top
      (K := K) R D hDtop]
    change principalUnitSquareClassSubgroup K high =
      principalUnitSquareClassSubgroup K kD ⊔
        principalUnitSquareClassSubgroup K high
    exact (sup_eq_right.mpr
      (principalUnitSquareClassSubgroup_anti K hk)).symm

/-- Case (3) of Beli's proof: equal low defects.  Lemma 1.3(ii) shows that
the two restricted norm kernels coincide exactly when the product-defect
congruence factor is already contained in the first norm kernel. -/
theorem beliNormGeneratorSquareClassGroup_sup_equal_low
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hdefectEq :
      beliParameterDefect K (uniformizerPowerUnit K R * ε) =
        beliParameterDefect K (uniformizerPowerUnit K R * η))
    (hlow :
      2 * beliParameterDefect K (uniformizerPowerUnit K R * ε) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  let A : ℕ∞ := beliParameterDefect K a
  let D : ℕ∞ := quadraticDefect K (ε * η)
  let dA : Nat := A.toNat
  let kA : Nat := Int.toNat (R + (dA : Int))
  let H : Subgroup (SquareClass K) :=
    principalUnitSquareClassSubgroup K kA
  let F : Subgroup (SquareClass K) :=
    beliLemma314CongruenceFactor (K := K) R D
  have hdefectEqAB : beliParameterDefect K a =
      beliParameterDefect K b := by
    simpa [a, b] using hdefectEq
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hbOrder : ordUnit K b = R :=
    ordUnit_uniformizerPower_mul_valuationUnit η hη R
  have hnotOrderA : ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rwa [haOrder, not_lt]
  have hnotOrderB : ¬2 * (ramificationIndex K : Int) < ordUnit K b := by
    rwa [hbOrder, not_lt]
  have hfiniteA : A ≠ ⊤ := by
    intro htop
    have h := hlow
    change 2 * A ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞) at h
    rw [htop] at h
    simp at h
  have hnonnegA : 0 ≤ R + (dA : Int) := by
    dsimp [dA, A]
    rw [← haOrder]
    exact ha.order_add_parameterDefect_nonneg hfiniteA
  have hlowA :
      2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
    unfold beliDefectCutoff
    rwa [haOrder]
  have hlowB :
      2 * beliParameterDefect K b ≤
        (beliDefectCutoff K b : ℕ∞) := by
    rw [← hdefectEqAB]
    unfold beliDefectCutoff
    rwa [hbOrder]
  have hlowExponentA : beliLowDefectExponent K a = kA := by
    unfold beliLowDefectExponent beliParameterDefectNat
    rw [haOrder]
  have hlowExponentB : beliLowDefectExponent K b = kA := by
    unfold beliLowDefectExponent beliParameterDefectNat
    rw [hbOrder, ← hdefectEqAB]
  have hgA : beliNormGeneratorSquareClassGroup K a =
      H ⊓ quadraticNormSquareClassSubgroup K (-a) := by
    rw [beliNormGeneratorSquareClassGroup_of_low_defect
      K a hnotOrderA hlowA]
    rw [hlowExponentA]
  have hgB : beliNormGeneratorSquareClassGroup K b =
      H ⊓ quadraticNormSquareClassSubgroup K (-b) := by
    rw [beliNormGeneratorSquareClassGroup_of_low_defect
      K b hnotOrderB hlowB]
    rw [hlowExponentB]
  have hproductDefect : quadraticDefect K ((-a) * (-b)) = D := by
    dsimp [D]
    simpa [a, b, mul_comm, mul_left_comm, mul_assoc] using
      quadraticDefect_negative_uniformizerParameters_mul
        (K := K) R ε η
  have hAD : A ≤ D := by
    have hdom := quadraticDefect_mul_ge_min K (-a) (-b)
    rw [hproductDefect] at hdom
    change min A (beliParameterDefect K b) ≤ D at hdom
    rwa [← hdefectEqAB, min_self] at hdom
  have hlowNat := hlow
  change 2 * A ≤
    (Int.toNat
      (2 * (ramificationIndex K : Int) - R) : ℕ∞) at hlowNat
  rw [← ENat.coe_toNat hfiniteA] at hlowNat
  norm_cast at hlowNat
  by_cases hAendpoint :
      A = ((2 * ramificationIndex K : Nat) : ℕ∞)
  · have hdA : dA = 2 * ramificationIndex K := by
      dsimp [dA]
      rw [hAendpoint]
      simp
    have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
      have hbound := ha.ordUnit_ge_neg_two_mul_e
      rwa [haOrder] at hbound
    have hcutNonneg :
        0 ≤ 2 * (ramificationIndex K : Int) - R := by
      omega
    have hlowInt :
        (2 * A.toNat : Int) ≤
          2 * (ramificationIndex K : Int) - R := by
      have hlowInt' :
          (2 * A.toNat : Int) ≤
            (Int.toNat
              (2 * (ramificationIndex K : Int) - R) : Int) := by
        exact_mod_cast hlowNat
      rwa [Int.toNat_of_nonneg hcutNonneg] at hlowInt'
    have hRupperEndpoint :
        R ≤ -(2 * (ramificationIndex K : Int)) := by
      change (2 * (dA : Int)) ≤
        2 * (ramificationIndex K : Int) - R at hlowInt
      rw [hdA] at hlowInt
      omega
    have hkAZero : kA = 0 := by
      dsimp [kA]
      rw [hdA]
      apply Int.toNat_eq_zero.mpr
      omega
    have hendpointA :
        ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
          quadraticDefect K (-a) := by
      change ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ A
      rw [hAendpoint]
    have hendpointB :
        ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
          quadraticDefect K (-b) := by
      change ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        beliParameterDefect K b
      rw [← hdefectEqAB]
      change ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ A
      rw [hAendpoint]
    have hfiniteB : beliParameterDefect K b ≠ ⊤ := by
      rwa [← hdefectEqAB]
    have haNotSquare : ¬IsSquare (-a) := by
      intro hsquare
      apply hfiniteA
      change quadraticDefect K (-a) = ⊤
      exact (quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).2 hsquare
    have hbNotSquare : ¬IsSquare (-b) := by
      intro hsquare
      apply hfiniteB
      change quadraticDefect K (-b) = ⊤
      exact (quadraticDefect_eq_top_iff_isSquare (K := K) (-b)).2 hsquare
    let delta : Kˣ :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have haDisc : IsSquare ((-a) / delta) := by
      have hcases :=
        isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
          (-a) hendpointA
      simpa [delta] using hcases.resolve_left haNotSquare
    have hbDisc : IsSquare ((-b) / delta) := by
      have hcases :=
        isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
          (-b) hendpointB
      simpa [delta] using hcases.resolve_left hbNotSquare
    have hdeltaSquare : IsSquare (delta ^ 2) :=
      ⟨delta, by simp [pow_two]⟩
    have hproductSquare : IsSquare ((-a) * (-b)) := by
      have hquotientSquare := haDisc.mul hbDisc
      have heq :
          (-a) * (-b) = (((-a) / delta) * ((-b) / delta)) * delta ^ 2 := by
        symm
        simp only [div_eq_mul_inv, pow_two]
        calc
          ((-a) * delta⁻¹ * ((-b) * delta⁻¹)) * (delta * delta) =
              ((-a) * (-b)) *
                ((delta⁻¹ * delta) * (delta⁻¹ * delta)) := by
            ac_rfl
          _ = (-a) * (-b) := by simp
      rw [heq]
      exact hquotientSquare.mul hdeltaSquare
    have hDtop : D = ⊤ := by
      rw [← hproductDefect]
      exact (quadraticDefect_eq_top_iff_isSquare
        (K := K) ((-a) * (-b))).2
        hproductSquare
    have hHNormA : H ≤ quadraticNormSquareClassSubgroup K (-a) := by
      dsimp [H]
      rw [hkAZero,
        principalUnitSquareClassSubgroup_zero_le_quadraticNorm_iff]
      exact hendpointA
    have hHNormB : H ≤ quadraticNormSquareClassSubgroup K (-b) := by
      dsimp [H]
      rw [hkAZero,
        principalUnitSquareClassSubgroup_zero_le_quadraticNorm_iff]
      exact hendpointB
    have hgAEndpoint : beliNormGeneratorSquareClassGroup K a = H :=
      hgA.trans (inf_eq_left.mpr hHNormA)
    have hgBEndpoint : beliNormGeneratorSquareClassGroup K b = H :=
      hgB.trans (inf_eq_left.mpr hHNormB)
    have hFEndpoint : F = ⊥ := by
      simp [F, hDtop]
    change beliNormGeneratorSquareClassGroup K a ⊔
      beliNormGeneratorSquareClassGroup K b =
        F ⊔ beliNormGeneratorSquareClassGroup K a
    rw [hgAEndpoint, hgBEndpoint, hFEndpoint]
    simp
  have haNotSquare : ¬IsSquare (-a) := by
    intro hsquare
    apply hfiniteA
    change quadraticDefect K (-a) = ⊤
    exact (quadraticDefect_eq_top_iff_isSquare (K := K) (-a)).2 hsquare
  have hAle : A ≤ ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    change quadraticDefect K (-a) ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)
    exact quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) haNotSquare
  have hAlt : A < ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    lt_of_le_of_ne hAle hAendpoint
  have hkApos : 0 < kA := by
    have hpos := ha.lowDefectExponent_pos_of_lt_twoE (by
      simpa [A] using hAlt)
    change 0 < Int.toNat (R + (dA : Int))
    rw [← haOrder]
    change 0 < Int.toNat
      (ordUnit K a + ((beliParameterDefect K a).toNat : Int))
    exact hpos
  have hnotHNormA :
      ¬H ≤ quadraticNormSquareClassSubgroup K (-a) := by
    dsimp [H]
    rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
      K (-a) kA hkApos]
    change ¬((2 * ramificationIndex K : Nat) : ℕ∞) < A + kA
    rw [← ENat.coe_toNat hfiniteA]
    norm_cast
    dsimp [kA, dA] at hnonnegA ⊢
    omega
  have hfactorLeH : F ≤ H := by
    by_cases hDtop : D = ⊤
    · simp [F, hDtop]
    · let dD : Nat := D.toNat
      let kD : Nat := Int.toNat (R + (dD : Int))
      have hnat : dA ≤ dD := by
        have h := hAD
        rw [← ENat.coe_toNat hfiniteA,
          ← ENat.coe_toNat hDtop] at h
        exact_mod_cast h
      have hk : kA ≤ kD := by
        dsimp [kA, kD]
        omega
      rw [show F = principalUnitSquareClassSubgroup K kD by
        dsimp [F, kD]
        rw [beliLemma314CongruenceFactor_of_ne_top
          (K := K) R D hDtop]]
      exact principalUnitSquareClassSubgroup_anti K hk
  have hcriterion :
      H ≤ quadraticNormSquareClassSubgroup K ((-a) * (-b)) ↔
        F ≤ quadraticNormSquareClassSubgroup K (-a) := by
    by_cases hDtop : D = ⊤
    · have hleft :
          H ≤ quadraticNormSquareClassSubgroup K ((-a) * (-b)) := by
        dsimp [H]
        rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
            K ((-a) * (-b)) kA hkApos,
          hproductDefect, hDtop]
        exact ENat.coe_lt_top _
      have hright : F ≤ quadraticNormSquareClassSubgroup K (-a) := by
        simp [F, hDtop]
      exact ⟨fun _ => hright, fun _ => hleft⟩
    · let dD : Nat := D.toNat
      let kD : Nat := Int.toNat (R + (dD : Int))
      have hnat : dA ≤ dD := by
        have h := hAD
        rw [← ENat.coe_toNat hfiniteA,
          ← ENat.coe_toNat hDtop] at h
        exact_mod_cast h
      have hnonnegD : 0 ≤ R + (dD : Int) := by
        omega
      have hkDpos : 0 < kD := by
        dsimp [kA, kD]
        omega
      have hsum : D + (kA : ℕ∞) = A + (kD : ℕ∞) := by
        rw [← ENat.coe_toNat hDtop,
          ← ENat.coe_toNat hfiniteA]
        norm_cast
        dsimp [kA, kD, dA, dD] at hnonnegA hnonnegD ⊢
        omega
      dsimp [H, F]
      rw [beliLemma314CongruenceFactor_of_ne_top
        (K := K) R D hDtop]
      change
        principalUnitSquareClassSubgroup K kA ≤
            quadraticNormSquareClassSubgroup K ((-a) * (-b)) ↔
          principalUnitSquareClassSubgroup K kD ≤
            quadraticNormSquareClassSubgroup K (-a)
      rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K ((-a) * (-b)) kA hkApos,
        principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K (-a) kD hkDpos,
        hproductDefect]
      change ((2 * ramificationIndex K : Nat) : ℕ∞) < D + kA ↔
        ((2 * ramificationIndex K : Nat) : ℕ∞) < A + kD
      rw [hsum]
  by_cases hnorm :
      H ≤ quadraticNormSquareClassSubgroup K ((-a) * (-b))
  · have hgroupsEq : beliNormGeneratorSquareClassGroup K a =
        beliNormGeneratorSquareClassGroup K b := by
      rw [hgA, hgB]
      exact (quadraticNorm_inf_eq_quadraticNorm_inf_iff
        K (-a) (-b) H).2 hnorm
    have hfactorLegA : F ≤ beliNormGeneratorSquareClassGroup K a := by
      rw [hgA]
      exact le_inf hfactorLeH (hcriterion.1 hnorm)
    calc
      beliNormGeneratorSquareClassGroup K a ⊔
            beliNormGeneratorSquareClassGroup K b =
          beliNormGeneratorSquareClassGroup K a ⊔
            beliNormGeneratorSquareClassGroup K a := by
              rw [← hgroupsEq]
      _ = beliNormGeneratorSquareClassGroup K a := sup_idem _
      _ = F ⊔ beliNormGeneratorSquareClassGroup K a :=
        (sup_eq_right.mpr hfactorLegA).symm
  · have hnotgB :
        ¬beliNormGeneratorSquareClassGroup K b ≤
          quadraticNormSquareClassSubgroup K (-a) := by
      intro hcontra
      have hinclusion :
          quadraticNormSquareClassSubgroup K (-b) ⊓ H ≤
            quadraticNormSquareClassSubgroup K (-a) := by
        simpa [hgB, inf_comm] using hcontra
      rcases
          (quadraticNorm_inf_le_quadraticNorm_iff
            K (-b) (-a) H).1 hinclusion with hfirst | hsecond
      · exact hnotHNormA hfirst
      · apply hnorm
        simpa [mul_comm] using hsecond
    have hnotgBKer :
        ¬beliNormGeneratorSquareClassGroup K b ≤
          (squareClassHilbertCharacter K (-a)).ker := by
      rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
      exact hnotgB
    have hleft :
        beliNormGeneratorSquareClassGroup K a ⊔
            beliNormGeneratorSquareClassGroup K b = H := by
      rw [hgA, quadraticNormSquareClassSubgroup_eq_ker]
      exact inf_ker_sup_eq_of_le_of_not_le
        (squareClassHilbertCharacter K (-a)) H
          (beliNormGeneratorSquareClassGroup K b)
          (by rw [hgB]; exact inf_le_left) hnotgBKer
    have hnotF :
        ¬F ≤ quadraticNormSquareClassSubgroup K (-a) := by
      exact fun hF => hnorm (hcriterion.2 hF)
    have hnotFKer :
        ¬F ≤ (squareClassHilbertCharacter K (-a)).ker := by
      rw [← quadraticNormSquareClassSubgroup_eq_ker K (-a)]
      exact hnotF
    have hright : F ⊔ beliNormGeneratorSquareClassGroup K a = H := by
      rw [hgA, quadraticNormSquareClassSubgroup_eq_ker, sup_comm]
      exact inf_ker_sup_eq_of_le_of_not_le
        (squareClassHilbertCharacter K (-a)) H F
          hfactorLeH hnotFKer
    exact hleft.trans hright.symm

/-- Beli (2003), Lemma 3.14.  For two admissible parameters of common order
`R ≤ 2e`, the second norm-generator group enlarges the first exactly by the
principal-unit factor at depth `R + d(εη)`. -/
theorem beliNormGeneratorSquareClassGroup_sup
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int)) :
    beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliNormGeneratorSquareClassGroup K
          (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  let gA : Subgroup (SquareClass K) :=
    beliNormGeneratorSquareClassGroup K a
  let gB : Subgroup (SquareClass K) :=
    beliNormGeneratorSquareClassGroup K b
  let D : ℕ∞ := quadraticDefect K (ε * η)
  let F : Subgroup (SquareClass K) :=
    beliLemma314CongruenceFactor (K := K) R D
  let cutoff : ℕ∞ :=
    (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞)
  change gA ⊔ gB = F ⊔ gA
  by_cases hlowA : 2 * beliParameterDefect K a ≤ cutoff
  · by_cases heq : beliParameterDefect K a = beliParameterDefect K b
    · simpa [a, b, gA, gB, D, F, cutoff] using
        beliNormGeneratorSquareClassGroup_sup_equal_low
          (K := K) R ε η hε hη ha hRupper
            (by simpa [a, b] using heq)
            (by simpa [a, cutoff] using hlowA)
    · rcases lt_or_gt_of_ne heq with hAB | hBA
      · have hspan : gA ⊔ gB =
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K a).toNat : Int))) := by
          simpa [a, b, gA, gB, cutoff] using
            beliNormGeneratorSquareClassGroup_sup_eq_principal_of_defect_lt
              (K := K) R ε η hε hη ha hb hRupper
                (by simpa [a, b] using hAB)
                (by simpa [a, cutoff] using hlowA)
        have hD : D = beliParameterDefect K a := by
          dsimp [D]
          exact quadraticDefect_unitProduct_eq_parameterDefect_of_lt
            (K := K) R ε η (by simpa [a, b] using hAB)
        have hfinite : beliParameterDefect K a ≠ ⊤ :=
          ne_top_of_lt hAB
        have hfactor : F =
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K a).toNat : Int))) := by
          dsimp [F]
          rw [hD, beliLemma314CongruenceFactor_of_ne_top
            (K := K) R (beliParameterDefect K a) hfinite]
        have hgAle : gA ≤
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K a).toNat : Int))) := by
          rw [← hspan]
          exact le_sup_left
        rw [hfactor]
        exact hspan.trans (sup_eq_left.mpr hgAle).symm
      · have hlowB : 2 * beliParameterDefect K b ≤ cutoff := by
          have htwice : 2 * beliParameterDefect K b ≤
              2 * beliParameterDefect K a := by
            gcongr
          exact htwice.trans hlowA
        have hspan : gA ⊔ gB =
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K b).toNat : Int))) := by
          simpa [a, b, gA, gB, cutoff, sup_comm] using
            beliNormGeneratorSquareClassGroup_sup_eq_principal_of_defect_lt
              (K := K) R η ε hη hε hb ha hRupper
                (by simpa [a, b] using hBA)
                (by simpa [b, cutoff] using hlowB)
        have hD : D = beliParameterDefect K b := by
          dsimp [D]
          simpa [b, mul_comm] using
            quadraticDefect_unitProduct_eq_parameterDefect_of_lt
              (K := K) R η ε (by simpa [a, b] using hBA)
        have hfinite : beliParameterDefect K b ≠ ⊤ :=
          ne_top_of_lt hBA
        have hfactor : F =
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K b).toNat : Int))) := by
          dsimp [F]
          rw [hD, beliLemma314CongruenceFactor_of_ne_top
            (K := K) R (beliParameterDefect K b) hfinite]
        have hgAle : gA ≤
            principalUnitSquareClassSubgroup K
              (Int.toNat
                (R + ((beliParameterDefect K b).toNat : Int))) := by
          rw [← hspan]
          exact le_sup_left
        rw [hfactor]
        exact hspan.trans (sup_eq_left.mpr hgAle).symm
  · by_cases hlowB : 2 * beliParameterDefect K b ≤ cutoff
    · have hBA : beliParameterDefect K b <
          beliParameterDefect K a := by
        apply lt_of_not_ge
        intro hAB
        apply hlowA
        have htwice : 2 * beliParameterDefect K a ≤
            2 * beliParameterDefect K b := by
          gcongr
        exact htwice.trans hlowB
      have hspan : gA ⊔ gB =
          principalUnitSquareClassSubgroup K
            (Int.toNat
              (R + ((beliParameterDefect K b).toNat : Int))) := by
        simpa [a, b, gA, gB, cutoff, sup_comm] using
          beliNormGeneratorSquareClassGroup_sup_eq_principal_of_defect_lt
            (K := K) R η ε hη hε hb ha hRupper
              (by simpa [a, b] using hBA)
              (by simpa [b, cutoff] using hlowB)
      have hD : D = beliParameterDefect K b := by
        dsimp [D]
        simpa [b, mul_comm] using
          quadraticDefect_unitProduct_eq_parameterDefect_of_lt
            (K := K) R η ε (by simpa [a, b] using hBA)
      have hfinite : beliParameterDefect K b ≠ ⊤ :=
        ne_top_of_lt hBA
      have hfactor : F =
          principalUnitSquareClassSubgroup K
            (Int.toNat
              (R + ((beliParameterDefect K b).toNat : Int))) := by
        dsimp [F]
        rw [hD, beliLemma314CongruenceFactor_of_ne_top
          (K := K) R (beliParameterDefect K b) hfinite]
      have hgAle : gA ≤
          principalUnitSquareClassSubgroup K
            (Int.toNat
              (R + ((beliParameterDefect K b).toNat : Int))) := by
        rw [← hspan]
        exact le_sup_left
      rw [hfactor]
      exact hspan.trans (sup_eq_left.mpr hgAle).symm
    · simpa [a, b, gA, gB, D, F, cutoff] using
        beliNormGeneratorSquareClassGroup_sup_high_high
          (K := K) R ε η hε hη ha hRupper
            (by simpa [a, cutoff] using hlowA)
            (by simpa [b, cutoff] using hlowB)

end Dyadic

end Bong
