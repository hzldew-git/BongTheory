/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma314

/-!
# Beli 2003, Corollary 3.15

This file transports Lemma 3.14 through the comparison formulas of Lemma
3.13.  The first part treats the range `2e < R ≤ 4e`.
-/

namespace Bong.Dyadic

universe u v

/-- In a commutative group, replacing two generators `x,y` by `xy,x` does
not change the subgroup they generate. -/
theorem zpowers_sup_zpowers_eq_mul_sup
    {G : Type v} [CommGroup G] (x y : G) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y =
      Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x := by
  apply le_antisymm
  · apply sup_le
    · rw [Subgroup.zpowers_le]
      exact (le_sup_right : Subgroup.zpowers x ≤
        Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x)
        (Subgroup.mem_zpowers x)
    · rw [Subgroup.zpowers_le]
      have hx : x ∈ Subgroup.zpowers (x * y) ⊔
          Subgroup.zpowers x :=
        (le_sup_right : Subgroup.zpowers x ≤
          Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x)
          (Subgroup.mem_zpowers x)
      have hxy : x * y ∈ Subgroup.zpowers (x * y) ⊔
          Subgroup.zpowers x :=
        (le_sup_left : Subgroup.zpowers (x * y) ≤
          Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x)
          (Subgroup.mem_zpowers (x * y))
      have h :=
        (Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x).mul_mem
          ((Subgroup.zpowers (x * y) ⊔
            Subgroup.zpowers x).inv_mem hx) hxy
      simpa using h
  · apply sup_le
    · rw [Subgroup.zpowers_le]
      exact (Subgroup.zpowers x ⊔ Subgroup.zpowers y).mul_mem
        ((le_sup_left : Subgroup.zpowers x ≤
          Subgroup.zpowers x ⊔ Subgroup.zpowers y)
          (Subgroup.mem_zpowers x))
        ((le_sup_right : Subgroup.zpowers y ≤
          Subgroup.zpowers x ⊔ Subgroup.zpowers y)
          (Subgroup.mem_zpowers y))
    · exact le_sup_left

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The congruence factor printed in Corollary 3.15(ii), with depth
`R / 2 + d - e`.  Infinite defect again means the trivial square-class
factor. -/
noncomputable def beliCorollary315EvenCongruenceFactor
    (R : Int) (d : ℕ∞) : Subgroup (SquareClass K) :=
  if d = ⊤ then ⊥ else
    principalUnitSquareClassSubgroup K
      (Int.toNat
        (R / 2 + (d.toNat : Int) - (ramificationIndex K : Int)))

@[simp]
theorem beliCorollary315EvenCongruenceFactor_top (R : Int) :
    beliCorollary315EvenCongruenceFactor (K := K) R ⊤ = ⊥ := by
  simp [beliCorollary315EvenCongruenceFactor]

theorem beliCorollary315EvenCongruenceFactor_of_ne_top
    (R : Int) (d : ℕ∞) (hd : d ≠ ⊤) :
    beliCorollary315EvenCongruenceFactor (K := K) R d =
      principalUnitSquareClassSubgroup K
        (Int.toNat
          (R / 2 + (d.toNat : Int) -
            (ramificationIndex K : Int))) := by
  simp [beliCorollary315EvenCongruenceFactor, hd]

@[simp]
theorem squareClass_mul_eq (a b : Kˣ) :
    squareClass K (a * b) = squareClass K a * squareClass K b :=
  rfl

/-- Cyclic square-class subgroups satisfy the same change of generators. -/
theorem cyclicSquareClassSubgroup_sup_eq_mul_sup (a b : Kˣ) :
    cyclicSquareClassSubgroup K a ⊔ cyclicSquareClassSubgroup K b =
      cyclicSquareClassSubgroup K (a * b) ⊔
        cyclicSquareClassSubgroup K a := by
  unfold cyclicSquareClassSubgroup
  simpa only [squareClass_mul_eq] using
    zpowers_sup_zpowers_eq_mul_sup
      (squareClass K a) (squareClass K b)

/-- For equal-order uniformizer parameters, the product cyclic class is the
unit-product class because the common uniformizer factor occurs as a square. -/
theorem cyclicSquareClassSubgroup_uniformizerParameters_sup
    (R : Int) (ε η : Kˣ) :
    cyclicSquareClassSubgroup K (uniformizerPowerUnit K R * ε) ⊔
        cyclicSquareClassSubgroup K (uniformizerPowerUnit K R * η) =
      cyclicSquareClassSubgroup K (ε * η) ⊔
        cyclicSquareClassSubgroup K
          (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  have hproduct : a * b =
      (ε * η) * uniformizerPowerUnit K R ^ 2 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    dsimp [a, b]
    ring
  have hclass : squareClass K (a * b) = squareClass K (ε * η) := by
    rw [hproduct, squareClass_mul_square]
  have hcyclic : cyclicSquareClassSubgroup K (a * b) =
      cyclicSquareClassSubgroup K (ε * η) := by
    unfold cyclicSquareClassSubgroup
    rw [hclass]
  calc
    cyclicSquareClassSubgroup K a ⊔
          cyclicSquareClassSubgroup K b =
        cyclicSquareClassSubgroup K (a * b) ⊔
          cyclicSquareClassSubgroup K a :=
      cyclicSquareClassSubgroup_sup_eq_mul_sup (K := K) a b
    _ = cyclicSquareClassSubgroup K (ε * η) ⊔
        cyclicSquareClassSubgroup K a := by rw [hcyclic]

/-- A parameter of order greater than `2e` cannot be in the exceptional
class `-1/4`, whose order is `-2e`. -/
theorem unitSquareClass_ne_negativeQuarter_of_two_e_lt
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    unitSquareClass K a ≠ unitSquareClass K (negativeQuarterUnit K) := by
  intro hclass
  have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  rw [ordUnit_negativeQuarterUnit] at horder
  have he : 0 ≤ (ramificationIndex K : Int) := by positivity
  omega

/-- Corollary 3.15(i), auxiliary-group identity. -/
theorem beliAuxiliarySpinorGroup_sup
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (hRlow : 2 * (ramificationIndex K : Int) < R)
    (hRhigh : R ≤ 4 * (ramificationIndex K : Int)) :
    beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * ε)
          (by
            rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
            exact hRlow) ⊔
        beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * η)
          (by
            rw [ordUnit_uniformizerPower_mul_valuationUnit η hη R]
            exact hRlow) =
      beliLemma314CongruenceFactor (K := K)
          (R - 2 * (ramificationIndex K : Int))
          (quadraticDefect K (ε * η)) ⊔
        beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * ε)
          (by
            rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
            exact hRlow) := by
  let T : Int := R - 2 * (ramificationIndex K : Int)
  let shiftedε : Kˣ := uniformizerPowerUnit K T * ε
  let shiftedη : Kˣ := uniformizerPowerUnit K T * η
  have hTpos : 0 < T := by
    dsimp [T]
    omega
  have hTupper : T ≤ 2 * (ramificationIndex K : Int) := by
    dsimp [T]
    omega
  have hshiftedε : BONG.IsBinaryParameterAdmissible shiftedε := by
    apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε T]
    exact hTpos.le
  have hshiftedη : BONG.IsBinaryParameterAdmissible shiftedη := by
    apply BONG.isBinaryParameterAdmissible_of_ordUnit_nonneg
    rw [ordUnit_uniformizerPower_mul_valuationUnit η hη T]
    exact hTpos.le
  have hlemma314 := beliNormGeneratorSquareClassGroup_sup
    (K := K) T ε η hε hη hshiftedε hshiftedη hTupper
  have hεshift :=
    beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
      (K := K) R ε hε hRlow
  have hηshift :=
    beliAuxiliarySpinorGroup_eq_shiftedNormGeneratorGroup
      (K := K) R η hη hRlow
  change
    beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * ε) _ ⊔
        beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * η) _ =
      beliLemma314CongruenceFactor (K := K) T
          (quadraticDefect K (ε * η)) ⊔
        beliAuxiliarySpinorGroup K
          (uniformizerPowerUnit K R * ε) _
  rw [hεshift, hηshift]
  simpa [T, shiftedε, shiftedη] using hlemma314

/-- Corollary 3.15(i), full spinor-group identity. -/
theorem beliSpinorGroupRepresentative_sup_of_two_e_lt
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRlow : 2 * (ramificationIndex K : Int) < R)
    (hRhigh : R ≤ 4 * (ramificationIndex K : Int)) :
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      cyclicSquareClassSubgroup K (ε * η) ⊔
        beliLemma314CongruenceFactor (K := K)
          (R - 2 * (ramificationIndex K : Int))
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let b : Kˣ := uniformizerPowerUnit K R * η
  let CA : Subgroup (SquareClass K) := cyclicSquareClassSubgroup K a
  let CB : Subgroup (SquareClass K) := cyclicSquareClassSubgroup K b
  let C : Subgroup (SquareClass K) := cyclicSquareClassSubgroup K (ε * η)
  let GA : Subgroup (SquareClass K) := beliSpinorGroupRepresentative K a
  let GB : Subgroup (SquareClass K) := beliSpinorGroupRepresentative K b
  let AA : Subgroup (SquareClass K) :=
    beliAuxiliarySpinorGroup K a (by
      rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
      exact hRlow)
  let AB : Subgroup (SquareClass K) :=
    beliAuxiliarySpinorGroup K b (by
      rw [ordUnit_uniformizerPower_mul_valuationUnit η hη R]
      exact hRlow)
  let F : Subgroup (SquareClass K) :=
    beliLemma314CongruenceFactor (K := K)
      (R - 2 * (ramificationIndex K : Int))
      (quadraticDefect K (ε * η))
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hbOrder : ordUnit K b = R :=
    ordUnit_uniformizerPower_mul_valuationUnit η hη R
  have hRrepA : 2 * (ramificationIndex K : Int) < ordUnit K a := by
    rwa [haOrder]
  have hRrepB : 2 * (ramificationIndex K : Int) < ordUnit K b := by
    rwa [hbOrder]
  have hquarterA :=
    unitSquareClass_ne_negativeQuarter_of_two_e_lt (K := K) a hRrepA
  have hquarterB :=
    unitSquareClass_ne_negativeQuarter_of_two_e_lt (K := K) b hRrepB
  have hGA : GA = CA ⊔ AA := by
    dsimp [GA, CA, AA]
    exact beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
      K a ha hquarterA hRrepA
  have hGB : GB = CB ⊔ AB := by
    dsimp [GB, CB, AB]
    exact beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
      K b hb hquarterB hRrepB
  have haux : AA ⊔ AB = F ⊔ AA := by
    dsimp [AA, AB, F]
    exact beliAuxiliarySpinorGroup_sup
      (K := K) R ε η hε hη hRlow hRhigh
  have hcyclic : CA ⊔ CB = C ⊔ CA := by
    simpa [a, b, CA, CB, C] using
      cyclicSquareClassSubgroup_uniformizerParameters_sup
        (K := K) R ε η
  change GA ⊔ GB = C ⊔ F ⊔ GA
  calc
    GA ⊔ GB = (CA ⊔ AA) ⊔ (CB ⊔ AB) := by rw [hGA, hGB]
    _ = (CA ⊔ CB) ⊔ (AA ⊔ AB) := by ac_rfl
    _ = (C ⊔ CA) ⊔ (F ⊔ AA) := by rw [hcyclic, haux]
    _ = C ⊔ F ⊔ (CA ⊔ AA) := by ac_rfl
    _ = C ⊔ F ⊔ GA := by rw [hGA]

/-- The shifted parameter used in Lemma 3.13(ii) is again admissible.  This
is the membership check needed before applying Lemma 3.14. -/
theorem beliLemma313EvenShift_isBinaryParameterAdmissible
    [QuadraticDefectLaws K]
    (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K
        (beliLemma313EvenShift (K := K) R) * ε) := by
  let q : Int := (2 * (ramificationIndex K : Int) - R) / 4
  let T : Int := beliLemma313EvenShift (K := K) R
  let shifted : Kˣ := uniformizerPowerUnit K T * ε
  have haOrder : ordUnit K (uniformizerPowerUnit K R * ε) = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have h := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at h
  have hn0 : 0 ≤ 2 * (ramificationIndex K : Int) - R := by
    omega
  have hq0 : 0 ≤ q := by
    exact Int.ediv_nonneg hn0 (by omega)
  have hqle : q ≤ (ramificationIndex K : Int) := by
    rw [← Int.lt_add_one_iff]
    apply (Int.ediv_lt_iff_lt_mul (by omega)).2
    omega
  have hT : T = -2 * q := by rfl
  have hEvenT : Even T := by
    refine ⟨-q, ?_⟩
    omega
  have hshiftedOrder : ordUnit K shifted = T :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε T
  have hnegativeOrder : ordUnit K (-shifted) = T := by
    calc
      ordUnit K (-shifted) = ordUnit K shifted := by
        apply WithTop.coe_injective
        simpa using ord_neg K (shifted : K)
      _ = T := hshiftedOrder
  have hdefect : beliParameterDefect K shifted =
      quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) T ε hε hEvenT
  apply
    (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      shifted).2
  constructor
  · rw [hshiftedOrder, hT]
    omega
  · rw [hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le]
    change (absoluteDefectThreshold (-shifted) : ℕ∞) ≤
      beliParameterDefect K shifted
    rw [hdefect]
    by_cases htop : quadraticDefect K (-ε) = ⊤
    · rw [htop]
      exact le_top
    · have hdNat := hdLower
      rw [← ENat.coe_toNat htop] at hdNat
      norm_cast at hdNat
      rw [← ENat.coe_toNat htop]
      norm_cast
      unfold absoluteDefectThreshold
      rw [hnegativeOrder, hT]
      have hdivision :=
        Int.ediv_mul_le (2 * (ramificationIndex K : Int) - R)
          (by norm_num : (4 : Int) ≠ 0)
      omega

/-- In the range of Corollary 3.15(ii), the principal layer of depth
`R / 2 + e` is already contained in `G(πᴿε)`.  This is the representative
form of the use of paragraph 3.16 in the exceptional parity case. -/
theorem principalUnitSquareClassSubgroup_halfOrder_add_e_le_spinor
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    (R : Int) (ε : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdLower : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    principalUnitSquareClassSubgroup K
        (Int.toNat
          (R / 2 + (ramificationIndex K : Int))) ≤
      beliSpinorGroupRepresentative K
        (uniformizerPowerUnit K R * ε) := by
  rcases hEven with ⟨r, hr⟩
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let k : Nat := Int.toNat
    (R / 2 + (ramificationIndex K : Int))
  have hEvenR : Even R := ⟨r, hr⟩
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have h := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at h
  have hdefectA : beliParameterDefect K a =
      quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε hEvenR
  have hRrep : ordUnit K a ≤ 2 * (ramificationIndex K : Int) := by
    rwa [haOrder]
  have hdLowRep : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [haOrder, hdefectA]
    exact hdLower
  by_cases hquarter : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)
  · rw [beliSpinorGroupRepresentative_of_negativeQuarter K a ha hquarter]
    exact principalUnitSquareClassSubgroup_le_valuationUnit K k
  · by_cases hdUpper : 4 * beliParameterDefect K a ≤
        (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)
    · rw [beliSpinorGroupRepresentative_caseIII_middle K a ha
        hquarter hRrep hdLowRep hdUpper]
      have hfinite : quadraticDefect K (-ε) ≠ ⊤ := by
        intro htop
        have := hdUpper
        rw [hdefectA, htop] at this
        simpa using this
      have hnotSquare : ¬IsSquare (-ε) := by
        intro hsquare
        exact hfinite
          ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).2 hsquare)
      have hbound :=
        quadraticDefect_le_two_mul_e_of_not_isSquare
          (K := K) hnotSquare
      rw [← ENat.coe_toNat hfinite] at hbound
      norm_cast at hbound
      have hdNat := hdLower
      rw [← ENat.coe_toNat hfinite] at hdNat
      norm_cast at hdNat
      refine le_inf ?_ ?_
      · apply principalUnitSquareClassSubgroup_anti K
        unfold beliSpinorCaseIIIMiddleExponent beliParameterDefectNat
        rw [haOrder, hdefectA]
        apply Int.toNat_le_toNat
        omega
      · have hkpos : 0 < k := by
          dsimp [k]
          have hpositive :
              0 < R / 2 + (ramificationIndex K : Int) := by
            have hhalf : R / 2 = r := by omega
            by_contra hnotPos
            have hnonpos :
                R / 2 + (ramificationIndex K : Int) ≤ 0 :=
              le_of_not_gt hnotPos
            rw [hhalf] at hnonpos
            have hRendpoint :
                R = -(2 * (ramificationIndex K : Int)) := by
              omega
            apply hdNat
            rw [hRendpoint]
            norm_num
            omega
          have hcast :
              (0 : Int) <
                (Int.toNat
                  (R / 2 + (ramificationIndex K : Int)) : Int) := by
            rw [Int.toNat_of_nonneg hpositive.le]
            exact hpositive
          exact_mod_cast hcast
        rw [principalUnitSquareClassSubgroup_le_quadraticNorm_iff
          K (-a) k hkpos]
        change ((2 * ramificationIndex K : Nat) : ℕ∞) <
          beliParameterDefect K a + k
        rw [hdefectA, ← ENat.coe_toNat hfinite]
        norm_cast
        dsimp [k]
        omega
    · rw [beliSpinorGroupRepresentative_caseIII_high K a ha
        hquarter hRrep hdLowRep hdUpper]
      apply principalUnitSquareClassSubgroup_anti K
      unfold beliSpinorCaseIIIHighExponent
      rw [haOrder]
      apply Int.toNat_le_toNat
      have hdivisionUpper :
          2 * (ramificationIndex K : Int) - R <
            ((2 * (ramificationIndex K : Int) - R) / 4 + 1) * 4 := by
        apply (Int.ediv_lt_iff_lt_mul (by omega)).1
        omega
      omega

/-- Corollary 3.15(ii) in the exact shifted form delivered by Lemmas 3.13
and 3.14.  The following stage normalizes its congruence depth to the printed
`R/2 + d(εη) - e`. -/
theorem beliSpinorGroupRepresentative_sup_even_shift
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdε : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hdη : ¬2 * quadraticDefect K (-η) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K)
          (beliLemma313EvenShift (K := K) R)
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) := by
  let T : Int := beliLemma313EvenShift (K := K) R
  let shiftedε : Kˣ := uniformizerPowerUnit K T * ε
  let shiftedη : Kˣ := uniformizerPowerUnit K T * η
  have hTupper : T ≤ 2 * (ramificationIndex K : Int) := by
    have hn0 : 0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
    have hq0 : 0 ≤
        (2 * (ramificationIndex K : Int) - R) / 4 :=
      Int.ediv_nonneg hn0 (by omega)
    dsimp [T, beliLemma313EvenShift]
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  have hshiftedε : BONG.IsBinaryParameterAdmissible shiftedε := by
    dsimp [shiftedε, T]
    exact beliLemma313EvenShift_isBinaryParameterAdmissible
      (K := K) R ε hε ha hRupper hdε
  have hshiftedη : BONG.IsBinaryParameterAdmissible shiftedη := by
    dsimp [shiftedη, T]
    exact beliLemma313EvenShift_isBinaryParameterAdmissible
      (K := K) R η hη hb hRupper hdη
  have hlemma314 := beliNormGeneratorSquareClassGroup_sup
    (K := K) T ε η hε hη hshiftedε hshiftedη hTupper
  have hεshift :=
    beliSpinorGroupRepresentative_eq_evenShift_normGenerator
      (K := K) R ε hε ha hRupper hEven hdε
  have hηshift :=
    beliSpinorGroupRepresentative_eq_evenShift_normGenerator
      (K := K) R η hη hb hRupper hEven hdη
  change
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      beliLemma314CongruenceFactor (K := K) T
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε)
  rw [hεshift, hηshift]
  simpa [T, shiftedε, shiftedη] using hlemma314

/-- The shifted factor in Lemma 3.14 and the factor printed in Corollary
3.15(ii) give the same product after adjoining `G(πᴿε)`.  In the sole
exceptional parity case, the shallower factor is absorbed by `G(πᴿε)`. -/
theorem beliLemma314EvenShiftFactor_sup_spinor_eq_corollary315
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdε : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hdη : ¬2 * quadraticDefect K (-η) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliLemma314CongruenceFactor (K := K)
          (beliLemma313EvenShift (K := K) R)
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) =
      beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) := by
  rcases hEven with ⟨r, hr⟩
  let q : Int := (2 * (ramificationIndex K : Int) - R) / 4
  let x : Int := (ramificationIndex K : Int) - r
  let T : Int := beliLemma313EvenShift (K := K) R
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let D : ℕ∞ := quadraticDefect K (ε * η)
  let d : Nat := D.toNat
  have hEvenR : Even R := ⟨r, hr⟩
  have hRdiv : R / 2 = r := by omega
  have hx0 : 0 ≤ x := by
    dsimp [x]
    omega
  have hn0 : 0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
  have hq0 : 0 ≤ q := Int.ediv_nonneg hn0 (by omega)
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
  have hT : T = -2 * q := by rfl
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have h := ha.ordUnit_ge_neg_two_mul_e
    rwa [haOrder] at h
  have hdom : min (quadraticDefect K (-ε))
        (quadraticDefect K (-η)) ≤ D := by
    dsimp [D]
    simpa using quadraticDefect_mul_ge_min K (-ε) (-η)
  have hcutD :
      (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : ℕ∞) <
        2 * D := by
    rcases le_total (quadraticDefect K (-ε))
        (quadraticDefect K (-η)) with hεη | hηε
    · have hεD : quadraticDefect K (-ε) ≤ D := by
        simpa [min_eq_left hεη] using hdom
      have htwice : 2 * quadraticDefect K (-ε) ≤ 2 * D := by
        gcongr
      exact (lt_of_not_ge hdε).trans_le htwice
    · have hηD : quadraticDefect K (-η) ≤ D := by
        simpa [min_eq_right hηε] using hdom
      have htwice : 2 * quadraticDefect K (-η) ≤ 2 * D := by
        gcongr
      exact (lt_of_not_ge hdη).trans_le htwice
  change beliLemma314CongruenceFactor (K := K) T D ⊔
        beliSpinorGroupRepresentative K a =
      beliCorollary315EvenCongruenceFactor (K := K) R D ⊔
        beliSpinorGroupRepresentative K a
  by_cases hDtop : D = ⊤
  · rw [hDtop, beliLemma314CongruenceFactor_top,
      beliCorollary315EvenCongruenceFactor_top]
  · have hnotSquare : ¬IsSquare (ε * η) := by
      intro hsquare
      apply hDtop
      dsimp [D]
      exact
        (quadraticDefect_eq_top_iff_isSquare (K := K) (ε * η)).2
          hsquare
    have hDle : D ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      dsimp [D]
      exact quadraticDefect_le_two_mul_e_of_not_isSquare
        (K := K) hnotSquare
    have hDleNat := hDle
    rw [← ENat.coe_toNat hDtop] at hDleNat
    norm_cast at hDleNat
    have hcutNat := hcutD
    rw [← ENat.coe_toNat hDtop] at hcutNat
    norm_cast at hcutNat
    have hxlt : Int.toNat x < d := by
      dsimp [x, d]
      omega
    by_cases hxEven : x = 2 * q
    · have hexponent :
          Int.toNat (T + (D.toNat : Int)) =
            Int.toNat
              (R / 2 + (D.toNat : Int) -
                (ramificationIndex K : Int)) := by
        apply congrArg Int.toNat
        rw [hT, hRdiv]
        dsimp [x] at hxEven
        omega
      rw [beliLemma314CongruenceFactor_of_ne_top
          (K := K) T D hDtop,
        beliCorollary315EvenCongruenceFactor_of_ne_top
          (K := K) R D hDtop, hexponent]
    · have hxOdd : x = 2 * q + 1 := by omega
      by_cases hdMax : d = 2 * ramificationIndex K
      · have hDtoNat : D.toNat = 2 * ramificationIndex K := by
          simpa [d] using hdMax
        have htargetExponent :
            Int.toNat
                (R / 2 + (D.toNat : Int) -
                  (ramificationIndex K : Int)) =
              Int.toNat
                (R / 2 + (ramificationIndex K : Int)) := by
          apply congrArg Int.toNat
          rw [hDtoNat]
          push_cast
          ring
        have htargetLe :
            beliCorollary315EvenCongruenceFactor (K := K) R D ≤
              beliSpinorGroupRepresentative K a := by
          rw [beliCorollary315EvenCongruenceFactor_of_ne_top
            (K := K) R D hDtop, htargetExponent]
          exact
            principalUnitSquareClassSubgroup_halfOrder_add_e_le_spinor
              (K := K) R ε hε ha hRupper hEvenR hdε
        have hfactorLe :
            beliLemma314CongruenceFactor (K := K) T D ≤
              beliCorollary315EvenCongruenceFactor (K := K) R D := by
          rw [beliLemma314CongruenceFactor_of_ne_top
              (K := K) T D hDtop,
            beliCorollary315EvenCongruenceFactor_of_ne_top
              (K := K) R D hDtop]
          apply principalUnitSquareClassSubgroup_anti K
          apply Int.toNat_le_toNat
          rw [hT, hRdiv]
          dsimp [x] at hxOdd
          omega
        rw [sup_eq_right.mpr (hfactorLe.trans htargetLe),
          sup_eq_right.mpr htargetLe]
      · have hdLt : d < 2 * ramificationIndex K := by omega
        have hDlt : D <
            ((2 * ramificationIndex K : Nat) : ℕ∞) := by
          rw [← ENat.coe_toNat hDtop]
          norm_cast
        have hunitProduct :
            IsValuationUnit K (((ε * η : Kˣ) : K)) := by
          rw [IsValuationUnit, Units.val_mul, ord_mul, hε, hη]
          simp
        have hdOdd : Odd d := by
          dsimp [d, D]
          exact quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
            (K := K) (ε * η) hunitProduct hDlt
        let n : Nat := d - Int.toNat x
        have hxOddNat : Odd (Int.toNat x) := by
          refine ⟨Int.toNat q, ?_⟩
          omega
        have hnEven : Even n := by
          dsimp [n]
          exact Nat.Odd.sub_odd hdOdd hxOddNat
        have hnPos : 0 < n := by
          dsimp [n]
          omega
        have hnLt : n < 2 * ramificationIndex K := by
          dsimp [n]
          omega
        have hfiltration :=
          principalUnitSquareClassSubgroup_eq_succ_of_even
            K n hnPos hnLt hnEven
        have htargetExponent :
            Int.toNat
                (R / 2 + (D.toNat : Int) -
                  (ramificationIndex K : Int)) = n := by
          dsimp [n, d]
          rw [hRdiv]
          dsimp [x]
          omega
        have hshiftExponent :
            Int.toNat (T + (D.toNat : Int)) = n + 1 := by
          dsimp [n, d]
          rw [hT]
          dsimp [x] at hxOdd
          omega
        rw [beliLemma314CongruenceFactor_of_ne_top
            (K := K) T D hDtop,
          beliCorollary315EvenCongruenceFactor_of_ne_top
            (K := K) R D hDtop,
          hshiftExponent, htargetExponent, ← hfiltration]

/-- Beli (2003), Corollary 3.15(ii), in the paper's printed exponent form
`R / 2 + d(εη) - e`. -/
theorem beliSpinorGroupRepresentative_sup_of_even_order
    [QuadraticDefectLaws K]
    [BeliHilbertCongruenceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε η : Kˣ)
    (hε : IsValuationUnit K (ε : K))
    (hη : IsValuationUnit K (η : K))
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hb : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * η))
    (hRupper : R ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even R)
    (hdε : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞))
    (hdη : ¬2 * quadraticDefect K (-η) ≤
      (Int.toNat
        (2 * (ramificationIndex K : Int) - R) : ℕ∞)) :
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
      beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) := by
  calc
    beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * η) =
        beliLemma314CongruenceFactor (K := K)
            (beliLemma313EvenShift (K := K) R)
            (quadraticDefect K (ε * η)) ⊔
          beliSpinorGroupRepresentative K
            (uniformizerPowerUnit K R * ε) :=
      beliSpinorGroupRepresentative_sup_even_shift
        (K := K) R ε η hε hη ha hb hRupper hEven hdε hdη
    _ = beliCorollary315EvenCongruenceFactor (K := K) R
          (quadraticDefect K (ε * η)) ⊔
        beliSpinorGroupRepresentative K
          (uniformizerPowerUnit K R * ε) :=
      beliLemma314EvenShiftFactor_sup_spinor_eq_corollary315
        (K := K) R ε η hε hη ha hRupper hEven hdε hdη

end Bong.Dyadic
