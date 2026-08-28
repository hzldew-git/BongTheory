/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma72
import Bong.Bong.BinarySpinorLocalProof

/-!
# Unconditional proof of Beli (2003), Lemma 7.2

This file proves the unit-square-class criterion for the binary spinor group
and the domination statement for a nonempty family of unit-bounded binary
parameters.  The exceptional finite endpoint is `-Delta/4`; the hyperbolic
endpoint `-1/4` belongs to the strict infinite-defect branch.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

private theorem test_cyclic_le_unit_iff (a : Kˣ) :
    cyclicSquareClassSubgroup K a ≤
        valuationUnitSquareClassSubgroup K ↔
      Even (ordUnit K a) := by
  rw [cyclicSquareClassSubgroup, Subgroup.zpowers_le]
  exact squareClass_mem_valuationUnitSquareClassSubgroup_iff_even a

private theorem test_norm_le_unit_iff
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K] [HilbertSymbolLaws K]
    (c : Kˣ) :
    quadraticNormSquareClassSubgroup K c ≤
        valuationUnitSquareClassSubgroup K ↔
      IsSquare (c * laws.discriminantUnit) := by
  rw [← BONG.quadraticNormSquareClassSubgroup_discriminant_eq_valuationUnit
    (K := K)]
  constructor
  · intro hle
    have hker :
        (squareClassHilbertCharacter K c).ker ≤
          (squareClassHilbertCharacter K laws.discriminantUnit).ker := by
      simpa only [← quadraticNormSquareClassSubgroup_eq_ker] using hle
    have hcases :=
      (ker_inf_le_ker_iff
        (squareClassHilbertCharacter K c)
        (squareClassHilbertCharacter K laws.discriminantUnit)
        (⊤ : Subgroup (SquareClass K))).1 (by simpa using hker)
    rcases hcases with hdiscTrivial | hproductTrivial
    · let p : Kˣ := uniformizerPowerUnit K 1
      have hp := hdiscTrivial (show squareClass K p ∈
        (⊤ : Subgroup (SquareClass K)) from trivial)
      have hpHilbert :
          hilbertSymbol K laws.discriminantUnit p = 1 := by
        simpa only [MonoidHom.mem_ker,
          squareClassHilbertCharacter_apply] using hp
      have hpEven : Even (ordUnit K p) :=
        (hilbertSymbol_discriminant_eq_one_iff_even_order p).1 hpHilbert
      have hpOrder : ordUnit K p = 1 :=
        ordUnit_uniformizerPowerUnit (K := K) 1
      rw [hpOrder] at hpEven
      norm_num at hpEven
    · have hcharacter :
        squareClassHilbertCharacter K (c * laws.discriminantUnit) =
            squareClassHilbertCharacter K c *
              squareClassHilbertCharacter K laws.discriminantUnit := by
        ext b
        change (hilbertSymbol K (c * laws.discriminantUnit) b : Int) =
          (hilbertSymbol K c b : Int) *
            (hilbertSymbol K laws.discriminantUnit b : Int)
        rw [hilbertSymbol_mul_left]
        rfl
      rw [← hcharacter] at hproductTrivial
      apply (hilbertSymbol_left_trivial_iff_isSquare K
        (c * laws.discriminantUnit)).1
      intro b
      have hb := hproductTrivial
        (show squareClass K b ∈ (⊤ : Subgroup (SquareClass K)) from trivial)
      simpa only [MonoidHom.mem_ker,
        squareClassHilbertCharacter_apply] using hb
  · rintro ⟨s, hs⟩
    have hfactor : c = laws.discriminantUnit *
        (s * laws.discriminantUnit⁻¹) ^ 2 := by
      calc
        c = (c * laws.discriminantUnit) *
            laws.discriminantUnit⁻¹ := by simp
        _ = s ^ 2 * laws.discriminantUnit⁻¹ := by rw [hs, pow_two]
        _ = laws.discriminantUnit *
            (s * laws.discriminantUnit⁻¹) ^ 2 := by
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    rw [hfactor, quadraticNormSquareClassSubgroup_mul_square]

private theorem test_norm_le_unit_iff_endpoint
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K] [HilbertSymbolLaws K]
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hdLow : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞)) :
    quadraticNormSquareClassSubgroup K (-a) ≤
        valuationUnitSquareClassSubgroup K ↔
      IsNegativeDiscriminantQuarterParameter (K := K) a := by
  rw [test_norm_le_unit_iff (K := K) (-a)]
  constructor
  · intro hsquare
    rcases hsquare with ⟨s, hs⟩
    have hdeltaOrder : ordUnit K laws.discriminantUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        laws.discriminant_isValuationUnit
    have horderEq := congrArg (ordUnit K) hs
    have hEven : Even (ordUnit K a) := by
      refine ⟨ordUnit K s, ?_⟩
      rw [ordUnit_mul, ordUnit_neg, hdeltaOrder,
        ordUnit_mul] at horderEq
      omega
    have hfactor : -a = laws.discriminantUnit *
        (s * laws.discriminantUnit⁻¹) ^ 2 := by
      calc
        -a = ((-a) * laws.discriminantUnit) *
            laws.discriminantUnit⁻¹ := by simp
        _ = s ^ 2 * laws.discriminantUnit⁻¹ := by rw [hs, pow_two]
        _ = laws.discriminantUnit *
            (s * laws.discriminantUnit⁻¹) ^ 2 := by
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hdefect : beliParameterDefect K a =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      unfold beliParameterDefect
      rw [hfactor, quadraticDefect_mul_square,
        laws.discriminant_defect]
    have hcutNonneg :
        0 ≤ 2 * (ramificationIndex K : Int) - ordUnit K a := by
      omega
    have hdLow' := hdLow
    rw [hdefect] at hdLow'
    unfold beliSpinorCaseIIILowerCutoff at hdLow'
    norm_cast at hdLow'
    have hcast : ((2 * ramificationIndex K : Nat) : Int) =
        2 * (ramificationIndex K : Int) := by norm_num
    rw [hcast] at hdLow'
    have hdLowInt :
        ((2 * (2 * ramificationIndex K) : Nat) : Int) ≤
          (((2 * (ramificationIndex K : Int) - ordUnit K a).toNat : Nat) : Int) := by
      exact_mod_cast hdLow'
    rw [Int.toNat_of_nonneg hcutNonneg] at hdLowInt
    refine ⟨?_, hdefect⟩
    have hlower := ha.ordUnit_ge_neg_two_mul_e
    push_cast at hdLowInt
    omega
  · rintro ⟨horder, hdefect⟩
    rcases laws.endpoint_parameter_class a ha horder with
      hquarter | hdiscriminant
    · have htop := beliParameterDefect_eq_of_unitSquareClass_eq
          (K := K) hquarter
      rw [beliParameterDefect_negativeQuarterUnit] at htop
      rw [htop] at hdefect
      exact (ENat.coe_ne_top _ hdefect.symm).elim
    · exact isSquare_neg_mul_discriminant_of_endpointClass hdiscriminant

private theorem test_strict_threshold_iff_not_low
    (a : Kˣ)
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int)) :
    ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) <
        beliParameterDefectOrderQ (K := K) a ↔
      ¬2 * beliParameterDefect K a ≤
        (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
  cases hdefect : beliParameterDefect K a with
  | top =>
      unfold beliParameterDefectOrderQ lemma72DefectThreshold
        beliSpinorCaseIIILowerCutoff
      rw [hdefect]
      change
        (((ramificationIndex K : ℚ) - (ordUnit K a : ℚ) / 2 : ℚ) :
            WithTop ℚ) < ⊤ ↔
          ¬2 * (⊤ : ℕ∞) ≤
            ((Int.toNat
              (2 * (ramificationIndex K : Int) - ordUnit K a) : Nat) : ℕ∞)
      simp
      exact WithTop.coe_lt_top _
  | coe d =>
      unfold beliParameterDefectOrderQ lemma72DefectThreshold
        beliSpinorCaseIIILowerCutoff
      rw [hdefect]
      change
        (((ramificationIndex K : ℚ) - (ordUnit K a : ℚ) / 2 : ℚ) :
            WithTop ℚ) < (((d : Nat) : ℚ) : WithTop ℚ) ↔
          ¬2 * ((d : Nat) : ℕ∞) ≤
            ((Int.toNat
              (2 * (ramificationIndex K : Int) - ordUnit K a) : Nat) : ℕ∞)
      norm_cast
      have hcutNonneg :
          0 ≤ 2 * (ramificationIndex K : Int) - ordUnit K a := by
        omega
      have hcut :
          ((Int.toNat
              (2 * (ramificationIndex K : Int) - ordUnit K a) : Nat) : Int) =
            2 * (ramificationIndex K : Int) - ordUnit K a :=
        Int.toNat_of_nonneg hcutNonneg
      constructor
      · intro h
        simp only [Rat.divInt_eq_div] at h
        have hq :
            ((2 * (ramificationIndex K : Int) - ordUnit K a : Int) : ℚ) <
              ((2 * d : Nat) : ℚ) := by
          push_cast
          linarith
        have hint :
            2 * (ramificationIndex K : Int) - ordUnit K a <
              ((2 * d : Nat) : Int) := by
          exact_mod_cast hq
        have hcutLt :
            Int.toNat
                (2 * (ramificationIndex K : Int) - ordUnit K a) <
              2 * d := by
          exact_mod_cast (show
            ((Int.toNat
                (2 * (ramificationIndex K : Int) - ordUnit K a) : Nat) : Int) <
              ((2 * d : Nat) : Int) by simpa [hcut] using hint)
        omega
      · intro h
        have hcutLt :
            Int.toNat
                (2 * (ramificationIndex K : Int) - ordUnit K a) <
              2 * d := by omega
        have hint :
            2 * (ramificationIndex K : Int) - ordUnit K a <
              ((2 * d : Nat) : Int) := by
          rw [← hcut]
          exact_mod_cast hcutLt
        have hq :
            ((2 * (ramificationIndex K : Int) - ordUnit K a : Int) : ℚ) <
              ((2 * d : Nat) : ℚ) := by
          exact_mod_cast hint
        push_cast at hq
        simp only [Rat.divInt_eq_div]
        linarith

private theorem test_even_of_not_low
    (a : Kˣ)
    (hnotLow : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞)) :
    Even (ordUnit K a) := by
  rcases Int.even_or_odd (ordUnit K a) with hEven | hOdd
  · exact hEven
  · have hOddNeg : Odd (ordUnit K (-a)) := by
      simpa only [ordUnit_neg] using hOdd
    have hzero : quadraticDefect K (-a) = 0 :=
      quadraticDefect_eq_zero_of_odd_ordUnit (-a) hOddNeg
    unfold beliParameterDefect at hnotLow
    rw [hzero] at hnotLow
    simp at hnotLow

private theorem test_strict_threshold_of_two_e_lt
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) <
      beliParameterDefectOrderQ (K := K) a := by
  cases hdefect : beliParameterDefect K a with
  | top =>
      unfold beliParameterDefectOrderQ
      rw [hdefect]
      change
        ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) < ⊤
      exact WithTop.coe_lt_top _
  | coe d =>
      unfold beliParameterDefectOrderQ lemma72DefectThreshold
      rw [hdefect]
      change
        (((ramificationIndex K : ℚ) - (ordUnit K a : ℚ) / 2 : ℚ) :
          WithTop ℚ) < (((d : Nat) : ℚ) : WithTop ℚ)
      norm_cast
      simp only [Rat.divInt_eq_div]
      have hd : (0 : ℚ) ≤ d := by positivity
      have hRq :
          ((2 * (ramificationIndex K : Int) : Int) : ℚ) <
            ((ordUnit K a : Int) : ℚ) := by exact_mod_cast hR
      push_cast at hRq
      linarith

theorem beliLemma72_i_proved
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliSpinorGroupRepresentative K a ≤
        valuationUnitSquareClassSubgroup K ↔
      SatisfiesLemma72UnitCriterion (K := K) a := by
  by_cases hquarter : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)
  · rw [beliSpinorGroupRepresentative_of_negativeQuarter K a ha hquarter]
    constructor
    · intro _
      have horder := ordUnit_eq_of_unitSquareClass_eq (K := K) hquarter
      rw [ordUnit_negativeQuarterUnit] at horder
      have hEven : Even (ordUnit K a) := by
        refine ⟨-(ramificationIndex K : Int), ?_⟩
        omega
      refine ⟨hEven, Or.inr ?_⟩
      rw [beliParameterDefectOrderQ_eq_top_of_negativeQuarter
        (K := K) a hquarter]
      exact WithTop.coe_lt_top _
    · intro _
      exact le_rfl
  · by_cases hcaseI :
        4 * (ramificationIndex K : Int) < ordUnit K a
    · rw [beliSpinorGroupRepresentative_caseI K a ha hquarter hcaseI,
        test_cyclic_le_unit_iff]
      constructor
      · intro hEven
        refine ⟨hEven, Or.inr ?_⟩
        apply test_strict_threshold_of_two_e_lt (K := K) a
        have he : 0 ≤ (ramificationIndex K : Int) := by positivity
        omega
      · exact fun h ↦ h.1
    · have hRhigh :
          ordUnit K a ≤ 4 * (ramificationIndex K : Int) := by omega
      by_cases hcaseII :
          2 * (ramificationIndex K : Int) < ordUnit K a
      · have hstrict := test_strict_threshold_of_two_e_lt
          (K := K) a hcaseII
        by_cases hdLow : 2 * beliParameterDefect K a ≤
            (beliSpinorCaseIICutoff K a : ℕ∞)
        · rw [beliSpinorGroupRepresentative_caseII_low K a ha hquarter
              hcaseII hRhigh hdLow]
          constructor
          · intro hG
            have hcyclic : cyclicSquareClassSubgroup K a ≤
                valuationUnitSquareClassSubgroup K :=
              (le_sup_left : cyclicSquareClassSubgroup K a ≤
                  cyclicSquareClassSubgroup K a ⊔
                    (principalUnitSquareClassSubgroup K
                        (beliSpinorCaseIILowExponent K a) ⊓
                      quadraticNormSquareClassSubgroup K (-a))).trans hG
            exact ⟨(test_cyclic_le_unit_iff (K := K) a).1 hcyclic,
              Or.inr hstrict⟩
          · rintro ⟨hEven, _⟩
            apply sup_le
            · exact (test_cyclic_le_unit_iff (K := K) a).2 hEven
            · exact inf_le_left.trans
                (principalUnitSquareClassSubgroup_le_valuationUnit K _)
        · rw [beliSpinorGroupRepresentative_caseII_high K a ha hquarter
              hcaseII hRhigh hdLow]
          constructor
          · intro hG
            have hcyclic : cyclicSquareClassSubgroup K a ≤
                valuationUnitSquareClassSubgroup K :=
              (le_sup_left : cyclicSquareClassSubgroup K a ≤
                  cyclicSquareClassSubgroup K a ⊔
                    principalUnitSquareClassSubgroup K
                      (beliSpinorCaseIIHighExponent K a)).trans hG
            exact ⟨(test_cyclic_le_unit_iff (K := K) a).1 hcyclic,
              Or.inr hstrict⟩
          · rintro ⟨hEven, _⟩
            exact sup_le
              ((test_cyclic_le_unit_iff (K := K) a).2 hEven)
              (principalUnitSquareClassSubgroup_le_valuationUnit K _)
      · have hR :
            ordUnit K a ≤ 2 * (ramificationIndex K : Int) := by omega
        by_cases hdLow : 2 * beliParameterDefect K a ≤
            (beliSpinorCaseIIILowerCutoff K a : ℕ∞)
        · rw [beliSpinorGroupRepresentative_caseIII_low K a ha hquarter
              hR hdLow,
            test_norm_le_unit_iff_endpoint (K := K) a ha hR hdLow]
          constructor
          · intro hendpoint
            refine ⟨?_, Or.inl hendpoint⟩
            rcases hendpoint with ⟨horder, _⟩
            refine ⟨-(ramificationIndex K : Int), ?_⟩
            omega
          · rintro ⟨_, hendpoint | hstrict⟩
            · exact hendpoint
            · exact (((test_strict_threshold_iff_not_low
                  (K := K) a hR).1 hstrict) hdLow).elim
        · have hEven := test_even_of_not_low (K := K) a hdLow
          have hstrict :=
            (test_strict_threshold_iff_not_low (K := K) a hR).2 hdLow
          by_cases hdHigh : 4 * beliParameterDefect K a ≤
              (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)
          · rw [beliSpinorGroupRepresentative_caseIII_middle K a ha
                hquarter hR hdLow hdHigh]
            constructor
            · intro _
              exact ⟨hEven, Or.inr hstrict⟩
            · intro _
              exact inf_le_left.trans
                (principalUnitSquareClassSubgroup_le_valuationUnit K _)
          · rw [beliSpinorGroupRepresentative_caseIII_high K a ha
                hquarter hR hdLow hdHigh]
            constructor
            · intro _
              exact ⟨hEven, Or.inr hstrict⟩
            · intro _
              exact principalUnitSquareClassSubgroup_le_valuationUnit K _

private theorem test_combinedParameterDefect_eq_product
    {k : Nat} (a : Fin k → Kˣ) (R : Int)
    (hk : 0 < k) (hR : Even R) :
    beliParameterDefect K (lemma72CombinedParameter (K := K) a R) =
      quadraticDefect K (∏ i, -(normalizedUnitPart K (a i))) := by
  rcases hR with ⟨r, hr⟩
  have hpower : uniformizerPowerUnit K R =
      uniformizerPowerUnit K r ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
  have hsign :
      -((-1 : Kˣ) ^ (k - 1)) = (-1 : Kˣ) ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [pow_succ, mul_comm]
  have hnegative :
      -(lemma72CombinedParameter (K := K) a R) =
        (∏ i, -(normalizedUnitPart K (a i))) *
          uniformizerPowerUnit K r ^ 2 := by
    classical
    unfold lemma72CombinedParameter
    rw [hpower]
    calc
      -((-1 : Kˣ) ^ (k - 1) * uniformizerPowerUnit K r ^ 2 *
          ∏ i, normalizedUnitPart K (a i)) =
          (-((-1 : Kˣ) ^ (k - 1))) *
            uniformizerPowerUnit K r ^ 2 *
              ∏ i, normalizedUnitPart K (a i) := by
            apply Units.ext
            simp only [Units.val_neg, Units.val_mul]
            ring
      _ = (-1 : Kˣ) ^ k * uniformizerPowerUnit K r ^ 2 *
            ∏ i, normalizedUnitPart K (a i) := by rw [hsign]
      _ = (∏ i, -(normalizedUnitPart K (a i))) *
            uniformizerPowerUnit K r ^ 2 := by
        rw [Finset.prod_neg]
        simp only [Finset.card_univ, Fintype.card_fin]
        ac_rfl
  unfold beliParameterDefect
  rw [hnegative, quadraticDefect_mul_square]

private theorem test_le_quadraticDefect_prod
    {k : Nat} (s : Finset (Fin k)) (f : Fin k → Kˣ) (d : ℕ∞)
    (h : ∀ i ∈ s, d ≤ quadraticDefect K (f i)) :
    d ≤ quadraticDefect K (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      rw [quadraticDefect_eq_top_of_isSquare K (show IsSquare (1 : Kˣ) by
        exact ⟨1, by simp⟩)]
      exact le_top
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (le_min (h i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))).trans
          (quadraticDefect_mul_ge_min K (f i) (∏ j ∈ s, f j))

private theorem test_natCast_le_defectOrderQ_iff (m : Nat) (d : ℕ∞) :
    (((m : Nat) : ℚ) : WithTop ℚ) ≤
        WithTop.map (fun n : Nat ↦ (n : ℚ)) d ↔
      (m : ℕ∞) ≤ d := by
  cases d with
  | top =>
      change (((m : Nat) : ℚ) : WithTop ℚ) ≤ ⊤ ↔
        (m : ℕ∞) ≤ ⊤
      simp
  | coe n =>
      change (((m : Nat) : ℚ) : WithTop ℚ) ≤
          (((n : Nat) : ℚ) : WithTop ℚ) ↔
        (m : ℕ∞) ≤ (n : ℕ∞)
      norm_cast

private theorem test_natCast_lt_defectOrderQ_iff (m : Nat) (d : ℕ∞) :
    (((m : Nat) : ℚ) : WithTop ℚ) <
        WithTop.map (fun n : Nat ↦ (n : ℚ)) d ↔
      (m : ℕ∞) < d := by
  cases d with
  | top =>
      change (((m : Nat) : ℚ) : WithTop ℚ) < ⊤ ↔
        (m : ℕ∞) < ⊤
      simp
  | coe n =>
      change (((m : Nat) : ℚ) : WithTop ℚ) <
          (((n : Nat) : ℚ) : WithTop ℚ) ↔
        (m : ℕ∞) < (n : ℕ∞)
      norm_cast

private theorem test_lemma72DefectThreshold_anti
    (a b : Kˣ) (horder : ordUnit K a ≤ ordUnit K b) :
    lemma72DefectThreshold (K := K) b ≤
      lemma72DefectThreshold (K := K) a := by
  unfold lemma72DefectThreshold
  have hq : ((ordUnit K a : Int) : ℚ) ≤
      ((ordUnit K b : Int) : ℚ) := by exact_mod_cast horder
  linarith

private theorem test_lemma72DefectThreshold_strictAnti
    (a b : Kˣ) (horder : ordUnit K a < ordUnit K b) :
    lemma72DefectThreshold (K := K) b <
      lemma72DefectThreshold (K := K) a := by
  unfold lemma72DefectThreshold
  have hq : ((ordUnit K a : Int) : ℚ) <
      ((ordUnit K b : Int) : ℚ) := by exact_mod_cast horder
  linarith

private theorem test_defect_lower_bound_of_criterion
    (a : Kˣ) (h : SatisfiesLemma72UnitCriterion (K := K) a) :
    ((lemma72DefectThreshold (K := K) a : ℚ) : WithTop ℚ) ≤
      beliParameterDefectOrderQ (K := K) a := by
  rcases h with ⟨_, hendpoint | hstrict⟩
  · rcases hendpoint with ⟨horder, hdefect⟩
    unfold lemma72DefectThreshold beliParameterDefectOrderQ
    rw [horder, hdefect]
    change
      (((ramificationIndex K : ℚ) -
          ((-(2 * (ramificationIndex K : Int)) : Int) : ℚ) / 2 : ℚ) :
        WithTop ℚ) ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
    have hhalf :
        ((-(2 * (ramificationIndex K : Int)) : Int) : ℚ) / 2 =
          -(ramificationIndex K : ℚ) := by
      push_cast
      ring
    have htwo : ((2 * ramificationIndex K : Nat) : ℚ) =
        2 * (ramificationIndex K : ℚ) := by norm_num
    rw [hhalf, htwo]
    have hint :
        (ramificationIndex K : Int) - -(ramificationIndex K : Int) =
          2 * (ramificationIndex K : Int) := by ring
    exact_mod_cast hint.le
  · exact hstrict.le

theorem beliLemma72_ii_proved
    {k : Nat} (a : Fin k → Kˣ) (R : Int)
    (hk : 0 < k)
    (ha : ∀ i, IsLemma72UnitParameter (K := K) (a i))
    (hR : Even R) (horder : ∀ i, ordUnit K (a i) ≤ R) :
    IsLemma72UnitParameter (K := K)
      (lemma72CombinedParameter (K := K) a R) := by
  classical
  let t : Kˣ := lemma72CombinedParameter (K := K) a R
  have htOrder : ordUnit K t = R := by
    simpa only [t] using ordUnit_lemma72CombinedParameter (K := K) a R
  have hcriterion : ∀ i,
      SatisfiesLemma72UnitCriterion (K := K) (a i) := by
    intro i
    exact (beliLemma72_i_proved (K := K) (a i) (ha i).1).1 (ha i).2
  have hiEven : ∀ i, Even (ordUnit K (a i)) :=
    fun i ↦ (hcriterion i).1
  let i₀ : Fin k := ⟨0, hk⟩
  have hRlower : -(2 * (ramificationIndex K : Int)) ≤ R := by
    have hiLower := (ha i₀).1.ordUnit_ge_neg_two_mul_e
    exact hiLower.trans (horder i₀)
  have htDefect :
      quadraticDefect K (-t) =
        quadraticDefect K (∏ i, -(normalizedUnitPart K (a i))) := by
    simpa only [t, beliParameterDefect] using
      test_combinedParameterDefect_eq_product
        (K := K) a R hk hR
  have hfactorAbsolute : ∀ i,
      (absoluteDefectThreshold (-t) : ℕ∞) ≤
        quadraticDefect K (-(normalizedUnitPart K (a i))) := by
    intro i
    have hiAdmissible :=
      (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
        (a i)).1 (ha i).1
    have hiDefect :=
      (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le
        (K := K) (-a i)).1 hiAdmissible.2
    have hthresholdNat :
        absoluteDefectThreshold (-t) ≤
          absoluteDefectThreshold (-a i) := by
      unfold absoluteDefectThreshold
      apply Int.toNat_le_toNat
      rw [ordUnit_neg, htOrder, ordUnit_neg]
      have hiOrder := horder i
      omega
    have hthresholdENat :
        (absoluteDefectThreshold (-t) : ℕ∞) ≤
          (absoluteDefectThreshold (-a i) : ℕ∞) := by
      exact_mod_cast hthresholdNat
    have htoInput :
        (absoluteDefectThreshold (-t) : ℕ∞) ≤
          quadraticDefect K (-a i) :=
      hthresholdENat.trans hiDefect
    rw [BONG.beliParameterDefect_eq_normalizedUnitPart_of_even
      (K := K) (a i) (hiEven i)] at htoInput
    exact htoInput
  have hproductAbsolute :
      (absoluteDefectThreshold (-t) : ℕ∞) ≤
        quadraticDefect K (∏ i, -(normalizedUnitPart K (a i))) := by
    apply test_le_quadraticDefect_prod (K := K) Finset.univ
      (fun i ↦ -(normalizedUnitPart K (a i)))
      (absoluteDefectThreshold (-t) : ℕ∞)
    intro i _
    exact hfactorAbsolute i
  have htAbsolute : HasNonnegativeAbsoluteQuadraticDefect (-t) := by
    apply (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le
      (K := K) (-t)).2
    rw [htDefect]
    exact hproductAbsolute
  have htAdmissible : BONG.IsBinaryParameterAdmissible t := by
    apply (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      t).2
    refine ⟨?_, htAbsolute⟩
    rw [htOrder]
    omega
  refine ⟨htAdmissible, ?_⟩
  apply (beliLemma72_i_proved (K := K) t htAdmissible).2
  refine ⟨?_, ?_⟩
  · rwa [htOrder]
  · by_cases hRlarge :
        2 * (ramificationIndex K : Int) < R
    · right
      apply test_strict_threshold_of_two_e_lt (K := K) t
      rwa [htOrder]
    · have hRupper : R ≤ 2 * (ramificationIndex K : Int) := by omega
      obtain ⟨r, hr⟩ := hR
      let m : Nat := Int.toNat ((ramificationIndex K : Int) - r)
      have hrUpper : r ≤ (ramificationIndex K : Int) := by omega
      have hmNonneg : 0 ≤ (ramificationIndex K : Int) - r := by omega
      have hmInt : (m : Int) = (ramificationIndex K : Int) - r := by
        dsimp [m]
        exact Int.toNat_of_nonneg hmNonneg
      have hmQ : (m : ℚ) = (ramificationIndex K : ℚ) - (r : ℚ) := by
        exact_mod_cast hmInt
      have hrQ : (R : ℚ) = 2 * (r : ℚ) := by
        exact_mod_cast (show R = 2 * r by omega)
      have htThreshold : lemma72DefectThreshold (K := K) t = (m : ℚ) := by
        unfold lemma72DefectThreshold
        rw [htOrder]
        rw [hmQ, hrQ]
        ring
      have hiDefectEq : ∀ i,
          beliParameterDefect K (a i) =
            quadraticDefect K (-(normalizedUnitPart K (a i))) := by
        intro i
        unfold beliParameterDefect
        exact BONG.beliParameterDefect_eq_normalizedUnitPart_of_even
          (K := K) (a i) (hiEven i)
      have hfactorGe : ∀ i,
          (m : ℕ∞) ≤
            quadraticDefect K (-(normalizedUnitPart K (a i))) := by
        intro i
        have hthresholdOrder :
            lemma72DefectThreshold (K := K) t ≤
              lemma72DefectThreshold (K := K) (a i) :=
          test_lemma72DefectThreshold_anti (K := K) (a i) t (by
            rw [htOrder]
            exact horder i)
        have hbound :
            ((lemma72DefectThreshold (K := K) t : ℚ) : WithTop ℚ) ≤
              beliParameterDefectOrderQ (K := K) (a i) :=
          (WithTop.coe_le_coe.mpr hthresholdOrder).trans
            (test_defect_lower_bound_of_criterion
              (K := K) (a i) (hcriterion i))
        unfold beliParameterDefectOrderQ at hbound
        rw [hiDefectEq i] at hbound
        rw [htThreshold] at hbound
        exact (test_natCast_le_defectOrderQ_iff
          (m := m)
          (quadraticDefect K (-(normalizedUnitPart K (a i))))).1 hbound
      have hproductGe :
          (m : ℕ∞) ≤
            quadraticDefect K (∏ i, -(normalizedUnitPart K (a i))) := by
        apply test_le_quadraticDefect_prod (K := K) Finset.univ
          (fun i ↦ -(normalizedUnitPart K (a i))) (m : ℕ∞)
        intro i _
        exact hfactorGe i
      have htGe : (m : ℕ∞) ≤ quadraticDefect K (-t) := by
        rw [htDefect]
        exact hproductGe
      by_cases hEndpointR :
          R = -(2 * (ramificationIndex K : Int))
      · have hrEndpoint : r = -(ramificationIndex K : Int) := by omega
        have hmTwoE : m = 2 * ramificationIndex K := by
          have hmTwoEInt : (m : Int) =
              ((2 * ramificationIndex K : Nat) : Int) := by
            rw [hmInt, hrEndpoint]
            push_cast
            ring
          exact_mod_cast hmTwoEInt
        have htwoELe :
            ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
              quadraticDefect K (-t) := by
          rwa [← hmTwoE]
        let laws : DyadicDiscriminantClassLaws K := inferInstance
        rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
            (-t) htwoELe with hsquare | hdiscriminant
        · right
          have htop : beliParameterDefect K t = ⊤ := by
            unfold beliParameterDefect
            exact quadraticDefect_eq_top_of_isSquare K hsquare
          unfold beliParameterDefectOrderQ
          rw [htop]
          exact WithTop.coe_lt_top _
        · left
          refine ⟨?_, ?_⟩
          · rw [htOrder, hEndpointR]
          · rcases hdiscriminant with ⟨s, hs⟩
            have hfactor : -t = laws.discriminantUnit * s ^ 2 := by
              calc
                -t = ((-t) / laws.discriminantUnit) *
                    laws.discriminantUnit := by simp
                _ = (s * s) * laws.discriminantUnit := by rw [hs]
                _ = laws.discriminantUnit * s ^ 2 := by
                  simp [pow_two, mul_comm]
            unfold beliParameterDefect
            rw [hfactor, quadraticDefect_mul_square,
              laws.discriminant_defect]
      · have hRstrict :
            -(2 * (ramificationIndex K : Int)) < R := by omega
        have hfactorGt : ∀ i,
            (m : ℕ∞) <
              quadraticDefect K (-(normalizedUnitPart K (a i))) := by
          intro i
          have hmap :
              ((lemma72DefectThreshold (K := K) t : ℚ) : WithTop ℚ) <
                beliParameterDefectOrderQ (K := K) (a i) := by
            rcases (hcriterion i).2 with hendpoint | hstrict
            · have horderStrict : ordUnit K (a i) < ordUnit K t := by
                rw [hendpoint.1, htOrder]
                exact hRstrict
              exact (WithTop.coe_lt_coe.mpr
                (test_lemma72DefectThreshold_strictAnti
                  (K := K) (a i) t horderStrict)).trans_le
                    (test_defect_lower_bound_of_criterion
                      (K := K) (a i) (hcriterion i))
            · have hthresholdOrder :
                  lemma72DefectThreshold (K := K) t ≤
                    lemma72DefectThreshold (K := K) (a i) :=
                test_lemma72DefectThreshold_anti (K := K) (a i) t (by
                  rw [htOrder]
                  exact horder i)
              exact (WithTop.coe_le_coe.mpr hthresholdOrder).trans_lt hstrict
          unfold beliParameterDefectOrderQ at hmap
          rw [hiDefectEq i] at hmap
          rw [htThreshold] at hmap
          exact (test_natCast_lt_defectOrderQ_iff
            (m := m)
            (quadraticDefect K (-(normalizedUnitPart K (a i))))).1 hmap
        have hfactorPlus : ∀ i,
            ((m + 1 : Nat) : ℕ∞) ≤
              quadraticDefect K (-(normalizedUnitPart K (a i))) := by
          intro i
          exact ENat.coe_add_one_le_iff.mpr (hfactorGt i)
        have hproductPlus :
            ((m + 1 : Nat) : ℕ∞) ≤
              quadraticDefect K (∏ i, -(normalizedUnitPart K (a i))) := by
          apply test_le_quadraticDefect_prod (K := K) Finset.univ
            (fun i ↦ -(normalizedUnitPart K (a i)))
            ((m + 1 : Nat) : ℕ∞)
          intro i _
          exact hfactorPlus i
        have htPlus : ((m + 1 : Nat) : ℕ∞) ≤
            quadraticDefect K (-t) := by
          rw [htDefect]
          exact hproductPlus
        have htGt : (m : ℕ∞) < quadraticDefect K (-t) :=
          ENat.coe_add_one_le_iff.mp htPlus
        right
        unfold beliParameterDefectOrderQ beliParameterDefect
        rw [htThreshold]
        exact (test_natCast_lt_defectOrderQ_iff
          (m := m) (quadraticDefect K (-t))).2 htGt

end Dyadic

/-- Beli (2003), Lemma 7.2 over every dyadic local field, with no
remaining local-law hypothesis. -/
noncomputable instance beliLemma72LawsProved : BeliLemma72Laws K where
  spinor_group_le_unit_iff a ha :=
    Dyadic.beliLemma72_i_proved (K := K) a ha
  combined_parameter a R hk ha hR horder :=
    Dyadic.beliLemma72_ii_proved (K := K) a R hk ha hR horder

end Bong
