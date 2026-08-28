/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDefectCriterion
import Bong.Dyadic.BeliGroups
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Beli's binary spinor-group formulas

This file formalizes Beli (2003), Definitions 4 and 5 on representatives
`a : Kˣ`.  The function in the paper is defined on `Kˣ / 𝓞ˣ²`; descent to
that quotient is treated separately after representative invariance is proved.

The fourfold comparisons avoid fractions in the defect cutoffs.  The last
exponent in Definition 4(vi) is encoded as
`e - floor ((2e - R) / 4)` using integer Euclidean division.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The field unit `-1/4`, representing the exceptional hyperbolic class. -/
noncomputable def negativeQuarterUnit : Kˣ :=
  Units.mk0 (-(4 : K)⁻¹) (by norm_num)

/-- The exceptional parameter `-1/4` has order `-2e`. -/
theorem ordUnit_negativeQuarterUnit :
    ordUnit K (negativeQuarterUnit K) =
      -(2 * (ramificationIndex K : Int)) := by
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  change ord K (-(4 : K)⁻¹) =
    ((-(2 * (ramificationIndex K : Int)) : Int) : WithTop Int)
  rw [ord_neg, AddValuation.map_inv]
  have hfour : (4 : K) = 2 * 2 := by norm_num
  rw [hfour, ord_mul, ← ramificationIndex_spec]
  norm_cast
  omega

/-- The cyclic square-class subgroup denoted `⟨a⟩ Kˣ² / Kˣ²`. -/
noncomputable def cyclicSquareClassSubgroup (a : Kˣ) :
    Subgroup (SquareClass K) :=
  Subgroup.zpowers (squareClass K a)

/-- The exponent `R + d - 2e` in Definition 4(ii). -/
noncomputable def beliSpinorCaseIILowExponent (a : Kˣ) : Nat :=
  Int.toNat
    (ordUnit K a + (beliParameterDefectNat K a : Int) -
      2 * (ramificationIndex K : Int))

/-- The exponent `R/2` in Definition 4(iii). -/
noncomputable def beliSpinorCaseIIHighExponent (a : Kˣ) : Nat :=
  Int.toNat (ordUnit K a / 2)

/-- The exponent `R/2 + d - e` in Definition 4(v). -/
noncomputable def beliSpinorCaseIIIMiddleExponent (a : Kˣ) : Nat :=
  Int.toNat
    (ordUnit K a / 2 + (beliParameterDefectNat K a : Int) -
      (ramificationIndex K : Int))

/-- The exponent `e - floor(e/2 - R/4)` in Definition 4(vi). -/
noncomputable def beliSpinorCaseIIIHighExponent (a : Kˣ) : Nat :=
  Int.toNat
    ((ramificationIndex K : Int) -
      (2 * (ramificationIndex K : Int) - ordUnit K a) / 4)

/-- Twice the cutoff `2e - R/2` used in Definition 4(II). -/
noncomputable def beliSpinorCaseIICutoff (a : Kˣ) : Nat :=
  Int.toNat (4 * (ramificationIndex K : Int) - ordUnit K a)

/-- Twice the lower cutoff `e - R/2` used in Definition 4(III). -/
noncomputable def beliSpinorCaseIIILowerCutoff (a : Kˣ) : Nat :=
  Int.toNat (2 * (ramificationIndex K : Int) - ordUnit K a)

/-- Four times the upper cutoff `3e/2 - R/4` in Definition 4(III). -/
noncomputable def beliSpinorCaseIIIUpperCutoff (a : Kˣ) : Nat :=
  Int.toNat (6 * (ramificationIndex K : Int) - ordUnit K a)

/-- Beli (2003), Definition 4, evaluated on a representative `a : Kˣ`.

Joins are products of subgroups in the abelian square-class group.  The order
of the tests exactly follows the exceptional and six numbered cases in the
paper. -/
noncomputable def beliSpinorGroupRepresentative (a : Kˣ) :
    Subgroup (SquareClass K) := by
  classical
  exact
    if ¬BONG.IsBinaryParameterAdmissible a then
      quadraticNormSquareClassSubgroup K (-a)
    else if unitSquareClass K a =
        unitSquareClass K (negativeQuarterUnit K) then
      valuationUnitSquareClassSubgroup K
    else if 4 * (ramificationIndex K : Int) < ordUnit K a then
      cyclicSquareClassSubgroup K a
    else if 2 * (ramificationIndex K : Int) < ordUnit K a then
      if 2 * beliParameterDefect K a ≤
          (beliSpinorCaseIICutoff K a : ℕ∞) then
        cyclicSquareClassSubgroup K a ⊔
          (principalUnitSquareClassSubgroup K
              (beliSpinorCaseIILowExponent K a) ⊓
            quadraticNormSquareClassSubgroup K (-a))
      else
        cyclicSquareClassSubgroup K a ⊔
          principalUnitSquareClassSubgroup K
            (beliSpinorCaseIIHighExponent K a)
    else if 2 * beliParameterDefect K a ≤
        (beliSpinorCaseIIILowerCutoff K a : ℕ∞) then
      quadraticNormSquareClassSubgroup K (-a)
    else if 4 * beliParameterDefect K a ≤
        (beliSpinorCaseIIIUpperCutoff K a : ℕ∞) then
      principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIIMiddleExponent K a) ⊓
        quadraticNormSquareClassSubgroup K (-a)
    else
      principalUnitSquareClassSubgroup K
        (beliSpinorCaseIIIHighExponent K a)

/-- Definition 4 outside the admissible parameter set. -/
theorem beliSpinorGroupRepresentative_of_not_admissible
    (a : Kˣ) (ha : ¬BONG.IsBinaryParameterAdmissible a) :
    beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
  simp [beliSpinorGroupRepresentative, ha]

/-- The exceptional value `G(-1/4) = 𝓞ˣ Kˣ² / Kˣ²`. -/
theorem beliSpinorGroupRepresentative_of_negativeQuarter
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)) :
    beliSpinorGroupRepresentative K a =
      valuationUnitSquareClassSubgroup K := by
  simp [beliSpinorGroupRepresentative, ha, hquarter]

/-- Definition 4(I). -/
theorem beliSpinorGroupRepresentative_caseI
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : 4 * (ramificationIndex K : Int) < ordUnit K a) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a := by
  simp [beliSpinorGroupRepresentative, ha, hquarter, hR]

/-- Definition 4(II)(ii). -/
theorem beliSpinorGroupRepresentative_caseII_low
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hd : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞)) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a ⊔
        (principalUnitSquareClassSubgroup K
            (beliSpinorCaseIILowExponent K a) ⊓
          quadraticNormSquareClassSubgroup K (-a)) := by
  have hnotHigh : ¬4 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr hRhigh
  simp [beliSpinorGroupRepresentative, ha, hquarter, hnotHigh,
    hRlow, hd]

/-- Definition 4(II)(iii). -/
theorem beliSpinorGroupRepresentative_caseII_high
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hRlow : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞)) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a ⊔
        principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIHighExponent K a) := by
  have hnotHigh : ¬4 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr hRhigh
  simp [beliSpinorGroupRepresentative, ha, hquarter, hnotHigh,
    hRlow, hd]

/-- Definition 4(III)(iv). -/
theorem beliSpinorGroupRepresentative_caseIII_low
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hd : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞)) :
    beliSpinorGroupRepresentative K a =
      quadraticNormSquareClassSubgroup K (-a) := by
  have hnotMiddle : ¬2 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr hR
  have hnotHigh : ¬4 * (ramificationIndex K : Int) < ordUnit K a := by
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  simp [beliSpinorGroupRepresentative, ha, hquarter, hnotHigh,
    hnotMiddle, hd]

/-- Definition 4(III)(v). -/
theorem beliSpinorGroupRepresentative_caseIII_middle
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hdLow : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hdHigh : 4 * beliParameterDefect K a ≤
      (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)) :
    beliSpinorGroupRepresentative K a =
      principalUnitSquareClassSubgroup K
          (beliSpinorCaseIIIMiddleExponent K a) ⊓
        quadraticNormSquareClassSubgroup K (-a) := by
  have hnotMiddle : ¬2 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr hR
  have hnotHigh : ¬4 * (ramificationIndex K : Int) < ordUnit K a := by
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  simp [beliSpinorGroupRepresentative, ha, hquarter, hnotHigh,
    hnotMiddle, hdLow, hdHigh]

/-- Definition 4(III)(vi). -/
theorem beliSpinorGroupRepresentative_caseIII_high
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hdLow : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (hdHigh : ¬4 * beliParameterDefect K a ≤
      (beliSpinorCaseIIIUpperCutoff K a : ℕ∞)) :
    beliSpinorGroupRepresentative K a =
      principalUnitSquareClassSubgroup K
        (beliSpinorCaseIIIHighExponent K a) := by
  have hnotMiddle : ¬2 * (ramificationIndex K : Int) < ordUnit K a :=
    not_lt.mpr hR
  have hnotHigh : ¬4 * (ramificationIndex K : Int) < ordUnit K a := by
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  simp [beliSpinorGroupRepresentative, ha, hquarter, hnotHigh,
    hnotMiddle, hdLow, hdHigh]

/-- The representative formula underlying Definition 5.  The paper uses this
formula only when `R > 2e`; the proof-carrying wrapper below records that
domain. -/
noncomputable def beliAuxiliarySpinorGroupRepresentative (a : Kˣ) :
    Subgroup (SquareClass K) :=
  if 4 * (ramificationIndex K : Int) < ordUnit K a then
    ⊥
  else if 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞) then
    principalUnitSquareClassSubgroup K
        (beliSpinorCaseIILowExponent K a) ⊓
      quadraticNormSquareClassSubgroup K (-a)
  else
    principalUnitSquareClassSubgroup K
      (beliSpinorCaseIIHighExponent K a)

/-- Beli (2003), Definition 5.  Its stated domain is `R > 2e`, recorded by
the proof argument. -/
noncomputable def beliAuxiliarySpinorGroup (a : Kˣ)
    (_hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    Subgroup (SquareClass K) :=
  beliAuxiliarySpinorGroupRepresentative K a

/-- Definition 5(I). -/
theorem beliAuxiliarySpinorGroup_caseI
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : 4 * (ramificationIndex K : Int) < ordUnit K a) :
    beliAuxiliarySpinorGroup K a hR = ⊥ := by
  simp [beliAuxiliarySpinorGroup,
    beliAuxiliarySpinorGroupRepresentative, hRhigh]

/-- Definition 5(II)(ii). -/
theorem beliAuxiliarySpinorGroup_caseII_low
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hd : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞)) :
    beliAuxiliarySpinorGroup K a hR =
      principalUnitSquareClassSubgroup K
          (beliSpinorCaseIILowExponent K a) ⊓
        quadraticNormSquareClassSubgroup K (-a) := by
  simp [beliAuxiliarySpinorGroup,
    beliAuxiliarySpinorGroupRepresentative, not_lt.mpr hRhigh, hd]

/-- Definition 5(II)(iii). -/
theorem beliAuxiliarySpinorGroup_caseII_high
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a)
    (hRhigh : ordUnit K a ≤ 4 * (ramificationIndex K : Int))
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIICutoff K a : ℕ∞)) :
    beliAuxiliarySpinorGroup K a hR =
      principalUnitSquareClassSubgroup K
        (beliSpinorCaseIIHighExponent K a) := by
  simp [beliAuxiliarySpinorGroup,
    beliAuxiliarySpinorGroupRepresentative, not_lt.mpr hRhigh, hd]

/-- The relation `G(a) = ⟨a⟩ G'(a)` stated after Definition 5. -/
theorem beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hquarter : unitSquareClass K a ≠
      unitSquareClass K (negativeQuarterUnit K))
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliSpinorGroupRepresentative K a =
      cyclicSquareClassSubgroup K a ⊔
        beliAuxiliarySpinorGroup K a hR := by
  by_cases hRhigh : 4 * (ramificationIndex K : Int) < ordUnit K a
  · simp [beliSpinorGroupRepresentative, beliAuxiliarySpinorGroup,
      beliAuxiliarySpinorGroupRepresentative, ha, hquarter, hRhigh]
  · by_cases hd : 2 * beliParameterDefect K a ≤
        (beliSpinorCaseIICutoff K a : ℕ∞)
    · simp [beliSpinorGroupRepresentative, beliAuxiliarySpinorGroup,
        beliAuxiliarySpinorGroupRepresentative, ha, hquarter, hR,
        hRhigh, hd]
    · simp [beliSpinorGroupRepresentative, beliAuxiliarySpinorGroup,
        beliAuxiliarySpinorGroupRepresentative, ha, hquarter, hR,
        hRhigh, hd]

end Bong.Dyadic
