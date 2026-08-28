/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryAdmissibility
import Bong.Bong.BinarySpinorGroupFormula

/-!
# Invariance and descent of Beli's binary spinor group

This file proves that the representative formula for `G(a)` is unchanged by
multiplication by a valuation-unit square.  It therefore descends to the exact
domain `Kˣ / 𝓞ˣ²` used in Beli (2003), Definition 4.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Equality in `Kˣ / 𝓞ˣ²` can be represented by multiplication by a square
of a valuation unit. -/
theorem exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    ∃ s : Kˣ, IsValuationUnit K (s : K) ∧ a * s ^ 2 = b := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) a =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) b at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨z, hz, haz⟩
  rw [mem_valuationUnitSquareSubgroup_iff] at hz
  rcases hz with ⟨s, hs, rfl⟩
  exact ⟨s, hs, haz⟩

/-- Multiplication by a valuation-unit square preserves Beli's parameter
defect `d(-a)`. -/
theorem beliParameterDefect_mul_valuationUnit_square
    (a s : Kˣ) (_hs : IsValuationUnit K (s : K)) :
    beliParameterDefect K (a * s ^ 2) = beliParameterDefect K a := by
  unfold beliParameterDefect
  have hnegative : -(a * s ^ 2) = (-a) * s ^ 2 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hnegative, quadraticDefect_mul_square]

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- The square-class image of a quadratic norm group depends only on the
square class of its parameter. -/
theorem quadraticNormSquareClassSubgroup_mul_square (a s : Kˣ) :
    quadraticNormSquareClassSubgroup K (a * s ^ 2) =
      quadraticNormSquareClassSubgroup K a := by
  have hgroup : quadraticNormGroup K (a * s ^ 2) =
      quadraticNormGroup K a := by
    ext b
    exact isQuadraticNorm_mul_square_left_iff K a b s
  simp [quadraticNormSquareClassSubgroup, hgroup]

/-- Additive order descends to the refined unit-square-class quotient. -/
noncomputable def unitSquareClassOrder : UnitSquareClass K → Int :=
  Quotient.lift (ordUnit K) (by
    intro a b hab
    apply ordUnit_eq_of_unitSquareClass_eq (K := K)
    exact Quotient.sound hab)

@[simp]
theorem unitSquareClassOrder_unitSquareClass (a : Kˣ) :
    unitSquareClassOrder K (unitSquareClass K a) = ordUnit K a :=
  rfl

/-- The formula of Definition 4 is invariant under the choice of a
representative modulo valuation-unit squares. -/
theorem beliSpinorGroupRepresentative_eq_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    beliSpinorGroupRepresentative K a =
      beliSpinorGroupRepresentative K b := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass with ⟨s, hs, hab⟩
  have horder : ordUnit K a = ordUnit K b :=
    ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  have hdefectScaled :=
    beliParameterDefect_mul_valuationUnit_square K a s hs
  have hdefect : beliParameterDefect K a = beliParameterDefect K b := by
    rw [hab] at hdefectScaled
    exact hdefectScaled.symm
  have hdefectNat : beliParameterDefectNat K a =
      beliParameterDefectNat K b := by
    unfold beliParameterDefectNat
    rw [hdefect]
  have hcyclic : cyclicSquareClassSubgroup K a =
      cyclicSquareClassSubgroup K b := by
    have hsquare := congrArg (unitSquareClassToSquareClass K) hclass
    change squareClass K a = squareClass K b at hsquare
    unfold cyclicSquareClassSubgroup
    rw [hsquare]
  have hneg : -b = (-a) * s ^ 2 := by
    rw [← hab]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have hnorm : quadraticNormSquareClassSubgroup K (-a) =
      quadraticNormSquareClassSubgroup K (-b) := by
    rw [hneg, quadraticNormSquareClassSubgroup_mul_square]
  have hIILow : beliSpinorCaseIILowExponent K a =
      beliSpinorCaseIILowExponent K b := by
    unfold beliSpinorCaseIILowExponent
    rw [horder, hdefectNat]
  have hIIHigh : beliSpinorCaseIIHighExponent K a =
      beliSpinorCaseIIHighExponent K b := by
    unfold beliSpinorCaseIIHighExponent
    rw [horder]
  have hIIIMiddle : beliSpinorCaseIIIMiddleExponent K a =
      beliSpinorCaseIIIMiddleExponent K b := by
    unfold beliSpinorCaseIIIMiddleExponent
    rw [horder, hdefectNat]
  have hIIIHigh : beliSpinorCaseIIIHighExponent K a =
      beliSpinorCaseIIIHighExponent K b := by
    unfold beliSpinorCaseIIIHighExponent
    rw [horder]
  have hIICutoff : beliSpinorCaseIICutoff K a =
      beliSpinorCaseIICutoff K b := by
    unfold beliSpinorCaseIICutoff
    rw [horder]
  have hIIILower : beliSpinorCaseIIILowerCutoff K a =
      beliSpinorCaseIIILowerCutoff K b := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [horder]
  have hIIIUpper : beliSpinorCaseIIIUpperCutoff K a =
      beliSpinorCaseIIIUpperCutoff K b := by
    unfold beliSpinorCaseIIIUpperCutoff
    rw [horder]
  have hadmissible :=
    BONG.isBinaryParameterAdmissible_iff_of_unitSquareClass_eq
      (K := K) hclass
  by_cases ha : BONG.IsBinaryParameterAdmissible a
  · have hb : BONG.IsBinaryParameterAdmissible b := hadmissible.mp ha
    by_cases hquarter : unitSquareClass K a =
        unitSquareClass K (negativeQuarterUnit K)
    · have hquarterB : unitSquareClass K b =
          unitSquareClass K (negativeQuarterUnit K) :=
        hclass.symm.trans hquarter
      simp [beliSpinorGroupRepresentative, ha, hb, hquarter,
        hquarterB]
    · have hquarterB : unitSquareClass K b ≠
          unitSquareClass K (negativeQuarterUnit K) :=
        fun hbq => hquarter (hclass.trans hbq)
      simp [beliSpinorGroupRepresentative, ha, hb, hquarter,
        hquarterB, horder, hdefect, hcyclic, hnorm, hIILow,
        hIIHigh, hIIIMiddle, hIIIHigh, hIICutoff, hIIILower,
        hIIIUpper]
  · have hb : ¬BONG.IsBinaryParameterAdmissible b := by
      exact fun hb => ha (hadmissible.mpr hb)
    simp [beliSpinorGroupRepresentative, ha, hb, hnorm]

/-- Beli (2003), Definition 4 on its exact quotient domain
`Kˣ / 𝓞ˣ²`. -/
noncomputable def beliSpinorGroup :
    UnitSquareClass K → Subgroup (SquareClass K) :=
  Quotient.lift (beliSpinorGroupRepresentative K) (by
    intro a b hab
    apply beliSpinorGroupRepresentative_eq_of_unitSquareClass_eq K
    exact Quotient.sound hab)

@[simp]
theorem beliSpinorGroup_unitSquareClass (a : Kˣ) :
    beliSpinorGroup K (unitSquareClass K a) =
      beliSpinorGroupRepresentative K a :=
  rfl

end Bong.Dyadic
