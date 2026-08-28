/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorGroupInvariant

/-!
# Quotient form of Beli's auxiliary binary spinor group

This file proves representative invariance for Beli's `G'(a)`, descends its
formula to `Kˣ / 𝓞ˣ²`, and gives the quotient-level identity
`G(A) = ⟨A⟩ G'(A)` on the stated domain `R > 2e`.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The auxiliary representative formula is invariant under valuation-unit
squares. -/
theorem beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    beliAuxiliarySpinorGroupRepresentative K a =
      beliAuxiliarySpinorGroupRepresentative K b := by
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
  have hIICutoff : beliSpinorCaseIICutoff K a =
      beliSpinorCaseIICutoff K b := by
    unfold beliSpinorCaseIICutoff
    rw [horder]
  simp [beliAuxiliarySpinorGroupRepresentative, horder, hdefect,
    hnorm, hIILow, hIIHigh, hIICutoff]

/-- The cyclic subgroup attached intrinsically to a refined square class. -/
noncomputable def cyclicSquareClassSubgroupOnClass
    (A : UnitSquareClass K) : Subgroup (SquareClass K) :=
  Subgroup.zpowers (unitSquareClassToSquareClass K A)

@[simp]
theorem cyclicSquareClassSubgroupOnClass_unitSquareClass (a : Kˣ) :
    cyclicSquareClassSubgroupOnClass K (unitSquareClass K a) =
      cyclicSquareClassSubgroup K a :=
  rfl

/-- The representative formula for `G'` descended to the refined quotient. -/
noncomputable def beliAuxiliarySpinorGroupQuotient :
    UnitSquareClass K → Subgroup (SquareClass K) :=
  Quotient.lift (beliAuxiliarySpinorGroupRepresentative K) (by
    intro a b hab
    apply
      beliAuxiliarySpinorGroupRepresentative_eq_of_unitSquareClass_eq K
    exact Quotient.sound hab)

@[simp]
theorem beliAuxiliarySpinorGroupQuotient_unitSquareClass (a : Kˣ) :
    beliAuxiliarySpinorGroupQuotient K (unitSquareClass K a) =
      beliAuxiliarySpinorGroupRepresentative K a :=
  rfl

/-- Beli (2003), Definition 5 on its exact quotient domain `R > 2e`. -/
noncomputable def beliAuxiliarySpinorGroupClass
    (A : UnitSquareClass K)
    (_hR : 2 * (ramificationIndex K : Int) < unitSquareClassOrder K A) :
    Subgroup (SquareClass K) :=
  beliAuxiliarySpinorGroupQuotient K A

@[simp]
theorem beliAuxiliarySpinorGroupClass_unitSquareClass
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliAuxiliarySpinorGroupClass K (unitSquareClass K a)
        (by simpa using hR) =
      beliAuxiliarySpinorGroup K a hR :=
  rfl

/-- The quotient-level relation `G(A) = ⟨A⟩ G'(A)` following Definition 5. -/
theorem beliSpinorGroup_eq_cyclic_sup_auxiliaryClass
    (A : UnitSquareClass K)
    (hA : BONG.IsBinaryInvariantClassAdmissible A)
    (hquarter : A ≠ unitSquareClass K (negativeQuarterUnit K))
    (hR : 2 * (ramificationIndex K : Int) < unitSquareClassOrder K A) :
    beliSpinorGroup K A =
      cyclicSquareClassSubgroupOnClass K A ⊔
        beliAuxiliarySpinorGroupClass K A hR := by
  rcases hA with ⟨a, haClass, ha⟩
  subst A
  have hRrep : 2 * (ramificationIndex K : Int) < ordUnit K a := by
    simpa using hR
  simpa [beliAuxiliarySpinorGroupClass, beliAuxiliarySpinorGroup,
    cyclicSquareClassSubgroupOnClass, cyclicSquareClassSubgroup] using
      (beliSpinorGroupRepresentative_eq_cyclic_sup_auxiliary
        K a ha hquarter hRrep)

end Bong.Dyadic
