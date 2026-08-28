/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup

/-!
# Beli's binary norm-generator group

This file formalizes Definition 6 of Beli (2003).  The order of `a` and the
relative quadratic defect `d(-a)` determine a piecewise subgroup `g(a)` of
`𝓞ˣ / 𝓞ˣ²`.

Integer-to-natural conversions make the definition total for every `a`.  On
the admissible parameter set, Beli's inequalities ensure that the displayed
exponents are nonnegative and the definition reduces to the original formulas.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The valuation-unit factor `ε` in `a = πᴿ ε`. -/
noncomputable def normalizedUnitPart (a : Kˣ) : Kˣ :=
  a * uniformizerPowerUnit K (-ordUnit K a)

/-- The normalized factor has valuation zero. -/
theorem normalizedUnitPart_isValuationUnit (a : Kˣ) :
    IsValuationUnit K (normalizedUnitPart K a : K) := by
  rw [isValuationUnit_iff_ordUnit_eq_zero, normalizedUnitPart,
    ordUnit_mul, ordUnit_uniformizerPowerUnit]
  omega

/-- Recovering the parameter from its order and normalized unit part. -/
theorem uniformizerPower_mul_normalizedUnitPart (a : Kˣ) :
    uniformizerPowerUnit K (ordUnit K a) * normalizedUnitPart K a = a := by
  rw [normalizedUnitPart]
  calc
    uniformizerPowerUnit K (ordUnit K a) *
          (a * uniformizerPowerUnit K (-ordUnit K a)) =
        a * (uniformizerPowerUnit K (ordUnit K a) *
          uniformizerPowerUnit K (-ordUnit K a)) := by
      ac_rfl
    _ = a := by simp [uniformizerPowerUnit]

/-- The relative quadratic defect `d(-a)` used in Beli's Definitions 4--6.
In particular, it is zero when `ord(a)` is odd; it agrees with `d(-ε)` for
an even-order presentation `a = πᴿ ε`. -/
noncomputable def beliParameterDefect (a : Kˣ) : ℕ∞ :=
  quadraticDefect K (-a)

/-- The finite part of `d(-a)`, used only in the low-defect branch. -/
noncomputable def beliParameterDefectNat (a : Kˣ) : Nat :=
  ENat.toNat (beliParameterDefect K a)

/-- Twice the cutoff `e - R/2`, expressed as the nonnegative natural number
`2e - R`. -/
noncomputable def beliDefectCutoff (a : Kˣ) : Nat :=
  Int.toNat (2 * (ramificationIndex K : Int) - ordUnit K a)

/-- The exponent `R + d` in Definition 6(ii). -/
noncomputable def beliLowDefectExponent (a : Kˣ) : Nat :=
  Int.toNat
    (ordUnit K a + (beliParameterDefectNat K a : Int))

/-- The exponent `R/2 + e` in Definition 6(iii). -/
noncomputable def beliHighDefectExponent (a : Kˣ) : Nat :=
  Int.toNat
    ((ramificationIndex K : Int) + ordUnit K a / 2)

/-- Beli (2003), Definition 6: the norm-generator value-ratio group `g(a)`. -/
noncomputable def beliNormGeneratorGroup (a : Kˣ) :
    Subgroup (ValuationUnitClass K) :=
  if 2 * (ramificationIndex K : Int) < ordUnit K a then
    ⊥
  else if 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) then
    principalUnitValuationClassSubgroup K
        (beliLowDefectExponent K a) ⊓
      quadraticNormValuationClassSubgroup K (-a)
  else
    principalUnitValuationClassSubgroup K
      (beliHighDefectExponent K a)

/-- Definition 6(I): `g(a) = 𝓞ˣ²` when `R > 2e`, hence the
trivial subgroup after quotienting by valuation-unit squares. -/
theorem beliNormGeneratorGroup_of_two_e_lt
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorGroup K a = ⊥ := by
  simp [beliNormGeneratorGroup, hR]

/-- Definition 6(II)(ii), using the doubled cutoff inequality. -/
theorem beliNormGeneratorGroup_of_low_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hdefect : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorGroup K a =
      principalUnitValuationClassSubgroup K
          (beliLowDefectExponent K a) ⊓
        quadraticNormValuationClassSubgroup K (-a) := by
  simp [beliNormGeneratorGroup, hR, hdefect]

/-- Definition 6(II)(iii), using the doubled cutoff inequality. -/
theorem beliNormGeneratorGroup_of_high_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hdefect : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorGroup K a =
      principalUnitValuationClassSubgroup K
        (beliHighDefectExponent K a) := by
  simp [beliNormGeneratorGroup, hR, hdefect]

end Bong.Dyadic
