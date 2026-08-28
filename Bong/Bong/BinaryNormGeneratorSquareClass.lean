/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorGroup

/-!
# Binary norm-generator groups in field square classes

Beli (2003), Lemma 3.16, compares the unit-square-class group `g(a)` with the
spinor-norm group `G(a)`, which lives in the ordinary field square-class
group.  This file supplies the canonical change of quotient needed to state
that comparison without identifying the two quotient groups.
-/

namespace Bong

open Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli's norm-generator group `g(a)`, mapped from
`𝓞ˣ / 𝓞ˣ²` into `Kˣ / Kˣ²`. -/
noncomputable def beliNormGeneratorSquareClassGroup (a : Kˣ) :
    Subgroup (SquareClass K) :=
  Dyadic.valuationUnitClassSubgroupSquareImage K
    (beliNormGeneratorGroup K a)

theorem valuationUnitClassToSquareClass_mem_beliNormGeneratorGroup
    {a : Kˣ} {c : ValuationUnitClass K}
    (hc : c ∈ beliNormGeneratorGroup K a) :
    valuationUnitClassToSquareClass K c ∈
      beliNormGeneratorSquareClassGroup K a :=
  valuationUnitClassToSquareClass_mem_image K hc

/-- Definition 6(I), after embedding unit square classes into field square
classes. -/
theorem beliNormGeneratorSquareClassGroup_of_two_e_lt
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beliNormGeneratorSquareClassGroup K a = ⊥ := by
  rw [beliNormGeneratorSquareClassGroup,
    beliNormGeneratorGroup_of_two_e_lt K a hR]
  exact valuationUnitClassSubgroupSquareImage_bot K

/-- Definition 6(II)(ii), after embedding into field square classes. -/
theorem beliNormGeneratorSquareClassGroup_of_low_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hdefect : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K a =
      principalUnitSquareClassSubgroup K
          (beliLowDefectExponent K a) ⊓
        quadraticNormSquareClassSubgroup K (-a) := by
  rw [beliNormGeneratorSquareClassGroup,
    beliNormGeneratorGroup_of_low_defect K a hR hdefect]
  exact
    valuationUnitClassSubgroupSquareImage_principalUnit_inf_norm
      K (beliLowDefectExponent K a) (-a)

/-- Definition 6(II)(iii), after embedding into field square classes. -/
theorem beliNormGeneratorSquareClassGroup_of_high_defect
    (a : Kˣ)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hdefect : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beliNormGeneratorSquareClassGroup K a =
      principalUnitSquareClassSubgroup K
        (beliHighDefectExponent K a) := by
  rw [beliNormGeneratorSquareClassGroup,
    beliNormGeneratorGroup_of_high_defect K a hR hdefect]
  exact valuationUnitClassSubgroupSquareImage_principalUnit K
    (beliHighDefectExponent K a)

/-- The containment in the remark after Beli (2003), Lemma 3.11.  Notice
that the norm-generator group is contained in the depth-`R` principal-unit
group; this is the direction used in Lemma 3.13(i). -/
theorem beliNormGeneratorSquareClassGroup_le_principalUnitSquareClassSubgroup
    (a : Kˣ) (hR : 0 < ordUnit K a) :
    beliNormGeneratorSquareClassGroup K a ≤
      principalUnitSquareClassSubgroup K (Int.toNat (ordUnit K a)) := by
  by_cases hhigh :
      2 * (ramificationIndex K : Int) < ordUnit K a
  · rw [beliNormGeneratorSquareClassGroup_of_two_e_lt K a hhigh]
    exact bot_le
  · by_cases hdefect : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · rw [beliNormGeneratorSquareClassGroup_of_low_defect
        K a hhigh hdefect]
      exact inf_le_left.trans (principalUnitSquareClassSubgroup_anti K (by
        unfold beliLowDefectExponent
        apply Int.toNat_le_toNat
        omega))
    · rw [beliNormGeneratorSquareClassGroup_of_high_defect
        K a hhigh hdefect]
      apply principalUnitSquareClassSubgroup_anti K
      unfold beliHighDefectExponent
      apply Int.toNat_le_toNat
      have hRupper : ordUnit K a ≤
          2 * (ramificationIndex K : Int) := le_of_not_gt hhigh
      omega

@[simp]
theorem mem_beliNormGeneratorSquareClassGroup_iff
    {a : Kˣ} {z : SquareClass K} :
    z ∈ beliNormGeneratorSquareClassGroup K a ↔
      ∃ c : ValuationUnitClass K,
        c ∈ beliNormGeneratorGroup K a ∧
          valuationUnitClassToSquareClass K c = z :=
  Iff.rfl

end Bong
