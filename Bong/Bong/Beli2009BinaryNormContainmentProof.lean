/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2009BinaryRemarks

/-!
# Binary norm-generator containment

The containment `g(a) ⊆ N(-a)` is not an additional local-field law.  A
binary BONG is an orthogonal basis, so every norm-generator value ratio is
literally a value of the norm form `x² + a y²`.  Combining this observation
with the already isolated binary value-ratio theorem proves the containment.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Every binary norm-generator value ratio is a norm from the quadratic
algebra with parameter the negative binary parameter. -/
theorem normGeneratorValueRatioUnit_isQuadraticNorm_binary
    (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    IsQuadraticNorm K (-b.binaryParameter)
      (b.normGeneratorValueRatioUnit y hy) := by
  let x₀ : K := b.basis.repr y 0
  let x₁ : K := b.basis.repr y 1
  have hyDecomposition :
      x₀ • b.ambientVector 0 + x₁ • b.ambientVector 1 = y := by
    have h := b.basis.sum_repr y
    rw [Fin.sum_univ_two] at h
    exact h
  have horthogonal :
      q.bilin (b.ambientVector 0) (b.ambientVector 1) = 0 := by
    apply (LinearMap.BilinForm.iIsOrtho_def.mp b.ambientVector_iIsOrtho)
    norm_num
  have hquadratic :
      q.quadratic y = x₀ ^ 2 * b.value 0 + x₁ ^ 2 * b.value 1 := by
    rw [← hyDecomposition, q.quadratic_add, q.quadratic_smul,
      q.quadratic_smul, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, horthogonal,
      b.quadratic_ambientVector, b.quadratic_ambientVector]
    ring
  refine ⟨x₀, x₁, ?_⟩
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, coe_valueUnit, Units.val_neg]
  rw [hquadratic, b.coe_binaryParameter]
  field_simp [b.value_ne_zero 0]
  ring

end BONG

/-- A principal-unit square class of depth complementary to the defect of
`a` lies in the norm group of `a`. -/
theorem principalUnitValuationClassSubgroup_le_quadraticNorm_of_defect_sum_gt
    [HilbertSymbolLaws K] (a : Kˣ) (n : Nat)
    (hsum : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K a + (n : ℕ∞)) :
    principalUnitValuationClassSubgroup K n ≤
      quadraticNormValuationClassSubgroup K a := by
  intro c hc
  rcases hc with ⟨u, hu, rfl⟩
  let uK : Kˣ := u.1
  change uK ∈ principalUnitSubgroup K n at hu
  have herror : (n : WithTop Int) ≤ ord K ((uK : K) - 1) :=
    (Lattice.mem_powerIdeal_iff (K := K) (n : Int) ((uK : K) - 1)).1 hu.2
  have happroximation : IsQuadraticApproximation K uK n := by
    refine ⟨1, ?_⟩
    have hnormalized :
        1 - (1 : K) ^ 2 / (uK : K) = ((uK : K) - 1) / (uK : K) := by
      field_simp [Units.ne_zero uK]
    rw [hnormalized, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hu.1]
    simpa using herror
  have hdefect : (n : ℕ∞) ≤ quadraticDefect K uK :=
    (isQuadraticApproximation_iff_le_defect K).1 happroximation
  have hsum' : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K a + quadraticDefect K uK :=
    hsum.trans_le (add_le_add (le_refl _) hdefect)
  have hnorm : IsQuadraticNorm K a uK :=
    (hilbertSymbol_eq_one_iff K a uK).1
      (hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
        (K := K) (a := a) (b := uK) hsum')
  change uK ∈ quadraticNormGroup K a at hnorm
  have hnormUnit : u ∈ quadraticNormUnitSubgroup K a := hnorm
  exact ⟨u, hnormUnit, rfl⟩

/-- In the high-defect branch of Definition 6, the principal-unit depth and
the parameter defect have sum strictly greater than `2e`. -/
theorem two_mul_e_lt_parameterDefect_add_highExponent
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    ((2 * ramificationIndex K : Nat) : ℕ∞) <
      beliParameterDefect K a + (beliHighDefectExponent K a : ℕ∞) := by
  by_cases htop : beliParameterDefect K a = ⊤
  · simpa only [htop, top_add] using
      (ENat.coe_lt_top (2 * ramificationIndex K))
  · obtain ⟨d, hdValue⟩ := WithTop.ne_top_iff_exists.mp htop
    have hdStrict : beliDefectCutoff K a < 2 * d := by
      have hstrictTop : (beliDefectCutoff K a : ℕ∞) <
          2 * beliParameterDefect K a := lt_of_not_ge hd
      rw [← hdValue] at hstrictTop
      exact_mod_cast WithTop.coe_lt_coe.mp hstrictTop
    have hcutoff : (beliDefectCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - ordUnit K a := by
      unfold beliDefectCutoff
      rw [Int.toNat_of_nonneg]
      omega
    have heven := beli2009BinaryHighDefect_even_order (K := K) a hd
    rcases heven with ⟨r, hr⟩
    have hlower := ha.ordUnit_ge_neg_two_mul_e
    have hexponent : (beliHighDefectExponent K a : Int) =
        (ramificationIndex K : Int) + ordUnit K a / 2 := by
      unfold beliHighDefectExponent
      rw [Int.toNat_of_nonneg]
      omega
    have hdStrictInt : (beliDefectCutoff K a : Int) < 2 * (d : Int) := by
      exact_mod_cast hdStrict
    have hgoal : 2 * (ramificationIndex K : Int) <
        (d : Int) + (beliHighDefectExponent K a : Int) := by
      omega
    rw [← hdValue]
    exact WithTop.coe_lt_coe.mpr (by exact_mod_cast hgoal)

/-- The cited containment `g(a) ⊆ N(-a)` is a consequence of the concrete
piecewise definition of `g(a)` and the Hilbert defect criterion. -/
noncomputable instance beli2009BinaryNormContainmentLawsProved
    [HilbertSymbolLaws K] :
    Beli2009BinaryNormContainmentLaws (K := K) where
  normGenerator_le_norm a ha := by
    by_cases hR : 2 * (ramificationIndex K : Int) < ordUnit K a
    · rw [beliNormGeneratorGroup_of_two_e_lt K a hR]
      exact bot_le
    · by_cases hd : 2 * beliParameterDefect K a ≤
          (beliDefectCutoff K a : ℕ∞)
      · rw [beliNormGeneratorGroup_of_low_defect K a hR hd]
        exact inf_le_right
      · rw [beliNormGeneratorGroup_of_high_defect K a hR hd]
        apply
          principalUnitValuationClassSubgroup_le_quadraticNorm_of_defect_sum_gt
        exact two_mul_e_lt_parameterDefect_add_highExponent a ha hR hd

end Bong
