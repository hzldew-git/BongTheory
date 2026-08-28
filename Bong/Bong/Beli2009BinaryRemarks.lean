/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.BinaryNormGeneratorSquareClass

/-!
# Beli (2009/2010), Lemma 5.1 and Remark 5.2

This file rewrites the piecewise binary norm-generator group in terms of the
compact alpha cut.  It proves all three numeric branches, derives Lemma 5.1
from the cited containment `g(a) ≤ N(-a)`, and identifies the binary norm
parameter with the determinant parameter used in Remark 5.2.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The compact binary alpha formula from Section 5. -/
noncomputable def beli2009BinaryAlphaCut (a : Kˣ) : WithTop ℚ :=
  min
    ((((ordUnit K a : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
    ((((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
      BONG.GoodBONG.defectOrder (K := K) (-a))

/-- The principal-unit factor at the binary alpha cut.  A cut above `2e`
is represented by the bottom subgroup, since every such unit is a square. -/
noncomputable def beli2009BinaryAlphaCongruenceGroup (a : Kˣ) :
    Subgroup (ValuationUnitClass K) :=
  if 2 * (ramificationIndex K : Int) < ordUnit K a then
    ⊥
  else if 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞) then
    principalUnitValuationClassSubgroup K
      (beliLowDefectExponent K a)
  else
    principalUnitValuationClassSubgroup K
      (beliHighDefectExponent K a)

theorem beli2009BinaryAlphaCongruenceGroup_of_two_e_lt
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    beli2009BinaryAlphaCongruenceGroup (K := K) a = ⊥ := by
  simp [beli2009BinaryAlphaCongruenceGroup, hR]

theorem beli2009BinaryAlphaCongruenceGroup_of_low_defect
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCongruenceGroup (K := K) a =
      principalUnitValuationClassSubgroup K
        (beliLowDefectExponent K a) := by
  simp [beli2009BinaryAlphaCongruenceGroup, hR, hd]

theorem beli2009BinaryAlphaCongruenceGroup_of_high_defect
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCongruenceGroup (K := K) a =
      principalUnitValuationClassSubgroup K
        (beliHighDefectExponent K a) := by
  simp [beli2009BinaryAlphaCongruenceGroup, hR, hd]

theorem beli2009BinaryHighDefect_even_order
    (a : Kˣ) (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    Even (ordUnit K a) := by
  rcases Int.even_or_odd (ordUnit K a) with heven | hodd
  · exact heven
  · exfalso
    apply hd
    have hordNeg : ordUnit K (-a) = ordUnit K a := by
      apply WithTop.coe_injective
      rw [coe_ordUnit K (-a), coe_ordUnit K a]
      simpa only [Units.val_neg] using ord_neg K (a : K)
    have hoddNeg : Odd (ordUnit K (-a)) := by
      rwa [hordNeg]
    have hzero : beliParameterDefect K a = 0 := by
      exact quadraticDefect_eq_zero_of_odd_ordUnit
        (K := K) (-a) hoddNeg
    rw [hzero]
    simp

theorem beli2009BinaryAlphaCut_gt_two_mul_e_of_two_e_lt
    (a : Kˣ) (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      beli2009BinaryAlphaCut (K := K) a := by
  unfold beli2009BinaryAlphaCut
  rw [lt_min_iff]
  constructor
  · norm_cast
    push_cast
    have hRq :
        (2 * (ramificationIndex K : Int) : ℚ) <
          (ordUnit K a : ℚ) := by
      exact_mod_cast hR
    rw [Rat.divInt_eq_div]
    norm_num [div_eq_mul_inv] at hRq ⊢
    linarith
  · have hd : (0 : WithTop ℚ) ≤
        BONG.GoodBONG.defectOrder (K := K) (-a) := by
      by_cases htop : quadraticDefect K (-a) = ⊤
      · rw [show BONG.GoodBONG.defectOrder (K := K) (-a) = ⊤ by
          unfold BONG.GoodBONG.defectOrder
          rw [htop]
          rfl]
        exact le_top
      · rw [show BONG.GoodBONG.defectOrder (K := K) (-a) =
            (((quadraticDefect K (-a)).toNat : ℚ) : WithTop ℚ) by
          unfold BONG.GoodBONG.defectOrder
          rw [← ENat.coe_toNat htop]
          rfl]
        norm_cast
        positivity
    have horder :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (((ordUnit K a : Int) : ℚ) : WithTop ℚ) := by
      exact_mod_cast hR
    have hle : (((ordUnit K a : Int) : ℚ) : WithTop ℚ) ≤
        (((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
          BONG.GoodBONG.defectOrder (K := K) (-a) := by
      simpa [add_comm] using add_le_add_right hd
        ((((ordUnit K a : Int) : ℚ) : WithTop ℚ))
    exact horder.trans_le hle

theorem beli2009BinaryLowCandidate_le_halfCandidate
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    ((((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) (-a)) ≤
      (((((ordUnit K a : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  have hdNat := hd
  rw [← ENat.coe_toNat hfinite] at hdNat
  norm_cast at hdNat
  have hcutoff : (beliDefectCutoff K a : Int) =
      2 * (ramificationIndex K : Int) - ordUnit K a := by
    unfold beliDefectCutoff
    rw [Int.toNat_of_nonneg]
    omega
  have hdInt : 2 * (beliParameterDefectNat K a : Int) ≤
      2 * (ramificationIndex K : Int) - ordUnit K a := by
    rw [← hcutoff]
    exact_mod_cast hdNat
  have hdefectOrder :
      BONG.GoodBONG.defectOrder (K := K) (-a) =
        (((beliParameterDefectNat K a : Nat) : ℚ) : WithTop ℚ) := by
    have hfinite' : quadraticDefect K (-a) ≠ ⊤ := by
      simpa [beliParameterDefect] using hfinite
    unfold BONG.GoodBONG.defectOrder beliParameterDefectNat
      beliParameterDefect
    rw [← ENat.coe_toNat hfinite']
    rfl
  have hdQ :
      (2 * (beliParameterDefectNat K a : Int) : ℚ) ≤
        (2 * (ramificationIndex K : Int) - ordUnit K a : ℚ) := by
    exact_mod_cast hdInt
  rw [hdefectOrder]
  norm_cast
  rw [Rat.divInt_eq_div]
  push_cast at hdQ ⊢
  norm_num [div_eq_mul_inv] at hdQ ⊢
  linarith

theorem beli2009BinaryAlphaCut_eq_lowCandidate
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCut (K := K) a =
      (((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) (-a) := by
  unfold beli2009BinaryAlphaCut
  rw [min_eq_right]
  exact beli2009BinaryLowCandidate_le_halfCandidate
    (K := K) a hR hd

/-- The finite-defect part of binary admissibility gives `R + d ≥ 0`. -/
theorem beli2009_order_add_parameterDefect_nonneg
    {a : Kˣ} (ha : BONG.IsBinaryParameterAdmissible a)
    (hfinite : beliParameterDefect K a ≠ ⊤) :
    0 ≤ ordUnit K a + ((beliParameterDefect K a).toNat : Int) := by
  have habsolute : HasNonnegativeAbsoluteQuadraticDefect (-a) := by
    rw [hasNonnegativeAbsoluteQuadraticDefect_iff_exists_sub_sq_mem]
    rcases ha with ⟨c, _htwo, hdiag⟩
    refine ⟨c, ?_⟩
    have heq : (((-a : Kˣ) : K) - c ^ 2) =
        -(c ^ 2 + (a : K)) := by
      simp only [Units.val_neg]
      ring
    rw [heq]
    exact (IntegerRing K).neg_mem _ hdiag
  have hthreshold :=
    (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le
      (K := K) (-a)).1 habsolute
  have hfiniteDefect : quadraticDefect K (-a) ≠ ⊤ := by
    simpa [beliParameterDefect] using hfinite
  have horderNeg : ordUnit K (-a) = ordUnit K a := by
    apply WithTop.coe_injective
    rw [coe_ordUnit K (-a), coe_ordUnit K a]
    simpa only [Units.val_neg] using ord_neg K (a : K)
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

theorem beli2009BinaryAlphaCut_eq_lowExponent
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : 2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCut (K := K) a =
      (((beliLowDefectExponent K a : Nat) : ℚ) : WithTop ℚ) := by
  have hfinite : beliParameterDefect K a ≠ ⊤ := by
    intro htop
    rw [htop] at hd
    simp at hd
  have hnonneg := beli2009_order_add_parameterDefect_nonneg
    (K := K) ha hfinite
  have hcast : (beliLowDefectExponent K a : Int) =
      ordUnit K a + (beliParameterDefectNat K a : Int) := by
    unfold beliLowDefectExponent beliParameterDefectNat
    rw [Int.toNat_of_nonneg hnonneg]
  have hdefectOrder :
      BONG.GoodBONG.defectOrder (K := K) (-a) =
        (((beliParameterDefectNat K a : Nat) : ℚ) : WithTop ℚ) := by
    have hfinite' : quadraticDefect K (-a) ≠ ⊤ := by
      simpa [beliParameterDefect] using hfinite
    unfold BONG.GoodBONG.defectOrder beliParameterDefectNat
      beliParameterDefect
    rw [← ENat.coe_toNat hfinite']
    rfl
  rw [beli2009BinaryAlphaCut_eq_lowCandidate (K := K) a hR hd,
    hdefectOrder]
  norm_cast
  exact_mod_cast hcast.symm

theorem beli2009BinaryHalfCandidate_lt_lowCandidate
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    (((((ordUnit K a : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) <
      (((ordUnit K a : Int) : ℚ) : WithTop ℚ) +
        BONG.GoodBONG.defectOrder (K := K) (-a) := by
  by_cases htop : beliParameterDefect K a = ⊤
  · have hdefectOrder :
        BONG.GoodBONG.defectOrder (K := K) (-a) = ⊤ := by
      have htop' : quadraticDefect K (-a) = ⊤ := by
        simpa [beliParameterDefect] using htop
      unfold BONG.GoodBONG.defectOrder
      rw [htop']
      rfl
    rw [hdefectOrder]
    simp
  · have hdStrict : (beliDefectCutoff K a : ℕ∞) <
        2 * beliParameterDefect K a := lt_of_not_ge hd
    rw [← ENat.coe_toNat htop] at hdStrict
    norm_cast at hdStrict
    have hcutoff : (beliDefectCutoff K a : Int) =
        2 * (ramificationIndex K : Int) - ordUnit K a := by
      unfold beliDefectCutoff
      rw [Int.toNat_of_nonneg]
      omega
    have hdInt :
        2 * (ramificationIndex K : Int) - ordUnit K a <
          2 * (beliParameterDefectNat K a : Int) := by
      rw [← hcutoff]
      exact_mod_cast hdStrict
    have hdefectOrder :
        BONG.GoodBONG.defectOrder (K := K) (-a) =
          (((beliParameterDefectNat K a : Nat) : ℚ) : WithTop ℚ) := by
      have hfinite' : quadraticDefect K (-a) ≠ ⊤ := by
        simpa [beliParameterDefect] using htop
      unfold BONG.GoodBONG.defectOrder beliParameterDefectNat
        beliParameterDefect
      rw [← ENat.coe_toNat hfinite']
      rfl
    have hdQ :
        (2 * (ramificationIndex K : Int) - ordUnit K a : ℚ) <
          (2 * (beliParameterDefectNat K a : Int) : ℚ) := by
      exact_mod_cast hdInt
    rw [hdefectOrder]
    norm_cast
    rw [Rat.divInt_eq_div]
    push_cast at hdQ ⊢
    norm_num [div_eq_mul_inv] at hdQ ⊢
    linarith

theorem beli2009BinaryAlphaCut_eq_halfCandidate
    (a : Kˣ) (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCut (K := K) a =
      (((((ordUnit K a : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
  unfold beli2009BinaryAlphaCut
  rw [min_eq_left]
  exact (beli2009BinaryHalfCandidate_lt_lowCandidate
    (K := K) a hR hd).le

theorem beli2009BinaryAlphaCut_eq_highExponent
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a)
    (hd : ¬2 * beliParameterDefect K a ≤
      (beliDefectCutoff K a : ℕ∞)) :
    beli2009BinaryAlphaCut (K := K) a =
      (((beliHighDefectExponent K a : Nat) : ℚ) : WithTop ℚ) := by
  rw [beli2009BinaryAlphaCut_eq_halfCandidate (K := K) a hR hd]
  have heven := beli2009BinaryHighDefect_even_order (K := K) a hd
  rcases heven with ⟨r, hr⟩
  have hlower := ha.ordUnit_ge_neg_two_mul_e
  have hnonneg : 0 ≤
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
    omega
  have hcast : (beliHighDefectExponent K a : Int) =
      (ramificationIndex K : Int) + ordUnit K a / 2 := by
    unfold beliHighDefectExponent
    rw [Int.toNat_of_nonneg hnonneg]
  norm_cast
  calc
    Rat.divInt (ordUnit K a) 2 + (ramificationIndex K : ℚ) =
        (((ramificationIndex K : Int) + ordUnit K a / 2 : Int) : ℚ) := by
      rw [Rat.divInt_eq_div]
      push_cast
      norm_num [div_eq_mul_inv]
      have hhalf : ordUnit K a / 2 = r := by omega
      rw [hhalf, hr]
      push_cast
      ring
    _ = (beliHighDefectExponent K a : ℚ) := by
      exact_mod_cast hcast.symm

/-- The three branches of the principal-unit factor are exactly the three
numeric branches of the compact alpha formula. -/
theorem beli2009BinaryAlphaCongruenceGroup_spec
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    (∀ _hR : 2 * (ramificationIndex K : Int) < ordUnit K a,
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
            beli2009BinaryAlphaCut (K := K) a ∧
          beli2009BinaryAlphaCongruenceGroup (K := K) a = ⊥) ∧
      (∀ _hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a,
        ∀ _hd : 2 * beliParameterDefect K a ≤
            (beliDefectCutoff K a : ℕ∞),
          beli2009BinaryAlphaCut (K := K) a =
              (((beliLowDefectExponent K a : Nat) : ℚ) : WithTop ℚ) ∧
            beli2009BinaryAlphaCongruenceGroup (K := K) a =
              principalUnitValuationClassSubgroup K
                (beliLowDefectExponent K a)) ∧
      (∀ _hR : ¬2 * (ramificationIndex K : Int) < ordUnit K a,
        ∀ _hd : ¬2 * beliParameterDefect K a ≤
            (beliDefectCutoff K a : ℕ∞),
          beli2009BinaryAlphaCut (K := K) a =
              (((beliHighDefectExponent K a : Nat) : ℚ) : WithTop ℚ) ∧
            beli2009BinaryAlphaCongruenceGroup (K := K) a =
              principalUnitValuationClassSubgroup K
                (beliHighDefectExponent K a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hR
    exact ⟨beli2009BinaryAlphaCut_gt_two_mul_e_of_two_e_lt
      (K := K) a hR,
      beli2009BinaryAlphaCongruenceGroup_of_two_e_lt
        (K := K) a hR⟩
  · intro hR hd
    exact ⟨beli2009BinaryAlphaCut_eq_lowExponent
      (K := K) a ha hR hd,
      beli2009BinaryAlphaCongruenceGroup_of_low_defect
        (K := K) a hR hd⟩
  · intro hR hd
    exact ⟨beli2009BinaryAlphaCut_eq_highExponent
      (K := K) a ha hR hd,
      beli2009BinaryAlphaCongruenceGroup_of_high_defect
        (K := K) a hR hd⟩

/-- A finite rational lower bound on the embedded defect order reflects back
to the corresponding lower bound on the underlying `ℕ∞`-valued defect. -/
private theorem natCast_le_quadraticDefect_of_le_defectOrder
    (u : Kˣ) (n : Nat)
    (hdefect : (((n : Nat) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) u) :
    (n : ℕ∞) ≤ quadraticDefect K u := by
  unfold BONG.GoodBONG.defectOrder at hdefect
  cases hraw : quadraticDefect K u with
  | top => simp
  | coe m =>
      rw [hraw] at hdefect
      change (((n : Nat) : ℚ) : WithTop ℚ) ≤
        (((m : Nat) : ℚ) : WithTop ℚ) at hdefect
      exact_mod_cast hdefect

/-- The alpha lower bound places a valuation unit in the principal-unit
factor of Beli's binary norm-generator group.  This is the local conversion
used in the equal-norm rank-two case of the 2019 representation theorem. -/
theorem valuationUnitClassHom_mem_beli2009BinaryAlphaCongruenceGroup
    [QuadraticDefectLaws K]
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a)
    (u : valuationUnitSubgroup K)
    (hdefect : beli2009BinaryAlphaCut (K := K) a ≤
      BONG.GoodBONG.defectOrder (K := K) (u : Kˣ)) :
    valuationUnitClassHom K u ∈
      beli2009BinaryAlphaCongruenceGroup (K := K) a := by
  have hspec := beli2009BinaryAlphaCongruenceGroup_spec
    (K := K) a ha
  by_cases hR : 2 * (ramificationIndex K : Int) < ordUnit K a
  · have hbranch := hspec.1 hR
    have huSquare : IsSquare (u : Kˣ) :=
      BONG.GoodBONG.isSquare_of_two_mul_e_lt_defectOrder
        (K := K) (u : Kˣ) (hbranch.1.trans_le hdefect)
    have huClass : valuationUnitClassHom K u = 1 := by
      apply valuationUnitClassToSquareClass_injective K
      change squareClass K (u : Kˣ) = squareClass K 1
      rcases huSquare with ⟨s, hs⟩
      rw [hs]
      simpa [pow_two] using
        squareClass_mul_square K (1 : Kˣ) s
    rw [hbranch.2]
    simpa [huClass]
  · by_cases hd : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · have hbranch := hspec.2.1 hR hd
      rw [hbranch.2]
      apply
        valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
      apply natCast_le_quadraticDefect_of_le_defectOrder
      rw [← hbranch.1]
      exact hdefect
    · have hbranch := hspec.2.2 hR hd
      rw [hbranch.2]
      apply
        valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
      apply natCast_le_quadraticDefect_of_le_defectOrder
      rw [← hbranch.1]
      exact hdefect

/-- The cited containment `g(a) ⊆ N(-a)` from Beli (2003), paragraph 3.16.
It is kept separate from the Section 5 argument and has no default instance. -/
class Beli2009BinaryNormContainmentLaws : Prop where
  normGenerator_le_norm (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliNormGeneratorGroup K a ≤
      quadraticNormValuationClassSubgroup K (-a)

/-- Quadratic norm subgroups are unchanged when their parameter is
multiplied by a square. -/
theorem quadraticNormValuationClassSubgroup_mul_square
    (a s : Kˣ) :
    quadraticNormValuationClassSubgroup K (a * s ^ 2) =
      quadraticNormValuationClassSubgroup K a := by
  have hgroup : quadraticNormGroup K (a * s ^ 2) =
      quadraticNormGroup K a := by
    ext b
    exact isQuadraticNorm_mul_square_left_iff K a b s
  simp [quadraticNormValuationClassSubgroup,
    quadraticNormUnitSubgroup, hgroup]

/-- Beli (2009/2010), Lemma 5.1, in the unit-square-class quotient. -/
theorem beli2009Lemma51 [Beli2009BinaryNormContainmentLaws (K := K)]
    (a : Kˣ) (ha : BONG.IsBinaryParameterAdmissible a) :
    beliNormGeneratorGroup K a =
      beli2009BinaryAlphaCongruenceGroup (K := K) a ⊓
        quadraticNormValuationClassSubgroup K (-a) := by
  by_cases hR : 2 * (ramificationIndex K : Int) < ordUnit K a
  · rw [beliNormGeneratorGroup_of_two_e_lt K a hR,
      beli2009BinaryAlphaCongruenceGroup_of_two_e_lt (K := K) a hR]
    simp
  · by_cases hd : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞)
    · rw [beliNormGeneratorGroup_of_low_defect K a hR hd,
        beli2009BinaryAlphaCongruenceGroup_of_low_defect (K := K) a hR hd]
    · rw [beliNormGeneratorGroup_of_high_defect K a hR hd,
        beli2009BinaryAlphaCongruenceGroup_of_high_defect (K := K) a hR hd]
      apply (inf_eq_left.mpr _).symm
      rw [← beliNormGeneratorGroup_of_high_defect K a hR hd]
      exact Beli2009BinaryNormContainmentLaws.normGenerator_le_norm a ha

namespace BONG.GoodBONG

theorem binary_alpha_eq_min_candidates (b : GoodBONG q L 2) :
    (b.alphaValue 0 : WithTop ℚ) =
      min (b.halfGapCandidate 0) (b.leftDefectCandidate 0 0) := by
  rw [b.coe_alphaValue]
  unfold alpha alphaCandidates
  simp [leftDefectCandidate, rightDefectCandidate]

theorem binaryParameter_orderGap (b : GoodBONG q L 2) :
    ordUnit K b.toBONG.binaryParameter = b.orderGap 0 := by
  change ordUnit K b.toBONG.binaryParameter =
    b.toBONG.order 1 - b.toBONG.order 0
  exact b.toBONG.binaryParameterOrder_eq_orderGap

theorem binary_adjacentProduct_eq_parameter_mul_square
    (b : GoodBONG q L 2) :
    b.adjacentProduct 0 =
      (-b.toBONG.binaryParameter) * b.valueUnit 0 ^ 2 := by
  unfold adjacentProduct BONG.binaryParameter
  change -(b.toBONG.valueUnit 0 * b.toBONG.valueUnit 1) =
    -(b.toBONG.valueUnit 1 / b.toBONG.valueUnit 0) *
      b.toBONG.valueUnit 0 ^ 2
  rw [neg_mul]
  congr 1
  simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]

theorem binary_adjacentDefect_eq_parameterDefect
    (b : GoodBONG q L 2) :
    b.adjacentDefect 0 = defectOrder (K := K) (-b.toBONG.binaryParameter) := by
  unfold adjacentDefect
  rw [b.binary_adjacentProduct_eq_parameter_mul_square,
    defectOrder_mul_square]

/-- The binary equality `alpha(a₂/a₁) = alpha₁`. -/
theorem binaryAlphaCut_parameter_eq (b : GoodBONG q L 2) :
    beli2009BinaryAlphaCut (K := K) b.toBONG.binaryParameter =
      (b.alphaValue 0 : WithTop ℚ) := by
  rw [b.binary_alpha_eq_min_candidates]
  unfold beli2009BinaryAlphaCut halfGapCandidate leftDefectCandidate
  rw [b.binary_adjacentDefect_eq_parameterDefect,
    b.binaryParameter_orderGap]
  rfl

theorem binaryParameter_normGroup_eq_adjacentNorm
    (b : GoodBONG q L 2) :
    quadraticNormValuationClassSubgroup K (-b.toBONG.binaryParameter) =
      quadraticNormValuationClassSubgroup K (b.adjacentProduct 0) := by
  rw [b.binary_adjacentProduct_eq_parameter_mul_square]
  exact
    (quadraticNormValuationClassSubgroup_mul_square (K := K)
      (-b.toBONG.binaryParameter) (b.valueUnit 0)).symm

theorem binaryParameter_normGroup_eq_determinantNorm
    (b : GoodBONG q L 2) :
    quadraticNormValuationClassSubgroup K (-b.toBONG.binaryParameter) =
      quadraticNormValuationClassSubgroup K
        (-(b.valueUnit 0 * b.valueUnit 1)) := by
  rw [b.binaryParameter_normGroup_eq_adjacentNorm]
  rfl

/-- Beli (2009/2010), Remark 5.2. -/
theorem beli2009Remark52
    [Beli2009BinaryNormContainmentLaws (K := K)]
    (b : GoodBONG q L 2) :
    beli2009BinaryAlphaCut (K := K) b.toBONG.binaryParameter =
        (b.alphaValue 0 : WithTop ℚ) ∧
      beliNormGeneratorGroup K b.toBONG.binaryParameter =
        beli2009BinaryAlphaCongruenceGroup (K := K)
            b.toBONG.binaryParameter ⊓
          quadraticNormValuationClassSubgroup K
            (-(b.valueUnit 0 * b.valueUnit 1)) := by
  constructor
  · exact b.binaryAlphaCut_parameter_eq
  · rw [beli2009Lemma51 (K := K) b.toBONG.binaryParameter
        b.toBONG.binaryParameter_isBinaryParameterAdmissible,
      b.binaryParameter_normGroup_eq_determinantNorm]

end BONG.GoodBONG

end Bong
