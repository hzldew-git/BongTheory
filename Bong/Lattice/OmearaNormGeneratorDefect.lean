/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9327FundamentalIdeal
import Bong.Bong.DefectArithmetic

/-!
# Defect bounds for pairs of norm generators

O'Meara's square-coset description of a norm group shows that the product
of a norm generator with any norm-group value has absolute quadratic-defect
ideal contained in the generator times the weight ideal.  For two norm
generators of the same order, this gives the relative defect bound used in
the strict representation clauses of O'Meara 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- If `a` and `b` are norm generators of the same lattice and have the
same order, then `d(-a/b)` is at least `ord(wL) - ord(a)`.  The quotient
form is square-equivalent to the product `-ab`, to which the ideal-valued
weight estimate applies directly. -/
theorem weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
    (a b : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hb : IsNormGeneratorValue q L b)
    (horder : ordUnit K b = ordUnit K a) :
    ((((weightIdealOrder q L - ordUnit K a : Int) : ℚ) : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := K) (-(a / b))) := by
  have hbNeg : ((-b : Kˣ) : K) ∈ normGroupSet q L :=
    neg_mem_normGroupSet q L hb.1
  have hideal :=
    JordanDecomposition.quadraticDefectIdeal_mul_le_scalarIdeal_weight_of_mem_normGroup
      a (-b) ha hbNeg
  by_cases htop : quadraticDefect K (a * (-b)) = ⊤
  · have htop' : quadraticDefect K (-(a / b)) = ⊤ := by
      have hsquare := quadraticDefect_mul_square K (-(a / b)) b
      have hproduct : (-(a / b)) * b ^ 2 = a * (-b) := by
        apply Units.ext
        simp only [Units.val_neg, Units.val_div_eq_div_val,
          Units.val_mul, Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero a, Units.ne_zero b]
      rw [hproduct] at hsquare
      exact hsquare.symm.trans htop
    unfold BONG.GoodBONG.defectOrder
    rw [htop']
    exact le_top
  · rw [quadraticDefectIdeal, if_neg htop,
      weightIdeal_eq_powerIdeal, scalarIdeal_powerIdeal_units,
      powerIdeal_le_iff] at hideal
    have hdefectInt :
        weightIdealOrder q L - ordUnit K a ≤
          Int.ofNat (quadraticDefect K (a * (-b))).toNat := by
      rw [ordUnit_mul, ordUnit_neg, horder] at hideal
      omega
    have hdefectRat :
        ((weightIdealOrder q L - ordUnit K a : Int) : ℚ) ≤
          ((quadraticDefect K (a * (-b))).toNat : ℚ) := by
      exact_mod_cast hdefectInt
    have hfinite : quadraticDefect K (a * (-b)) =
        ((quadraticDefect K (a * (-b))).toNat : Nat) := by
      exact (ENat.coe_toNat htop).symm
    have hproduct : (-(a / b)) * b ^ 2 = a * (-b) := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_div_eq_div_val,
        Units.val_mul, Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero a, Units.ne_zero b]
    unfold BONG.GoodBONG.defectOrder
    rw [← quadraticDefect_mul_square K (-(a / b)) b, hproduct,
      hfinite]
    change ((((weightIdealOrder q L - ordUnit K a : Int) : ℚ) : WithTop ℚ) ≤
      ((((quadraticDefect K (a * (-b))).toNat : Nat) : ℚ) : WithTop ℚ))
    exact_mod_cast hdefectRat

end Lattice

end Bong
