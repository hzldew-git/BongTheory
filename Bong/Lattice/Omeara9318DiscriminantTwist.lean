/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiscriminantClassProof
import Bong.Dyadic.QuadraticDefectHensel

/-!
# The discriminant twist in O'Meara 93:18(iii)

Put `d = 1 + alpha` and `Delta = 1 - 4 rho`.  When `alpha` is in the
maximal ideal, the quotient

`((d - 4 rho) * Delta) / d`

is a principal unit strictly deeper than `2e`, hence a square.  This is the
precise Hensel argument behind the phrase "it is easily checked" in the
rank-four calculation.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

private theorem valuationUnit_ne_zero {x : K}
    (hx : IsValuationUnit K x) : x ≠ 0 := by
  intro hzero
  rw [hzero, IsValuationUnit, ord_zero] at hx
  exact WithTop.top_ne_coe hx

/-- Unit packaging of `1 + alpha`. -/
noncomputable def omeara9318DiscriminantUnit (alpha : K)
    (hunit : IsValuationUnit K (1 + alpha)) : Kˣ :=
  Units.mk0 (1 + alpha) (valuationUnit_ne_zero hunit)

@[simp]
theorem coe_omeara9318DiscriminantUnit
    (alpha : K) (hunit : IsValuationUnit K (1 + alpha)) :
    (omeara9318DiscriminantUnit alpha hunit : K) = 1 + alpha :=
  rfl

/-- Unit packaging of `1 + alpha - 4 rho`. -/
noncomputable def omeara9318ShiftedDiscriminantUnit (alpha : K)
    (hunit : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) : Kˣ :=
  Units.mk0 (1 + alpha - 4 * laws.rho)
    (valuationUnit_ne_zero hunit)

@[simp]
theorem coe_omeara9318ShiftedDiscriminantUnit
    (alpha : K)
    (hunit : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) :
    (omeara9318ShiftedDiscriminantUnit alpha hunit : K) =
      1 + alpha - 4 * laws.rho :=
  rfl

/-- The discriminant ratio whose square class compares the two printed
rank-four models. -/
noncomputable def omeara9318DiscriminantRatio
    (alpha : K)
    (hd : IsValuationUnit K (1 + alpha))
    (hshift : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) : Kˣ :=
  omeara9318ShiftedDiscriminantUnit alpha hshift *
    laws.discriminantUnit /
      omeara9318DiscriminantUnit alpha hd

private theorem ord_four_mul_rho :
    ord K ((4 : K) * laws.rho) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
  rw [show (4 : K) * laws.rho =
      (2 : K) * (2 : K) * laws.rho by ring,
    ord_mul, ord_mul, ← ramificationIndex_spec,
    laws.rho_isValuationUnit]
  norm_cast
  omega

/-- If `alpha` is nonprincipal modulo the maximal ideal, the auxiliary sum
`(1+alpha) + Delta` is itself in the maximal ideal. -/
theorem omeara9318_discriminant_add_delta_isInMaximalIdeal
    (alpha : K) (halpha : IsInMaximalIdeal K alpha) :
    IsInMaximalIdeal K
      ((1 + alpha) + (laws.discriminantUnit : K)) := by
  have hfourRhoIntegral : (2 : K) * laws.rho ∈ IntegerRing K := by
    exact (IntegerRing K).toSubring.mul_mem (by norm_num)
      ((mem_integerRing_iff K).2 laws.rho_isValuationUnit.ge)
  have hfourRhoMax : IsInMaximalIdeal K ((4 : K) * laws.rho) := by
    have h := isInMaximalIdeal_mul_isIntegral K
      (two_isInMaximalIdeal K)
      ((mem_integerRing_iff K).1 hfourRhoIntegral)
    convert h using 1 <;> ring
  rw [laws.discriminant_eq_one_sub_four_mul_rho]
  have htwoAlpha : IsInMaximalIdeal K ((2 : K) + alpha) :=
    isInMaximalIdeal_add K (two_isInMaximalIdeal K) halpha
  have hminusFour : IsInMaximalIdeal K (-((4 : K) * laws.rho)) := by
    rw [IsInMaximalIdeal, ord_neg]
    exact hfourRhoMax
  convert isInMaximalIdeal_add K htwoAlpha hminusFour using 1 <;> ring

/-- The discriminant ratio differs from one by the explicit deep error
`-4 rho (d + Delta) / d`. -/
theorem omeara9318DiscriminantRatio_sub_one
    (alpha : K)
    (hd : IsValuationUnit K (1 + alpha))
    (hshift : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) :
    (omeara9318DiscriminantRatio alpha hd hshift : K) - 1 =
      -((4 : K) * laws.rho) *
        ((1 + alpha) + (laws.discriminantUnit : K)) /
          (1 + alpha) := by
  simp only [omeara9318DiscriminantRatio,
    Units.val_div_eq_div_val, Units.val_mul,
    coe_omeara9318ShiftedDiscriminantUnit,
    coe_omeara9318DiscriminantUnit]
  change
    ((1 + alpha - 4 * laws.rho) *
          (laws.discriminantUnit : K) / (1 + alpha)) - 1 = _
  rw [laws.discriminant_eq_one_sub_four_mul_rho]
  field_simp [valuationUnit_ne_zero hd]
  ring

/-- Hensel square relation for the discriminant twist. -/
theorem omeara9318DiscriminantRatio_isSquare
    (alpha : K)
    (halpha : IsInMaximalIdeal K alpha)
    (hd : IsValuationUnit K (1 + alpha))
    (hshift : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) :
    IsSquare (omeara9318DiscriminantRatio alpha hd hshift) := by
  apply isSquare_of_ord_sub_one_gt_two_mul_e K
    (omeara9318DiscriminantRatio alpha hd hshift)
  rw [omeara9318DiscriminantRatio_sub_one]
  have hsumPos : 0 < ord K
      ((1 + alpha) + (laws.discriminantUnit : K)) :=
    omeara9318_discriminant_add_delta_isInMaximalIdeal alpha halpha
  rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, hd,
    ord_mul, ord_neg, ord_four_mul_rho]
  have hadd :
      ((((2 * ramificationIndex K : Nat) : Int) : WithTop Int)) + 0 <
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) +
          ord K ((1 + alpha) + (laws.discriminantUnit : K)) :=
    WithTop.add_lt_add_left (by exact WithTop.coe_ne_top) hsumPos
  simpa only [add_zero, add_assoc, neg_zero] using hadd

/-- Multiplicative determinant-square form of the preceding ratio. -/
theorem omeara9318Discriminants_sameSquareClass
    (alpha : K)
    (halpha : IsInMaximalIdeal K alpha)
    (hd : IsValuationUnit K (1 + alpha))
    (hshift : IsValuationUnit K
      (1 + alpha - 4 * laws.rho)) :
    IsSquare
      (omeara9318ShiftedDiscriminantUnit alpha hshift *
        laws.discriminantUnit *
          omeara9318DiscriminantUnit alpha hd) := by
  let d := omeara9318DiscriminantUnit alpha hd
  let e := omeara9318ShiftedDiscriminantUnit alpha hshift
  have hratio : IsSquare (e * laws.discriminantUnit / d) := by
    simpa only [omeara9318DiscriminantRatio, e, d] using
      omeara9318DiscriminantRatio_isSquare alpha halpha hd hshift
  have hdSquare : IsSquare (d ^ 2) := ⟨d, pow_two d⟩
  have hproduct := hratio.mul hdSquare
  have heq : (e * laws.discriminantUnit / d) * d ^ 2 =
      e * laws.discriminantUnit * d := by
    simp only [div_eq_mul_inv, pow_two]
    group
  rw [heq] at hproduct
  exact hproduct

end Bong
