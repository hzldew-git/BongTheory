/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointClass
import Bong.Bong.BinarySpinorGroupInvariant
import Mathlib.Algebra.Ring.Units

/-!
# Signed products at a binary endpoint

The two endpoint classes `-1/4` and `-Delta/4` determine the ordinary square
class of the signed product of two adjacent BONG values.  This is the
determinant-level form of the hyperbolic/unramified binary dichotomy.
-/

namespace Bong

open Dyadic

universe u v

/-- The negative of the endpoint representative `-1/4` is a square. -/
theorem isSquare_neg_negativeQuarterUnit
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    IsSquare (-(negativeQuarterUnit K)) := by
  let twoUnit : Kˣ := Units.mk0 (2 : K) (by norm_num)
  refine ⟨twoUnit⁻¹, ?_⟩
  apply Units.ext
  change -(-(4 : K)⁻¹) = (2 : K)⁻¹ * (2 : K)⁻¹
  norm_num

/-- A parameter in the `-1/4` endpoint class has square negative. -/
theorem isSquare_neg_of_unitSquareClass_eq_negativeQuarter
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {a : Kˣ}
    (hclass : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K)) :
    IsSquare (-a) := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq K hclass with
    ⟨s, _, hs⟩
  have hquotient : -a = (-(negativeQuarterUnit K)) / s ^ 2 := by
    rw [← hs]
    apply Units.ext
    simp only [Units.val_neg, Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero s]
  rw [hquotient]
  exact isSquare_neg_negativeQuarterUnit.div ⟨s, by simp [pow_two]⟩

/-- A parameter in the `-Delta/4` endpoint class becomes a square after its
negative is multiplied by `Delta`. -/
theorem isSquare_neg_mul_discriminant_of_endpointClass
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [laws : DyadicDiscriminantClassLaws K]
    {a : Kˣ}
    (hclass : unitSquareClass K a = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit)) :
    IsSquare (-a * laws.discriminantUnit) := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq K hclass with
    ⟨s, _, hs⟩
  have hquotient : -a * laws.discriminantUnit =
      (-(negativeQuarterUnit K)) * laws.discriminantUnit ^ 2 / s ^ 2 := by
    calc
      -a * laws.discriminantUnit =
          (-(a * s ^ 2)) * laws.discriminantUnit / s ^ 2 := by
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero s]
      _ = (-(negativeQuarterUnit K * laws.discriminantUnit)) *
          laws.discriminantUnit / s ^ 2 := by rw [hs]
      _ = (-(negativeQuarterUnit K)) * laws.discriminantUnit ^ 2 /
          s ^ 2 := by
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
          Units.val_pow_eq_pow_val]
        ring
  rw [hquotient]
  exact (isSquare_neg_negativeQuarterUnit.mul
    ⟨laws.discriminantUnit, by simp [pow_two]⟩).div
      ⟨s, by simp [pow_two]⟩

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The two refined endpoint classes give the corresponding alternatives for
the signed product of the adjacent BONG values. -/
theorem adjacentSignedProduct_endpoint_cases
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L n) (i : Fin n) (hi : i.val + 1 < n)
    (hclasses : b.adjacentUnitSquareClass i hi =
          unitSquareClass K (negativeQuarterUnit K) ∨
        b.adjacentUnitSquareClass i hi = unitSquareClass K
          (negativeQuarterUnit K * laws.discriminantUnit)) :
    IsSquare (-(b.valueUnit i * b.valueUnit ⟨i.val + 1, hi⟩)) ∨
      IsSquare (-(b.valueUnit i * b.valueUnit ⟨i.val + 1, hi⟩) *
        laws.discriminantUnit) := by
  have hproduct : -(b.valueUnit i * b.valueUnit ⟨i.val + 1, hi⟩) =
      (-(b.adjacentParameter i hi)) * b.valueUnit i ^ 2 := by
    unfold adjacentParameter
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero (b.valueUnit i)]
  rcases hclasses with hquarter | hdiscriminant
  · left
    rw [hproduct]
    exact (isSquare_neg_of_unitSquareClass_eq_negativeQuarter hquarter).mul
      ⟨b.valueUnit i, by simp [pow_two]⟩
  · right
    rw [hproduct]
    have hparameter :=
      isSquare_neg_mul_discriminant_of_endpointClass hdiscriminant
    have hreorder :
        (-(b.adjacentParameter i hi) * b.valueUnit i ^ 2) *
            laws.discriminantUnit =
          (-(b.adjacentParameter i hi) * laws.discriminantUnit) *
            b.valueUnit i ^ 2 := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    rw [hreorder]
    exact hparameter.mul ⟨b.valueUnit i, by simp [pow_two]⟩

end BONG

end Bong
