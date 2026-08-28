/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma72
import Bong.Bong.BeliDiscriminantNormGenerator
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.AdjacentNormGeneratorChange

/-!
# Norm-generator groups at the dyadic binary endpoints

For an admissible endpoint parameter of order `-2e`, the two possible refined
unit square classes are `-1/4` and `-Delta/4`.  In either case Beli's group
`g(a)` is the full valuation-unit square-class group.  This is the precise
local calculation needed when normalizing the binary blocks in Beli (2019),
Lemmas 7.17--7.18.
-/

namespace Bong

open Dyadic

universe u v

namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]
  [DyadicUnramifiedNormLaws K]

/-- At relative order `-2e`, either endpoint class admits every valuation-unit
square class as a norm-generator multiplier. -/
theorem valuationUnitClassHom_mem_beliNormGeneratorGroup_of_endpoint
    (a : Kˣ)
    (horder : ordUnit K a =
      -(2 * (ramificationIndex K : Int)))
    (hclass : unitSquareClass K a =
        unitSquareClass K (negativeQuarterUnit K) ∨
      unitSquareClass K a = unitSquareClass K
        (negativeQuarterUnit K * laws.discriminantUnit))
    (u : valuationUnitSubgroup K) :
    valuationUnitClassHom K u ∈ beliNormGeneratorGroup K a := by
  have hnotAbove :
      ¬ 2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [horder]
    have he : 0 ≤ (ramificationIndex K : Int) := by positivity
    omega
  rcases hclass with hquarter | hdiscriminant
  · have hdefect : beliParameterDefect K a = ⊤ :=
      beliParameterDefect_eq_of_unitSquareClass_eq
        (K := K) hquarter
        |>.trans (beliParameterDefect_negativeQuarterUnit (K := K))
    have hhigh : ¬ 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
      rw [hdefect]
      simp
    rw [beliNormGeneratorGroup_of_high_defect K a hnotAbove hhigh]
    have hexponent : beliHighDefectExponent K a = 0 := by
      unfold beliHighDefectExponent
      rw [horder]
      omega
    rw [hexponent]
    exact valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
      (K := K) u 0 (by simp)
  · have hsquare : IsSquare (-a * laws.discriminantUnit) :=
      isSquare_neg_mul_discriminant_of_endpointClass hdiscriminant
    rcases hsquare with ⟨s, hs⟩
    have hfactor : -a = laws.discriminantUnit *
        (s * laws.discriminantUnit⁻¹) ^ 2 := by
      calc
        -a = (-a * laws.discriminantUnit) *
            laws.discriminantUnit⁻¹ := by group
        _ = (s * s) * laws.discriminantUnit⁻¹ := by rw [hs]
        _ = laws.discriminantUnit *
            (s * laws.discriminantUnit⁻¹) ^ 2 := by
          simp only [pow_two]
          calc
            s * s * laws.discriminantUnit⁻¹ =
                (laws.discriminantUnit * laws.discriminantUnit⁻¹) *
                  (s * s) * laws.discriminantUnit⁻¹ := by simp
            _ = laws.discriminantUnit * s * laws.discriminantUnit⁻¹ * s *
                  laws.discriminantUnit⁻¹ := by ac_rfl
            _ = laws.discriminantUnit *
                (s * laws.discriminantUnit⁻¹ *
                  (s * laws.discriminantUnit⁻¹)) := by group
    have hdefect : beliParameterDefect K a =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      unfold beliParameterDefect
      rw [hfactor, quadraticDefect_mul_square,
        laws.discriminant_defect]
    have hcutoff : beliDefectCutoff K a =
        4 * ramificationIndex K := by
      unfold beliDefectCutoff
      rw [horder]
      have he : 0 ≤ (ramificationIndex K : Int) := by positivity
      omega
    have hlow : 2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
      rw [hdefect, hcutoff]
      norm_cast
      omega
    rw [beliNormGeneratorGroup_of_low_defect K a hnotAbove hlow]
    have hdefectNat : beliParameterDefectNat K a =
        2 * ramificationIndex K := by
      simp [beliParameterDefectNat, hdefect]
    have hexponent : beliLowDefectExponent K a = 0 := by
      unfold beliLowDefectExponent
      rw [horder, hdefectNat]
      omega
    rw [hexponent]
    constructor
    · exact valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        (K := K) u 0 (by simp)
    · refine ⟨u, ?_, rfl⟩
      change IsQuadraticNorm K (-a) (u : Kˣ)
      rw [hfactor, isQuadraticNorm_mul_square_left_iff]
      apply (isQuadraticNorm_discriminant_iff_even_order (u : Kˣ)).2
      have huOrder : ordUnit K (u : Kˣ) = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
      rw [huOrder]
      exact ⟨0, by simp⟩

end Dyadic

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]
  [DyadicUnramifiedNormLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Exact replacement of an endpoint pair inside a good BONG.  At the
endpoint order the first-value ratio automatically belongs to `g(a)`, so the
only remaining compatibility condition is equality of the binary determinant
square class. -/
theorem exists_endpointExactPairReplacementData
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    {n : Nat} (b : GoodBONG q L n) (i : Fin n)
    (hi : i.val + 1 < n) (targetZero targetOne : Kˣ)
    (hgap : b.order ⟨i.val + 1, hi⟩ - b.order i =
      -(2 * (ramificationIndex K : Int)))
    (hzeroOrder : ordUnit K targetZero = ordUnit K (b.valueUnit i))
    (honeOrder : ordUnit K targetOne =
      ordUnit K (b.valueUnit ⟨i.val + 1, hi⟩))
    (hdet : IsSquare
      ((b.valueUnit i * b.valueUnit ⟨i.val + 1, hi⟩) *
        (targetZero * targetOne))) :
    Nonempty (ExactPairReplacementData b i hi targetZero targetOne) := by
  let u : valuationUnitSubgroup K :=
    ⟨targetZero / b.valueUnit i, by
      apply (isValuationUnit_iff_ordUnit_eq_zero K _).2
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hzeroOrder]
      omega⟩
  have hparameterOrder : ordUnit K (b.toBONG.adjacentParameter i hi) =
      -(2 * (ramificationIndex K : Int)) := by
    rw [b.toBONG.ordUnit_adjacentParameter i hi]
    exact hgap
  have hclasses :
      unitSquareClass K (b.toBONG.adjacentParameter i hi) =
          unitSquareClass K (negativeQuarterUnit K) ∨
        unitSquareClass K (b.toBONG.adjacentParameter i hi) =
          unitSquareClass K
            (negativeQuarterUnit K * laws.discriminantUnit) := by
    simpa only [adjacentUnitSquareClass] using
      b.toBONG.adjacentUnitSquareClass_endpoint_cases i hi hgap
  have hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K (b.toBONG.adjacentParameter i hi) :=
    valuationUnitClassHom_mem_beliNormGeneratorGroup_of_endpoint
      (b.toBONG.adjacentParameter i hi) hparameterOrder hclasses u
  exact exists_exactPairReplacementData b i hi targetZero targetOne
    hzeroOrder honeOrder hdet u rfl hu

end BONG

end Bong
