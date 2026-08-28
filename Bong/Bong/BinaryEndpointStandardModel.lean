/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointModel
import Bong.Bong.BinaryShearIsometry
import Bong.Bong.BeliLemma317

/-!
# Standard binary endpoint models

The discriminant datum is normalized as in Beli's notation,
`Δ = 1 - 4ρ`.  Both endpoint parameters therefore admit the common standard
shear `1/2`.  Binary shear uniqueness then removes the arbitrary shear left by
the square-class representative theorem.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The common shear `1/2` in Beli's models `A(0,0)` and `A(2,2ρ)`. -/
noncomputable def standardEndpointShear : K :=
  (2 : K)⁻¹

/-- The fixed model attached to a chosen endpoint parameter. -/
noncomputable def standardEndpointModelSpace
    (b : BONG V q L 2) (d : Kˣ) : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.rescaleUnit (b.valueUnit 0)
    (QuadraticSpace.binaryModel d (standardEndpointShear (K := K)))

theorem standardEndpointShear_two_integral :
    (2 : K) * standardEndpointShear (K := K) ∈ IntegerRing K := by
  have heq : (2 : K) * standardEndpointShear (K := K) = 1 := by
    dsimp [standardEndpointShear]
    field_simp
  rw [heq]
  exact (IntegerRing K).one_mem

theorem negativeQuarter_standardEndpointShear_diagonal_integral :
    standardEndpointShear (K := K) ^ 2 +
        (negativeQuarterUnit K : K) ∈ IntegerRing K := by
  have heq : standardEndpointShear (K := K) ^ 2 +
      (negativeQuarterUnit K : K) = 0 := by
    dsimp [standardEndpointShear, negativeQuarterUnit]
    change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
    norm_num [show (4 : K) = 2 * 2 by norm_num]
  rw [heq]
  exact (IntegerRing K).zero_mem

theorem discriminant_standardEndpointShear_diagonal_integral
    [laws : DyadicDiscriminantClassLaws K] :
    standardEndpointShear (K := K) ^ 2 +
        ((negativeQuarterUnit K * laws.discriminantUnit : Kˣ) : K) ∈
      IntegerRing K := by
  have heq : standardEndpointShear (K := K) ^ 2 +
      ((negativeQuarterUnit K * laws.discriminantUnit : Kˣ) : K) =
        laws.rho := by
    rw [Units.val_mul, laws.discriminant_eq_one_sub_four_mul_rho]
    dsimp [standardEndpointShear, negativeQuarterUnit]
    change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ *
      (1 - 4 * laws.rho) = laws.rho
    norm_num [show (4 : K) = 2 * 2 by norm_num]
    field_simp
    ring
  rw [heq]
  apply (mem_integerRing_iff K).2
  change 0 ≤ ord K laws.rho
  rw [laws.rho_isValuationUnit]

/-- Dividing the adapted shear by the valuation unit used to change the
parameter preserves both binary integrality conditions. -/
theorem binaryModelCoefficient_div_isAdmissibleWitness
    (b : BONG V q L 2) (d s : Kˣ)
    (hs : IsValuationUnit K (s : K))
    (hparameter : d * s ^ 2 = b.binaryParameter) :
    (2 : K) * (b.binaryModelCoefficient / (s : K)) ∈ IntegerRing K ∧
      (b.binaryModelCoefficient / (s : K)) ^ 2 + (d : K) ∈
        IntegerRing K := by
  have hsInv : (s : K)⁻¹ ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change 0 ≤ ord K ((s : K)⁻¹)
    rw [AddValuation.map_inv, hs]
    rfl
  have hbase := b.binaryModelCoefficient_isAdmissibleWitness
  have hparameterCoe : (d : K) * (s : K) ^ 2 =
      (b.binaryParameter : K) :=
    congrArg Units.val hparameter
  constructor
  · have hmem := (IntegerRing K).mul_mem _ _ hbase.1 hsInv
    simpa [div_eq_mul_inv, mul_assoc] using hmem
  · have hsInvSq := (IntegerRing K).pow_mem hsInv 2
    have hmem := (IntegerRing K).mul_mem _ _ hbase.2 hsInvSq
    have heq : (b.binaryModelCoefficient / (s : K)) ^ 2 + (d : K) =
        (b.binaryModelCoefficient ^ 2 + (b.binaryParameter : K)) *
          (s : K)⁻¹ ^ 2 := by
      rw [← hparameterCoe]
      field_simp [Units.ne_zero s]
    rw [heq]
    exact hmem

/-- A prescribed endpoint square class is represented by the fixed standard
shear model, without any residual existential shear coefficient. -/
theorem isIsometric_standardEndpointModel
    (b : BONG V q L 2) (d : Kˣ)
    (hclass : b.binaryUnitSquareClass = unitSquareClass K d)
    (htwo : (2 : K) * standardEndpointShear (K := K) ∈ IntegerRing K)
    (hdiag : standardEndpointShear (K := K) ^ 2 + (d : K) ∈
      IntegerRing K) :
    Lattice.IsIsometric q (b.standardEndpointModelSpace d)
      L (binaryModelLattice (K := K)) := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass.symm with ⟨s, hs, hparameter⟩
  have htransformed :=
    b.binaryModelCoefficient_div_isAdmissibleWitness d s hs hparameter
  have hsub := binaryShear_sub_mem_integerRing
    d (b.binaryModelCoefficient / (s : K))
      (standardEndpointShear (K := K))
      htransformed.1 htransformed.2 htwo hdiag
  rcases b.normalizedBinaryModel_isIsometric with ⟨f⟩
  rcases rescaledBinaryModel_isIsometric_mul_valuationUnit_square
      (b.valueUnit 0) b.binaryParameter d s b.binaryModelCoefficient
      hs hparameter with ⟨g⟩
  rcases rescaledBinaryModel_isIsometric_of_shear_sub_integral
      (b.valueUnit 0) d (b.binaryModelCoefficient / (s : K))
      (standardEndpointShear (K := K)) hsub with ⟨h⟩
  exact ⟨f.symm.trans (g.trans h)⟩

/-- At relative order `-2e`, a binary BONG is one of Beli's two fixed
standard endpoint models. -/
theorem endpointStandardModel_cases
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L 2)
    (hgap : b.binaryOrderGap =
      -(2 * (ramificationIndex K : Int))) :
    Lattice.IsIsometric q
        (b.standardEndpointModelSpace (negativeQuarterUnit K))
        L (binaryModelLattice (K := K)) ∨
      Lattice.IsIsometric q
        (b.standardEndpointModelSpace
          (negativeQuarterUnit K * laws.discriminantUnit))
        L (binaryModelLattice (K := K)) := by
  have hparameterOrder : ordUnit K b.binaryParameter =
      -(2 * (ramificationIndex K : Int)) := by
    change b.binaryParameterOrder = _
    rw [b.binaryParameterOrder_eq_orderGap]
    exact hgap
  rcases laws.endpoint_parameter_class b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible hparameterOrder with
    hquarter | hdiscriminant
  · left
    exact b.isIsometric_standardEndpointModel
      (negativeQuarterUnit K) hquarter
      standardEndpointShear_two_integral
      negativeQuarter_standardEndpointShear_diagonal_integral
  · right
    exact b.isIsometric_standardEndpointModel
      (negativeQuarterUnit K * laws.discriminantUnit) hdiscriminant
      standardEndpointShear_two_integral
      discriminant_standardEndpointShear_diagonal_integral

end BONG

end Bong
