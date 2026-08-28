/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaUnitGeneralPlaneSplitting
import Bong.Lattice.OmearaOddQuaternaryModels
import Bong.Lattice.OmearaOddWeightNormGroupCriterion

/-!
# The odd ternary models in O'Meara 93:18(iv)

After a unit line is split from the first binary factor of either
quaternary model in 93:18(iii), the remaining ternary lattice has the form

`<c> orthogonal A(b,gamma)`.

This file computes its norm ideal, weight ideal, and norm group directly.
The hypotheses are scalar integrality and ideal containments, not an
additional local classification law.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Two square-coset descriptions agree when their leading coefficients
are mutually congruent to integral-square multiples modulo the error ideal. -/
theorem integralSquareCoset_eq_of_mutual_integral_square_congruence
    (a c : K) (I : CoefficientIdeal (K := K))
    (u v : IntegerRing K)
    (hca : c - a * (u : K) ^ 2 ∈ I)
    (hac : a - c * (v : K) ^ 2 ∈ I) :
    integralSquareCoset c I = integralSquareCoset a I := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, y, hy, rfl⟩
    let error := (c - a * (u : K) ^ 2) * (x : K) ^ 2 + y
    have hscaled :
        (c - a * (u : K) ^ 2) * (x : K) ^ 2 ∈ I := by
      have h := I.smul_mem (x ^ 2) hca
      change (x : K) ^ 2 * (c - a * (u : K) ^ 2) ∈ I at h
      simpa only [mul_comm] using h
    have herror : error ∈ I := I.add_mem hscaled hy
    refine ⟨u * x, error, herror, ?_⟩
    dsimp only [error]
    push_cast
    ring
  · rintro z ⟨x, y, hy, rfl⟩
    let error := (a - c * (v : K) ^ 2) * (x : K) ^ 2 + y
    have hscaled :
        (a - c * (v : K) ^ 2) * (x : K) ^ 2 ∈ I := by
      have h := I.smul_mem (x ^ 2) hac
      change (x : K) ^ 2 * (a - c * (v : K) ^ 2) ∈ I at h
      simpa only [mul_comm] using h
    have herror : error ∈ I := I.add_mem hscaled hy
    refine ⟨v * x, error, herror, ?_⟩
    dsimp only [error]
    push_cast
    ring

/-- Scalar data for a ternary model `<head> orthogonal A(b,tail)`. -/
structure OmearaOddTernaryModelData (K : Type u)
    [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  head : Kˣ
  b : Kˣ
  rightTail : K
  head_isValuationUnit : IsValuationUnit K (head : K)
  b_integral : (b : K) ∈ IntegerRing K
  rightTail_integral : rightTail ∈ IntegerRing K
  right_nondegenerate : (b : K) * rightTail ≠ 1
  right_determinant_unit :
    IsValuationUnit K ((b : K) * rightTail - 1)
  bIdeal_le_headIdeal :
    principalIdeal (K := K) (b : K) ≤
      principalIdeal (K := K) (head : K)
  twoIdeal_le_bIdeal :
    principalIdeal (K := K) (2 : K) ≤
      principalIdeal (K := K) (b : K)
  rightTailIdeal_le_bIdeal :
    principalIdeal (K := K) rightTail ≤
      principalIdeal (K := K) (b : K)
  odd_orders : Odd (ordUnit K head + ordUnit K b)

namespace OmearaOddTernaryModelData

variable (D : OmearaOddTernaryModelData K)

/-- The binary factor `A(b,rightTail)`. -/
noncomputable def rightSpace : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.omearaGeneralPlane
    (D.b : K) D.rightTail D.right_nondegenerate

/-- The ternary quadratic space `<head> orthogonal A(b,rightTail)`. -/
noncomputable def space : QuadraticSpace K (K × (Fin 2 → K)) :=
  (QuadraticSpace.scaledLine D.head).orthogonalSum D.rightSpace

/-- The standard product lattice of the ternary model. -/
noncomputable def lattice (D : OmearaOddTernaryModelData K) :
    Lattice K (K × (Fin 2 → K)) :=
  product (BONG.unaryModelLattice (K := K))
    (hyperbolicPlaneLattice (K := K))

/-- Explicit quadratic-value formula. -/
theorem quadratic_apply (x : K × (Fin 2 → K)) :
    D.space.quadratic x =
      (D.head : K) * x.1 ^ 2 +
        ((D.b : K) * x.2 0 ^ 2 + (2 : K) * x.2 0 * x.2 1 +
          D.rightTail * x.2 1 ^ 2) := by
  change ((QuadraticSpace.scaledLine D.head).orthogonalSum
    D.rightSpace).bilin x x = _
  rw [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.scaledLine_bilin_apply]
  change (D.head : K) * x.1 * x.1 +
    (QuadraticSpace.omearaGeneralPlane
      (D.b : K) D.rightTail D.right_nondegenerate).bilin x.2 x.2 = _
  rw [QuadraticSpace.omearaGeneralPlane_bilin_apply]
  ring

/-- Multiplying a generator by an integral scalar keeps it in every ideal
which contains the corresponding principal ideal. -/
private theorem coefficient_mul_integral_mem
    (c x : K) (hx : x ∈ IntegerRing K)
    (I : CoefficientIdeal (K := K))
    (hc : principalIdeal (K := K) c ≤ I) :
    c * x ∈ I := by
  let xO : IntegerRing K := ⟨x, hx⟩
  have hgenerator : c ∈ I := hc (generator_mem_principalIdeal c)
  have hsmul := I.smul_mem xO hgenerator
  change (xO : K) * c ∈ I at hsmul
  simpa only [xO, mul_comm] using hsmul

/-- The ternary model is unimodular. -/
theorem isModular : IsModular D.space D.lattice (1 : Kˣ) := by
  exact
    (unaryModelLattice_isModular_scaledLine_of_isValuationUnit
      D.head D.head_isValuationUnit).orthogonalProduct
      (omearaGeneralPlane_isModular_one
        (D.b : K) D.rightTail D.right_nondegenerate
        D.b_integral D.rightTail_integral D.right_determinant_unit)

/-- Its error ideal is `2 O`. -/
theorem twoScaleIdeal_eq_two :
    twoScaleIdeal D.space D.lattice =
      principalIdeal (K := K) (2 : K) := by
  exact twoScaleIdeal_eq_principalIdeal_two_of_unimodular
    D.isModular (by simp [space, Module.finrank_prod])

/-- The distinguished vector of value `head`. -/
def headVector (D : OmearaOddTernaryModelData K) :
    K × (Fin 2 → K) := (1, ![0, 0])

/-- The distinguished vector of value `b`. -/
def bVector (D : OmearaOddTernaryModelData K) :
    K × (Fin 2 → K) := (0, ![1, 0])

theorem headVector_mem : D.headVector ∈ D.lattice := by
  rw [lattice, mem_product_iff, BONG.mem_unaryModelLattice_iff,
    mem_omearaPlaneLattice_iff]
  simp [headVector]

theorem bVector_mem : D.bVector ∈ D.lattice := by
  rw [lattice, mem_product_iff, BONG.mem_unaryModelLattice_iff,
    mem_omearaPlaneLattice_iff]
  simp [bVector]

@[simp]
theorem quadratic_headVector :
    D.space.quadratic D.headVector = (D.head : K) := by
  rw [D.quadratic_apply]
  simp [headVector]

@[simp]
theorem quadratic_bVector :
    D.space.quadratic D.bVector = (D.b : K) := by
  rw [D.quadratic_apply]
  simp [bVector]

/-- The norm ideal is generated by the unit coefficient `head`. -/
theorem normIdeal_eq_head :
    normIdeal D.space D.lattice =
      principalIdeal (K := K) (D.head : K) := by
  have hrankOdd : Odd (finrank K (K × (Fin 2 → K))) := by
    norm_num [Module.finrank_prod]
  calc
    normIdeal D.space D.lattice = scaleIdeal D.space D.lattice :=
      normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
        D.space D.lattice (1 : Kˣ) D.isModular hrankOdd
    _ = principalIdeal (K := K) (1 : K) :=
      D.isModular.scaleIdeal_eq_principal
        (by simp [space, Module.finrank_prod])
    _ = principalIdeal (K := K) (D.head : K) := by
      symm
      apply (principalIdeal_eq_iff_ordUnit_eq D.head (1 : Kˣ)).mpr
      have hhead : ordUnit K D.head = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K D.head).mp
          D.head_isValuationUnit
      have hone : ordUnit K (1 : Kˣ) = 0 := by
        have h := ordUnit_mul K (1 : Kˣ) 1
        simp only [mul_one] at h
        omega
      rw [hhead, hone]

/-- The unary head factor itself has norm ideal generated by `head`. -/
theorem headLine_normIdeal_eq_head :
    normIdeal (QuadraticSpace.scaledLine D.head)
        (BONG.unaryModelLattice (K := K)) =
      principalIdeal (K := K) (D.head : K) := by
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem
    intro x hx
    rw [QuadraticSpace.scaledLine_quadratic_apply]
    have hxIntegral : x ∈ IntegerRing K :=
      (BONG.mem_unaryModelLattice_iff x).mp hx
    exact mul_mem_principalIdeal_of_mem_integerRing
      (K := K) (D.head : K) (x ^ 2)
        ((IntegerRing K).toSubring.pow_mem hxIntegral 2)
  · rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈ BONG.unaryModelLattice (K := K) := by
      rw [BONG.mem_unaryModelLattice_iff]
      exact (IntegerRing K).one_mem
    have hvalue :
        (QuadraticSpace.scaledLine D.head).quadratic (1 : K) =
          (D.head : K) := by
      rw [QuadraticSpace.scaledLine_quadratic_apply]
      ring
    rw [← hvalue]
    exact quadratic_mem_normIdeal_of_mem
      (QuadraticSpace.scaledLine D.head)
      (BONG.unaryModelLattice (K := K)) hone

/-- `head` is a norm generator of the ternary model. -/
theorem head_isNormGeneratorValue :
    IsNormGeneratorValue D.space D.lattice D.head := by
  constructor
  · exact ⟨D.headVector, D.headVector_mem, 0, Submodule.zero_mem _, by simp⟩
  · exact D.normIdeal_eq_head

/-- The opposite-parity value `b` is represented. -/
theorem b_mem_normGroupSet :
    (D.b : K) ∈ normGroupSet D.space D.lattice := by
  exact ⟨D.bVector, D.bVector_mem, 0, Submodule.zero_mem _, by simp⟩

/-- Every enlarged norm value lies in `head O^2 + b O`. -/
theorem normGroupSet_subset_integralSquareCoset :
    normGroupSet D.space D.lattice ⊆
      integralSquareCoset (D.head : K)
        (principalIdeal (K := K) (D.b : K)) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hx' := (mem_product_iff.mp hx)
  have hxHead := (BONG.mem_unaryModelLattice_iff x.1).mp hx'.1
  have hxR := (mem_omearaPlaneLattice_iff x.2).mp hx'.2
  let bI := principalIdeal (K := K) (D.b : K)
  let c : IntegerRing K := ⟨x.1, hxHead⟩
  have hb0 : (D.b : K) * x.2 0 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem (D.b : K) (x.2 0 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.1 2) bI le_rfl
  have htwo : (2 : K) * (x.2 0 * x.2 1) ∈ bI :=
    coefficient_mul_integral_mem (2 : K) (x.2 0 * x.2 1)
      ((IntegerRing K).toSubring.mul_mem hxR.1 hxR.2)
      bI D.twoIdeal_le_bIdeal
  have htail : D.rightTail * x.2 1 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem D.rightTail (x.2 1 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.2 2)
      bI D.rightTailIdeal_le_bIdeal
  have hyB : y ∈ bI := by
    rw [D.twoScaleIdeal_eq_two] at hy
    exact D.twoIdeal_le_bIdeal hy
  let error : K :=
    (D.b : K) * x.2 0 ^ 2 + (2 : K) * x.2 0 * x.2 1 +
      D.rightTail * x.2 1 ^ 2 + y
  have herror : error ∈ bI := by
    exact bI.add_mem
      (bI.add_mem (bI.add_mem hb0
        (by simpa only [mul_assoc] using htwo)) htail) hyB
  refine ⟨c, error, herror, ?_⟩
  rw [D.quadratic_apply]
  dsimp only [c, error]
  ring

/-- The weight ideal is exactly `b O`. -/
theorem weightIdeal_eq_b :
    weightIdeal D.space D.lattice =
      principalIdeal (K := K) (D.b : K) := by
  apply weightIdeal_eq_principalIdeal_of_odd_normGroup_bound
    D.head D.b D.head_isNormGeneratorValue D.b_mem_normGroupSet
      D.odd_orders
  · rw [D.twoScaleIdeal_eq_two]
    exact D.twoIdeal_le_bIdeal
  · exact D.normGroupSet_subset_integralSquareCoset

/-- The complete norm-group formula for the odd ternary model. -/
theorem normGroupSet_eq :
    normGroupSet D.space D.lattice =
      integralSquareCoset (D.head : K)
        (principalIdeal (K := K) (D.b : K)) := by
  rw [normGroupSet_eq_integralSquareCoset_weightIdeal
    D.head D.head_isNormGeneratorValue, D.weightIdeal_eq_b]

end OmearaOddTernaryModelData

namespace OmearaOddQuaternaryModelData

variable (D : OmearaOddQuaternaryModelData K)

/-- Splitting the first plane of a quaternary model at a valuation-unit
coefficient leaves a ternary model of the preceding form. -/
noncomputable def ternaryComplementData
    (ha : IsValuationUnit K (D.a : K)) :
    OmearaOddTernaryModelData K := by
  let head := unitGeneralPlaneTail D.a D.leftTail D.left_nondegenerate
  have hheadUnit : IsValuationUnit K (head : K) := by
    rw [IsValuationUnit, coe_unitGeneralPlaneTail]
    have hformula :
        D.leftTail - (D.a : K)⁻¹ =
          ((D.a : K) * D.leftTail - 1) * (D.a : K)⁻¹ := by
      field_simp [Units.ne_zero D.a]
    rw [hformula, ord_mul, D.left_determinant_unit,
      AddValuation.map_inv, ha]
    simp
  have hheadOrder : ordUnit K head = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K head).mp hheadUnit
  have haOrder : ordUnit K D.a = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K D.a).mp ha
  have hbLeHead : principalIdeal (K := K) (D.b : K) ≤
      principalIdeal (K := K) (head : K) := by
    apply (principalIdeal_le_iff_ord_ge
      (Units.ne_zero D.b) (Units.ne_zero head)).2
    rw [← coe_ordUnit, ← coe_ordUnit, hheadOrder]
    have hbIntegral := (mem_integerRing_iff K).1 D.b_integral
    rw [Dyadic.IsIntegral, ← coe_ordUnit] at hbIntegral
    exact hbIntegral
  exact
    { head := head
      b := D.b
      rightTail := D.rightTail
      head_isValuationUnit := hheadUnit
      b_integral := D.b_integral
      rightTail_integral := D.rightTail_integral
      right_nondegenerate := D.right_nondegenerate
      right_determinant_unit := D.right_determinant_unit
      bIdeal_le_headIdeal := hbLeHead
      twoIdeal_le_bIdeal := D.twoIdeal_le_bIdeal
      rightTailIdeal_le_bIdeal := D.rightTailIdeal_le_bIdeal
      odd_orders := by
        simpa only [hheadOrder, haOrder, zero_add] using D.odd_orders }

@[simp]
theorem ternaryComplementData_head
    (ha : IsValuationUnit K (D.a : K)) :
    (D.ternaryComplementData ha).head =
      unitGeneralPlaneTail D.a D.leftTail D.left_nondegenerate :=
  rfl

@[simp]
theorem ternaryComplementData_b
    (ha : IsValuationUnit K (D.a : K)) :
    (D.ternaryComplementData ha).b = D.b :=
  rfl

@[simp]
theorem ternaryComplementData_rightTail
    (ha : IsValuationUnit K (D.a : K)) :
    (D.ternaryComplementData ha).rightTail = D.rightTail :=
  rfl

end OmearaOddQuaternaryModelData

end Lattice

end Bong
