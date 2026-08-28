/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralPlaneChangeOfComplement
import Bong.Lattice.OmearaOddWeightNormGroupCriterion
import Bong.Lattice.ModularOrthogonalProduct
import Bong.Lattice.NormIdealOrthogonalProduct

/-!
# Norm groups of the odd quaternary O'Meara models

The two lattices in O'Meara 93:18(iii) are orthogonal products of integral
general planes.  This file proves the common norm-group calculation in a
parameterized form.  The hypotheses are ordinary ideal containments which
will be verified for the two printed models; no local classification law is
assumed.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Scalar data sufficient for the norm-group computation of the two
general-plane product occurring in 93:18(iii). -/
structure OmearaOddQuaternaryModelData (K : Type u)
    [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  a : Kˣ
  b : Kˣ
  leftTail : K
  rightTail : K
  left_nondegenerate : (a : K) * leftTail ≠ 1
  right_nondegenerate : (b : K) * rightTail ≠ 1
  a_integral : (a : K) ∈ IntegerRing K
  b_integral : (b : K) ∈ IntegerRing K
  leftTail_integral : leftTail ∈ IntegerRing K
  rightTail_integral : rightTail ∈ IntegerRing K
  left_determinant_unit :
    IsValuationUnit K ((a : K) * leftTail - 1)
  right_determinant_unit :
    IsValuationUnit K ((b : K) * rightTail - 1)
  bIdeal_le_aIdeal :
    principalIdeal (K := K) (b : K) ≤ principalIdeal (K := K) (a : K)
  twoIdeal_le_bIdeal :
    principalIdeal (K := K) (2 : K) ≤ principalIdeal (K := K) (b : K)
  leftTailIdeal_le_bIdeal :
    principalIdeal (K := K) leftTail ≤ principalIdeal (K := K) (b : K)
  rightTailIdeal_le_bIdeal :
    principalIdeal (K := K) rightTail ≤ principalIdeal (K := K) (b : K)
  odd_orders : Odd (ordUnit K a + ordUnit K b)

namespace OmearaOddQuaternaryModelData

variable (D : OmearaOddQuaternaryModelData K)

/-- Left binary factor of the quaternary model. -/
noncomputable def leftSpace : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.omearaGeneralPlane
    (D.a : K) D.leftTail D.left_nondegenerate

/-- Right binary factor of the quaternary model. -/
noncomputable def rightSpace : QuadraticSpace K (Fin 2 → K) :=
  QuadraticSpace.omearaGeneralPlane
    (D.b : K) D.rightTail D.right_nondegenerate

/-- The quaternary quadratic space of the model. -/
noncomputable def space :
    QuadraticSpace K ((Fin 2 → K) × (Fin 2 → K)) :=
  D.leftSpace.orthogonalSum D.rightSpace

/-- Its standard integral product lattice. -/
noncomputable def lattice (D : OmearaOddQuaternaryModelData K) :
    Lattice K ((Fin 2 → K) × (Fin 2 → K)) :=
  product (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))

/-- Explicit quadratic-value formula for the model. -/
theorem quadratic_apply
    (x : (Fin 2 → K) × (Fin 2 → K)) :
    D.space.quadratic x =
      (D.a : K) * x.1 0 ^ 2 + (2 : K) * x.1 0 * x.1 1 +
        D.leftTail * x.1 1 ^ 2 +
      ((D.b : K) * x.2 0 ^ 2 + (2 : K) * x.2 0 * x.2 1 +
        D.rightTail * x.2 1 ^ 2) := by
  change
    (D.leftSpace.orthogonalSum D.rightSpace).bilin x x = _
  rw [QuadraticSpace.orthogonalSum_bilin_apply]
  change
    (QuadraticSpace.omearaGeneralPlane
        (D.a : K) D.leftTail D.left_nondegenerate).bilin x.1 x.1 +
      (QuadraticSpace.omearaGeneralPlane
        (D.b : K) D.rightTail D.right_nondegenerate).bilin x.2 x.2 = _
  rw [
    QuadraticSpace.omearaGeneralPlane_bilin_apply,
    QuadraticSpace.omearaGeneralPlane_bilin_apply]
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

/-- The standard quaternary model is unimodular. -/
theorem isModular : IsModular D.space D.lattice (1 : Kˣ) := by
  exact (omearaGeneralPlane_isModular_one
      (D.a : K) D.leftTail D.left_nondegenerate
      D.a_integral D.leftTail_integral D.left_determinant_unit).orthogonalProduct
    (omearaGeneralPlane_isModular_one
      (D.b : K) D.rightTail D.right_nondegenerate
      D.b_integral D.rightTail_integral D.right_determinant_unit)

/-- In this positive-rank unimodular model the error ideal is `2 O`. -/
theorem twoScaleIdeal_eq_two :
    twoScaleIdeal D.space D.lattice =
      principalIdeal (K := K) (2 : K) := by
  unfold twoScaleIdeal
  rw [D.isModular.scaleIdeal_eq_principal (by simp),
    twiceIdeal_principalIdeal]
  simp

/-- The first standard vector in the left plane. -/
def aVector (D : OmearaOddQuaternaryModelData K) :
    (Fin 2 → K) × (Fin 2 → K) :=
  (![1, 0], ![0, 0])

/-- The first standard vector in the right plane. -/
def bVector (D : OmearaOddQuaternaryModelData K) :
    (Fin 2 → K) × (Fin 2 → K) :=
  (![0, 0], ![1, 0])

theorem aVector_mem : D.aVector ∈ D.lattice := by
  change (![1, 0], ![0, 0]) ∈
    product (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K))
  rw [mem_product_iff, mem_omearaPlaneLattice_iff,
    mem_omearaPlaneLattice_iff]
  simp

theorem bVector_mem : D.bVector ∈ D.lattice := by
  change (![0, 0], ![1, 0]) ∈
    product (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K))
  rw [mem_product_iff, mem_omearaPlaneLattice_iff,
    mem_omearaPlaneLattice_iff]
  simp

@[simp]
theorem quadratic_aVector :
    D.space.quadratic D.aVector = (D.a : K) := by
  rw [D.quadratic_apply]
  simp [aVector]

@[simp]
theorem quadratic_bVector :
    D.space.quadratic D.bVector = (D.b : K) := by
  rw [D.quadratic_apply]
  simp [bVector]

/-- Every quadratic value of the standard lattice lies in `a O`. -/
theorem quadratic_mem_aIdeal
    (x : (Fin 2 → K) × (Fin 2 → K))
    (hx : x ∈ D.lattice) :
    D.space.quadratic x ∈ principalIdeal (K := K) (D.a : K) := by
  have hx' := (mem_product_iff.mp hx)
  have hxL := (mem_omearaPlaneLattice_iff x.1).mp hx'.1
  have hxR := (mem_omearaPlaneLattice_iff x.2).mp hx'.2
  let aI := principalIdeal (K := K) (D.a : K)
  let bI := principalIdeal (K := K) (D.b : K)
  have ha0 : (D.a : K) * x.1 0 ^ 2 ∈ aI :=
    coefficient_mul_integral_mem (D.a : K) (x.1 0 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxL.1 2) aI le_rfl
  have htwoL : (2 : K) * (x.1 0 * x.1 1) ∈ bI :=
    coefficient_mul_integral_mem (2 : K) (x.1 0 * x.1 1)
      ((IntegerRing K).toSubring.mul_mem hxL.1 hxL.2)
      bI D.twoIdeal_le_bIdeal
  have htailL : D.leftTail * x.1 1 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem D.leftTail (x.1 1 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxL.2 2)
      bI D.leftTailIdeal_le_bIdeal
  have hb0 : (D.b : K) * x.2 0 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem (D.b : K) (x.2 0 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.1 2) bI le_rfl
  have htwoR : (2 : K) * (x.2 0 * x.2 1) ∈ bI :=
    coefficient_mul_integral_mem (2 : K) (x.2 0 * x.2 1)
      ((IntegerRing K).toSubring.mul_mem hxR.1 hxR.2)
      bI D.twoIdeal_le_bIdeal
  have htailR : D.rightTail * x.2 1 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem D.rightTail (x.2 1 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.2 2)
      bI D.rightTailIdeal_le_bIdeal
  have hrest :
      (2 : K) * x.1 0 * x.1 1 + D.leftTail * x.1 1 ^ 2 +
        ((D.b : K) * x.2 0 ^ 2 + (2 : K) * x.2 0 * x.2 1 +
          D.rightTail * x.2 1 ^ 2) ∈ bI := by
    exact bI.add_mem
      (bI.add_mem (by simpa only [mul_assoc] using htwoL) htailL)
      (bI.add_mem (bI.add_mem hb0
        (by simpa only [mul_assoc] using htwoR)) htailR)
  rw [D.quadratic_apply]
  have hsum := aI.add_mem ha0 (D.bIdeal_le_aIdeal hrest)
  convert hsum using 1 <;> ring

/-- The norm ideal is generated by `a`. -/
theorem normIdeal_eq_a :
    normIdeal D.space D.lattice =
      principalIdeal (K := K) (D.a : K) := by
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem
    intro x hx
    exact D.quadratic_mem_aIdeal x hx
  · rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    rw [← D.quadratic_aVector]
    exact quadratic_mem_normIdeal_of_mem D.space D.lattice D.aVector_mem

/-- The left binary factor already carries the full norm ideal generated
by `a`.  This is the norm-preserving complement used when the right weight
plane is moved to the front in O'Meara 93:18(v). -/
theorem left_normIdeal_eq_a :
    normIdeal D.leftSpace (hyperbolicPlaneLattice (K := K)) =
      principalIdeal (K := K) (D.a : K) := by
  apply le_antisymm
  · calc
      normIdeal D.leftSpace (hyperbolicPlaneLattice (K := K)) ≤
          normIdeal D.leftSpace (hyperbolicPlaneLattice (K := K)) ⊔
            normIdeal D.rightSpace
              (hyperbolicPlaneLattice (K := K)) := _root_.le_sup_left
      _ = normIdeal D.space D.lattice := by
        exact normIdeal_orthogonalProduct.symm
      _ = principalIdeal (K := K) (D.a : K) := D.normIdeal_eq_a
  · rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
    let e0 : Fin 2 → K := ![1, 0]
    have he0 : e0 ∈ hyperbolicPlaneLattice (K := K) := by
      rw [mem_omearaPlaneLattice_iff]
      simp [e0]
    have hvalue : D.leftSpace.quadratic e0 = (D.a : K) := by
      change
        (QuadraticSpace.omearaGeneralPlane
          (D.a : K) D.leftTail D.left_nondegenerate).quadratic e0 =
            (D.a : K)
      rw [QuadraticSpace.quadratic,
        QuadraticSpace.omearaGeneralPlane_bilin_apply]
      simp [e0]
    rw [← hvalue]
    exact quadratic_mem_normIdeal_of_mem D.leftSpace
      (hyperbolicPlaneLattice (K := K)) he0

/-- The coefficient `a` is a norm generator of the model. -/
theorem a_isNormGeneratorValue :
    IsNormGeneratorValue D.space D.lattice D.a := by
  constructor
  · exact ⟨D.aVector, D.aVector_mem, 0, Submodule.zero_mem _, by simp⟩
  · exact D.normIdeal_eq_a

/-- The opposite-parity value `b` is represented by the model. -/
theorem b_mem_normGroupSet :
    (D.b : K) ∈ normGroupSet D.space D.lattice := by
  exact ⟨D.bVector, D.bVector_mem, 0, Submodule.zero_mem _, by simp⟩

/-- Every enlarged norm value lies in `a O^2 + b O`. -/
theorem normGroupSet_subset_integralSquareCoset :
    normGroupSet D.space D.lattice ⊆
      integralSquareCoset (D.a : K)
        (principalIdeal (K := K) (D.b : K)) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hx' := (mem_product_iff.mp hx)
  have hxL := (mem_omearaPlaneLattice_iff x.1).mp hx'.1
  have hxR := (mem_omearaPlaneLattice_iff x.2).mp hx'.2
  let bI := principalIdeal (K := K) (D.b : K)
  let c : IntegerRing K := ⟨x.1 0, hxL.1⟩
  have htwoL : (2 : K) * (x.1 0 * x.1 1) ∈ bI :=
    coefficient_mul_integral_mem (2 : K) (x.1 0 * x.1 1)
      ((IntegerRing K).toSubring.mul_mem hxL.1 hxL.2)
      bI D.twoIdeal_le_bIdeal
  have htailL : D.leftTail * x.1 1 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem D.leftTail (x.1 1 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxL.2 2)
      bI D.leftTailIdeal_le_bIdeal
  have hb0 : (D.b : K) * x.2 0 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem (D.b : K) (x.2 0 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.1 2) bI le_rfl
  have htwoR : (2 : K) * (x.2 0 * x.2 1) ∈ bI :=
    coefficient_mul_integral_mem (2 : K) (x.2 0 * x.2 1)
      ((IntegerRing K).toSubring.mul_mem hxR.1 hxR.2)
      bI D.twoIdeal_le_bIdeal
  have htailR : D.rightTail * x.2 1 ^ 2 ∈ bI :=
    coefficient_mul_integral_mem D.rightTail (x.2 1 ^ 2)
      ((IntegerRing K).toSubring.pow_mem hxR.2 2)
      bI D.rightTailIdeal_le_bIdeal
  have hyB : y ∈ bI := by
    rw [D.twoScaleIdeal_eq_two] at hy
    exact D.twoIdeal_le_bIdeal hy
  let error : K :=
    (2 : K) * x.1 0 * x.1 1 + D.leftTail * x.1 1 ^ 2 +
      ((D.b : K) * x.2 0 ^ 2 + (2 : K) * x.2 0 * x.2 1 +
        D.rightTail * x.2 1 ^ 2) + y
  have herror : error ∈ bI := by
    exact bI.add_mem
      (bI.add_mem
        (bI.add_mem (by simpa only [mul_assoc] using htwoL) htailL)
        (bI.add_mem (bI.add_mem hb0
          (by simpa only [mul_assoc] using htwoR)) htailR)) hyB
  refine ⟨c, error, herror, ?_⟩
  rw [D.quadratic_apply]
  dsimp only [c, error]
  ring

/-- The weight ideal of the model is exactly `b O`. -/
theorem weightIdeal_eq_b :
    weightIdeal D.space D.lattice =
      principalIdeal (K := K) (D.b : K) := by
  apply weightIdeal_eq_principalIdeal_of_odd_normGroup_bound
    D.a D.b D.a_isNormGeneratorValue D.b_mem_normGroupSet
      D.odd_orders
  · rw [D.twoScaleIdeal_eq_two]
    exact D.twoIdeal_le_bIdeal
  · exact D.normGroupSet_subset_integralSquareCoset

/-- Both printed quaternary models therefore have the same explicit norm
group `a O^2 + b O`. -/
theorem normGroupSet_eq :
    normGroupSet D.space D.lattice =
      integralSquareCoset (D.a : K)
        (principalIdeal (K := K) (D.b : K)) := by
  rw [normGroupSet_eq_integralSquareCoset_weightIdeal
    D.a D.a_isNormGeneratorValue, D.weightIdeal_eq_b]

end OmearaOddQuaternaryModelData

end Lattice

end Bong
