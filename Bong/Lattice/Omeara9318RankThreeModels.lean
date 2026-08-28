/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaOddTernaryModels
import Bong.Lattice.Omeara9318RankFourModels

/-!
# The two ternary complements in O'Meara 93:18(iv)

For a unit norm generator `a`, split the first plane in each quaternary
model of 93:18(iii).  The remaining ternary models have leading coefficients
`-d/a` and `-d'/a`, respectively.  Their norm groups are both the original
coset `a O^2 + b O`, which supplies the nontrivial target-side hypothesis
of Corollary 93:14a.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

private theorem integralSquareCoset_tail_eq
    (a head : Kˣ) (s : K)
    (I : CoefficientIdeal (K := K))
    (ha : IsValuationUnit K (a : K))
    (herror : (2 : K) + s ∈ I)
    (hhead : (head : K) = -(1 + s) * (a : K)⁻¹) :
    integralSquareCoset (head : K) I =
      integralSquareCoset (a : K) I := by
  have haMem : (a : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 ha.ge
  have haInvUnit : IsValuationUnit K ((a : K)⁻¹) := by
    simpa [IsValuationUnit, AddValuation.map_inv, ha]
  have haInvMem : (a : K)⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 haInvUnit.ge
  let aO : IntegerRing K := ⟨a, haMem⟩
  let aInvO : IntegerRing K := ⟨(a : K)⁻¹, haInvMem⟩
  have hheadToA :
      (head : K) - (a : K) * (aInvO : K) ^ 2 ∈ I := by
    have hscaled := I.smul_mem aInvO (I.neg_mem herror)
    change (a : K)⁻¹ * (-((2 : K) + s)) ∈ I at hscaled
    convert hscaled using 1
    rw [hhead]
    dsimp only [aInvO]
    field_simp [Units.ne_zero a]
    ring
  have haToHead :
      (a : K) - (head : K) * (aO : K) ^ 2 ∈ I := by
    have hscaled := I.smul_mem aO herror
    change (a : K) * ((2 : K) + s) ∈ I at hscaled
    convert hscaled using 1
    rw [hhead]
    field_simp [Units.ne_zero a]
    ring
  exact integralSquareCoset_eq_of_mutual_integral_square_congruence
    (a : K) (head : K) I aInvO aO hheadToA haToHead

namespace Omeara9318RankFourModelParameters

variable (P : Omeara9318RankFourModelParameters K)

/-- The parameter `alpha` lies in `b O` when `a` is a valuation unit. -/
theorem alpha_mem_bIdeal (ha : IsValuationUnit K (P.a : K)) :
    P.alpha ∈ principalIdeal (K := K) (P.b : K) := by
  let bI := principalIdeal (K := K) (P.b : K)
  have htail : -P.alpha * (P.a : K)⁻¹ ∈ bI :=
    P.jLeftTailIdeal_le_bIdeal
      (generator_mem_principalIdeal (-P.alpha * (P.a : K)⁻¹))
  have haMem : (P.a : K) ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 ha.ge
  let aO : IntegerRing K := ⟨P.a, haMem⟩
  have hscaled := bI.smul_mem aO htail
  change (P.a : K) * (-P.alpha * (P.a : K)⁻¹) ∈ bI at hscaled
  have hneg : -P.alpha ∈ bI := by
    convert hscaled using 1
    field_simp [Units.ne_zero P.a]
  simpa only [neg_neg] using bI.neg_mem hneg

/-- The correction `4 rho` lies in `b O`. -/
theorem four_rho_mem_bIdeal :
    (4 : K) * laws.rho ∈ principalIdeal (K := K) (P.b : K) := by
  let bI := principalIdeal (K := K) (P.b : K)
  have htwo : (2 : K) ∈ bI :=
    P.twoIdeal_le_bIdeal
      (generator_mem_principalIdeal (K := K) (2 : K))
  have htwoRho : (2 : K) * laws.rho ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem (by norm_num)
      ((mem_integerRing_iff K).2 laws.rho_isValuationUnit.ge)
  let twoRhoO : IntegerRing K := ⟨(2 : K) * laws.rho, htwoRho⟩
  have hscaled := bI.smul_mem twoRhoO htwo
  change ((2 : K) * laws.rho) * 2 ∈ bI at hscaled
  convert hscaled using 1 <;> ring

/-- The error `2 + alpha` is in `b O`. -/
theorem two_add_alpha_mem_bIdeal
    (ha : IsValuationUnit K (P.a : K)) :
    (2 : K) + P.alpha ∈ principalIdeal (K := K) (P.b : K) := by
  exact (principalIdeal (K := K) (P.b : K)).add_mem
    (P.twoIdeal_le_bIdeal
      (generator_mem_principalIdeal (K := K) (2 : K)))
    (P.alpha_mem_bIdeal ha)

/-- The shifted error `2 + alpha - 4 rho` is in `b O`. -/
theorem two_add_alpha_sub_four_rho_mem_bIdeal
    (ha : IsValuationUnit K (P.a : K)) :
    (2 : K) + P.alpha - 4 * laws.rho ∈
      principalIdeal (K := K) (P.b : K) := by
  exact (principalIdeal (K := K) (P.b : K)).sub_mem
    (P.two_add_alpha_mem_bIdeal ha) P.four_rho_mem_bIdeal

/-- Ternary complement of the `J` model. -/
noncomputable def jTernaryData
    (ha : IsValuationUnit K (P.a : K)) :
    OmearaOddTernaryModelData K :=
  P.jData.ternaryComplementData ha

/-- Ternary complement of the discriminant-twisted `K` model. -/
noncomputable def kTernaryData
    (ha : IsValuationUnit K (P.a : K)) :
    OmearaOddTernaryModelData K :=
  P.kData.ternaryComplementData ha

/-- The first ternary coefficient is `-d/a`. -/
theorem jTernaryData_head_coe
    (ha : IsValuationUnit K (P.a : K)) :
    ((P.jTernaryData ha).head : K) =
      -(P.d : K) * (P.a : K)⁻¹ := by
  rw [jTernaryData, OmearaOddQuaternaryModelData.ternaryComplementData_head,
    coe_unitGeneralPlaneTail]
  simp [jData, d, coe_omeara9318DiscriminantUnit]
  field_simp [Units.ne_zero P.a]
  ring

/-- The second ternary coefficient is `-d'/a`. -/
theorem kTernaryData_head_coe
    (ha : IsValuationUnit K (P.a : K)) :
    ((P.kTernaryData ha).head : K) =
      -(P.dShift : K) * (P.a : K)⁻¹ := by
  rw [kTernaryData, OmearaOddQuaternaryModelData.ternaryComplementData_head,
    coe_unitGeneralPlaneTail]
  simp [kData, dShift, coe_omeara9318ShiftedDiscriminantUnit]
  field_simp [Units.ne_zero P.a]
  ring

/-- The `J` ternary complement has norm group `a O^2 + b O`. -/
theorem jTernary_normGroupSet_eq_common
    (ha : IsValuationUnit K (P.a : K)) :
    normGroupSet (P.jTernaryData ha).space (P.jTernaryData ha).lattice =
      integralSquareCoset (P.a : K)
        (principalIdeal (K := K) (P.b : K)) := by
  rw [(P.jTernaryData ha).normGroupSet_eq]
  apply integralSquareCoset_tail_eq P.a (P.jTernaryData ha).head
    P.alpha (principalIdeal (K := K) (P.b : K)) ha
      (P.two_add_alpha_mem_bIdeal ha)
  exact P.jTernaryData_head_coe ha

/-- The `K` ternary complement has the same norm group. -/
theorem kTernary_normGroupSet_eq_common
    (ha : IsValuationUnit K (P.a : K)) :
    normGroupSet (P.kTernaryData ha).space (P.kTernaryData ha).lattice =
      integralSquareCoset (P.a : K)
        (principalIdeal (K := K) (P.b : K)) := by
  rw [(P.kTernaryData ha).normGroupSet_eq]
  apply integralSquareCoset_tail_eq P.a (P.kTernaryData ha).head
    (P.alpha - 4 * laws.rho)
      (principalIdeal (K := K) (P.b : K)) ha
  · simpa only [sub_eq_add_neg, add_assoc] using
      P.two_add_alpha_sub_four_rho_mem_bIdeal ha
  · simpa [dShift, coe_omeara9318ShiftedDiscriminantUnit,
      sub_eq_add_neg, add_assoc] using P.kTernaryData_head_coe ha

/-- Display the `J` quaternary model as the common unit line followed by
its ternary complement. -/
noncomputable def jDisplayedTernaryIsometry
    (ha : IsValuationUnit K (P.a : K)) :
    Isometry P.jData.space
      ((QuadraticSpace.scaledLine P.a).orthogonalSum
        (P.jTernaryData ha).space)
      P.jData.lattice
      (product (BONG.unaryModelLattice (K := K))
        (P.jTernaryData ha).lattice) := by
  let split := unitGeneralPlaneSplittingIsometry
    P.a P.jData.leftTail P.jData.left_nondegenerate ha
  let keep := Isometry.refl P.jData.rightSpace
    (hyperbolicPlaneLattice (K := K))
  let splitFirst := split.orthogonalProductBasic keep
  let associate : Isometry
      (((QuadraticSpace.scaledLine P.a).orthogonalSum
        (QuadraticSpace.scaledLine
          (unitGeneralPlaneTail P.a P.jData.leftTail
            P.jData.left_nondegenerate))).orthogonalSum
        P.jData.rightSpace)
      ((QuadraticSpace.scaledLine P.a).orthogonalSum
        ((QuadraticSpace.scaledLine
          (unitGeneralPlaneTail P.a P.jData.leftTail
            P.jData.left_nondegenerate)).orthogonalSum
          P.jData.rightSpace))
      (product
        (product (BONG.unaryModelLattice (K := K))
          (BONG.unaryModelLattice (K := K)))
        (hyperbolicPlaneLattice (K := K)))
      (product (BONG.unaryModelLattice (K := K))
        (product (BONG.unaryModelLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))) :=
    orthogonalProductAssoc
  exact splitFirst.trans associate

/-- Display the discriminant-twisted `K` model in the same way. -/
noncomputable def kDisplayedTernaryIsometry
    (ha : IsValuationUnit K (P.a : K)) :
    Isometry P.kData.space
      ((QuadraticSpace.scaledLine P.a).orthogonalSum
        (P.kTernaryData ha).space)
      P.kData.lattice
      (product (BONG.unaryModelLattice (K := K))
        (P.kTernaryData ha).lattice) := by
  let split := unitGeneralPlaneSplittingIsometry
    P.a P.kData.leftTail P.kData.left_nondegenerate ha
  let keep := Isometry.refl P.kData.rightSpace
    (hyperbolicPlaneLattice (K := K))
  let splitFirst := split.orthogonalProductBasic keep
  let associate : Isometry
      (((QuadraticSpace.scaledLine P.a).orthogonalSum
        (QuadraticSpace.scaledLine
          (unitGeneralPlaneTail P.a P.kData.leftTail
            P.kData.left_nondegenerate))).orthogonalSum
        P.kData.rightSpace)
      ((QuadraticSpace.scaledLine P.a).orthogonalSum
        ((QuadraticSpace.scaledLine
          (unitGeneralPlaneTail P.a P.kData.leftTail
            P.kData.left_nondegenerate)).orthogonalSum
          P.kData.rightSpace))
      (product
        (product (BONG.unaryModelLattice (K := K))
          (BONG.unaryModelLattice (K := K)))
        (hyperbolicPlaneLattice (K := K)))
      (product (BONG.unaryModelLattice (K := K))
        (product (BONG.unaryModelLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))) :=
    orthogonalProductAssoc
  exact splitFirst.trans associate

end Omeara9318RankFourModelParameters

end Lattice

end Bong
