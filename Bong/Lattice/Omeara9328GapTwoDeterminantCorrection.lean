/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328GapTwoScaleOne

/-!
# O'Meara 93:28, Step 7: determinant correction

This file completes the two 93:19 exchanges used when the normalized norm
orders differ by two and the relative second scale has order one.  The first
exchange corrects the determinant of the quaternary head.  Its remaining
binary plane is then exchanged against the second component, leaving a
standard hyperbolic plane which can be cancelled by 93:14.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem.GapTwoErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.GapTwoErrorData z)

/-- The second 93:19 exchange.  After swapping the remaining plane from the
head exchange, adding `-coefficient` kills its first diagonal entry. -/
noncomputable def tailExchangeSetup
    (hunit : IsValuationUnit K (1 + z)) :
    Omeara9319ExchangeSetup S.targetSecondNormalized
      (S.targetJordan.component 1).lattice S.relativeSecondScale := by
  apply Omeara9319ExchangeSetup.ofRepresentedScalar
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.coefficient (-(D.firstGenerator : K)) (-D.coefficient)
  · exact D.coefficient_integral
  · exact (IntegerRing K).neg_mem (D.firstGenerator : K)
      D.firstGenerator_integral
  · exact S.relativeSecondScale_isInMaximalIdeal
  · have heq :
        D.coefficient * (-(D.firstGenerator : K)) - 1 = -(1 + z) := by
      calc
        D.coefficient * (-(D.firstGenerator : K)) - 1 =
            -(1 + (D.firstGenerator : K) * D.coefficient) := by ring
        _ = -(1 + z) :=
          congrArg (fun t : K ↦ -(1 + t)) D.error_eq.symm
    rw [heq, IsValuationUnit, ord_neg]
    exact hunit
  · exact neg_mem_normGroupSet S.targetSecondNormalized
      (S.targetJordan.component 1).lattice
      D.coefficient_mem_targetSecond

@[simp]
theorem tailExchangeSetup_alpha
    (hunit : IsValuationUnit K (1 + z)) :
    (D.tailExchangeSetup hunit).alpha = D.coefficient :=
  rfl

@[simp]
theorem tailExchangeSetup_beta
    (hunit : IsValuationUnit K (1 + z)) :
    (D.tailExchangeSetup hunit).beta = -(D.firstGenerator : K) :=
  rfl

@[simp]
theorem tailExchangeSetup_delta
    (hunit : IsValuationUnit K (1 + z)) :
    (D.tailExchangeSetup hunit).delta = -D.coefficient :=
  rfl

theorem tailExchangeSetup_newCoefficient_zero
    (hunit : IsValuationUnit K (1 + z)) :
    (D.tailExchangeSetup hunit).alpha +
        (S.relativeSecondScale : K) *
          (D.tailExchangeSetup hunit).gamma = 0 := by
  rw [← (D.tailExchangeSetup hunit).delta_eq]
  simp

/-- The complete second-component shift. -/
noncomputable def tailShift
    (hunit : IsValuationUnit K (1 + z)) :
    Omeara9319ExchangeSetup.Omeara9319Data
      (D.tailExchangeSetup hunit) :=
  (D.tailExchangeSetup hunit).coefficientShift
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)

noncomputable abbrev newTail
    (hunit : IsValuationUnit K (1 + z)) : QuadraticSpace K
      ((D.tailShift hunit).splitting.decomposition.component 1).carrier :=
  (D.tailShift hunit).splitting.decomposition.component 1 |>.space

noncomputable abbrev newTailLattice
    (hunit : IsValuationUnit K (1 + z)) : Lattice K
      ((D.tailShift hunit).splitting.decomposition.component 1).carrier :=
  (D.tailShift hunit).splitting.decomposition.component 1 |>.lattice

theorem tailExchangeComplement_normIdeal_le
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.tailExchangeSetup hunit).exchangeComplement
        (hyperbolicPlaneLattice (K := K)) ≤
      principalIdeal (K := K) (D.secondGenerator : K) := by
  apply Omeara9319ExchangeSetup.exchangeComplement_normIdeal_le_of_newCoefficient_zero
    (D.tailExchangeSetup hunit)
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.secondGenerator D.secondGenerator_targetSecond
    (D.tailExchangeSetup_newCoefficient_zero hunit)
  · simpa using D.coefficient_mem_secondGeneratorIdeal
  · have h :=
      (principalIdeal (K := K) (D.secondGenerator : K)).neg_mem
        D.firstGenerator_mul_relativeScale_sq_mem_secondGeneratorIdeal
    have heq :
        (D.tailExchangeSetup hunit).beta *
            (S.relativeSecondScale : K) ^ 2 =
          -((D.firstGenerator : K) *
            (S.relativeSecondScale : K) ^ 2) := by
      rw [D.tailExchangeSetup_beta hunit]
      ring
    rw [heq]
    exact h

theorem newTail_secondGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    IsNormGeneratorValue (D.newTail hunit) (D.newTailLattice hunit)
      D.secondGenerator := by
  let E := D.tailExchangeSetup hunit
  exact E.coefficientShift_complement_normGenerator_of_exchangeComplement_le
    S.targetSecondNormalized_modular
    (by rw [S.targetSecondNormalized_finrank]; omega)
    D.secondGenerator D.secondGenerator_targetSecond
    (D.tailExchangeComplement_normIdeal_le hunit)

theorem newTail_finrank
    (hunit : IsValuationUnit K (1 + z)) :
    finrank K ((D.tailShift hunit).splitting.decomposition.component 1).carrier =
      4 := by
  rw [(D.tailShift hunit).splitting.complement_finrank]
  letI : Module.Finite K (S.targetJordan.component 1).carrier :=
    (S.targetJordan.component 1).lattice.moduleFinite
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    S.targetSecondNormalized_finrank]

/-- The exchanged head complement is still a quaternary unimodular
component. -/
theorem correctedHead_unimodular
    (hunit : IsValuationUnit K (1 + z)) :
    IsModular (D.correctedHead hunit) (D.correctedHeadLattice hunit)
      (1 : Kˣ) :=
  (D.headShift hunit).splitting.complement_modular

/-- The new plane in the first exchange contributes the determinant factor
`-(1+z)`. -/
theorem headNewPlane_determinantClass
    (hunit : IsValuationUnit K (1 + z))
    (epsilon : Kˣ) (hepsilon : (epsilon : K) = 1 + z) :
    determinantClass (D.headExchangeSetup hunit).newPlane
        (hyperbolicPlaneLattice (K := K)) =
      unitSquareClass K ((-1 : Kˣ) * epsilon) := by
  unfold Omeara9319ExchangeSetup.newPlane
  rw [determinantClass_omearaGeneralPlane]
  apply congrArg (unitSquareClass K)
  apply Units.ext
  change
    ((D.headExchangeSetup hunit).alpha +
          ((1 : Kˣ) : K) * (D.headExchangeSetup hunit).gamma) *
        (D.headExchangeSetup hunit).beta - 1 =
      ((-1 : Kˣ) * epsilon : Kˣ)
  rw [D.headExchangeSetup_newCoefficient hunit,
    D.headExchangeSetup_beta hunit]
  simp only [Units.val_mul, Units.val_neg, Units.val_one]
  rw [show -(D.firstGenerator : K) * D.coefficient =
      -((D.firstGenerator : K) * D.coefficient) by ring,
    ← D.error_eq, hepsilon]
  ring

/-- The old plane in the first exchange has determinant class `-1`. -/
theorem headOldPlane_determinantClass
    (hunit : IsValuationUnit K (1 + z)) :
    determinantClass (D.headExchangeSetup hunit).oldPlane
        (hyperbolicPlaneLattice (K := K)) =
      unitSquareClass K (-1 : Kˣ) := by
  unfold Omeara9319ExchangeSetup.oldPlane
  rw [determinantClass_omearaGeneralPlane]
  apply congrArg (unitSquareClass K)
  apply Units.ext
  simp

set_option maxHeartbeats 1000000 in
/-- The first 93:19 complement has determinant class one.  The larger
heartbeat budget is needed to normalize the two dependent orthogonal-product
carrier types in the determinant identity. -/
theorem correctedHead_determinantClass_eq_one
    (hunit : IsValuationUnit K (1 + z))
    (epsilon : Kˣ) (hepsilon : (epsilon : K) = 1 + z)
    (hdet : determinantClass S.targetFirstNormalized
        (S.targetJordan.component 0).lattice =
      unitSquareClass K epsilon) :
    determinantClass (D.correctedHead hunit) (D.correctedHeadLattice hunit) =
      1 := by
  have hshift := determinantClass_eq_of_isometry
    (D.headShift hunit).shifted
  rw [determinantClass_orthogonalProduct,
    determinantClass_orthogonalProduct,
    D.headOldPlane_determinantClass hunit,
    D.headNewPlane_determinantClass hunit epsilon hepsilon,
    hdet, unitSquareClass_mul] at hshift
  let aClass : UnitSquareClass K :=
    unitSquareClass K (-1 : Kˣ) * unitSquareClass K epsilon
  calc
    determinantClass (D.correctedHead hunit) (D.correctedHeadLattice hunit) =
        1 * determinantClass (D.correctedHead hunit)
          (D.correctedHeadLattice hunit) :=
      (@one_mul (UnitSquareClass K) _ _).symm
    _ = (aClass⁻¹ * aClass) * determinantClass (D.correctedHead hunit)
          (D.correctedHeadLattice hunit) := by rw [inv_mul_cancel]
    _ = aClass⁻¹ * (aClass * determinantClass (D.correctedHead hunit)
          (D.correctedHeadLattice hunit)) := by rw [mul_assoc]
    _ = aClass⁻¹ * aClass := by
      rw [show aClass * determinantClass (D.correctedHead hunit)
          (D.correctedHeadLattice hunit) = aClass by
        simpa only [aClass] using hshift.symm]
    _ = 1 := inv_mul_cancel _

/-- The coefficient used to create the first old plane belongs to the
scale-one truncation of the normalized target head. -/
theorem negCoefficient_mem_targetFirst_scaleTruncation :
    -D.coefficient ∈ normGroupSet S.targetFirstNormalized
      (omearaScaleTruncation S.targetFirstNormalized
        (S.targetJordan.component 0).lattice (1 : Kˣ)) := by
  rw [omearaScaleTruncation_eq_of_isModular
    S.targetFirstNormalized_unimodular]
  exact neg_mem_normGroupSet S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
    D.coefficient_mem_targetFirst

/-- A 93:13 move changes the adjoined hyperbolic plane into `A(c,0)`
while leaving the old target head fixed. -/
noncomputable def insertCoefficient :
    Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized)
      (((QuadraticSpace.omearaPlane D.coefficient).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (S.targetJordan.component 0).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (S.targetJordan.component 0).lattice) := by
  let f := omeara9313 S.targetFirstNormalized
    (S.targetJordan.component 0).lattice (1 : Kˣ)
    D.coefficient (-D.coefficient)
    D.negCoefficient_mem_targetFirst_scaleTruncation
  simpa only [Units.val_inv_eq_inv_val, Units.val_one, inv_one, one_mul,
    add_neg_cancel] using f

/-- Identify the old plane of the first exchange with `A(c,0)`. -/
noncomputable def headOldPlaneToPositiveCoefficient
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry (D.headExchangeSetup hunit).oldPlane
      ((QuadraticSpace.omearaPlane D.coefficient).rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let swap := omearaGeneralPlaneSwapLatticeIsometry
    (0 : K) D.coefficient (by simp)
  let identify := omearaGeneralPlaneZeroRightLatticeIsometry D.coefficient
  let addScale :=
    (Isometry.rescaleUnitOne (QuadraticSpace.omearaPlane D.coefficient)
      (hyperbolicPlaneLattice (K := K))).symm
  have h : Isometry
      (QuadraticSpace.omearaGeneralPlane 0 D.coefficient (by simp))
      ((QuadraticSpace.omearaPlane D.coefficient).rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    swap.trans (identify.trans addScale)
  simpa only [Omeara9319ExchangeSetup.oldPlane,
    D.headExchangeSetup_alpha hunit,
    D.headExchangeSetup_beta hunit] using h

/-- Swapping coordinates identifies the new head-exchange plane with the
old plane of the tail exchange. -/
noncomputable def headNewPlaneToTailOldPlane
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry (D.headExchangeSetup hunit).newPlane
      (D.tailExchangeSetup hunit).oldPlane
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let f := omearaGeneralPlaneSwapLatticeIsometry
    (-(D.firstGenerator : K)) D.coefficient (by
      have h := (D.headExchangeSetup hunit).new_determinant_unit
      have h' : IsValuationUnit K
          (-(D.firstGenerator : K) * D.coefficient - 1) := by
        simpa only [D.headExchangeSetup_newCoefficient hunit,
          D.headExchangeSetup_beta hunit] using h
      exact sub_ne_zero.mp
        (omearaExchange_ne_zero_of_isValuationUnit h'))
  simpa only [Omeara9319ExchangeSetup.newPlane,
    Omeara9319ExchangeSetup.oldPlane,
    D.headExchangeSetup_newCoefficient hunit,
    D.headExchangeSetup_beta hunit,
    D.tailExchangeSetup_alpha hunit,
    D.tailExchangeSetup_beta hunit] using f

/-- After the second exchange the remaining displayed plane is
`A(0,-delta)`; swapping coordinates gives `A(-delta,0)`. -/
noncomputable def tailNewPlaneToNegativeGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry (D.tailExchangeSetup hunit).newPlane
      ((QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
        |>.rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let swap := omearaGeneralPlaneSwapLatticeIsometry
    (0 : K) (-(D.firstGenerator : K)) (by simp)
  let identify :=
    omearaGeneralPlaneZeroRightLatticeIsometry (-(D.firstGenerator : K))
  let addScale :=
    (Isometry.rescaleUnitOne
      (QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
      (hyperbolicPlaneLattice (K := K))).symm
  have h : Isometry
      (QuadraticSpace.omearaGeneralPlane 0 (-(D.firstGenerator : K))
        (by simp))
      ((QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
        |>.rescaleUnit (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    swap.trans (identify.trans addScale)
  simpa only [Omeara9319ExchangeSetup.newPlane,
    D.tailExchangeSetup_newCoefficient_zero hunit,
    D.tailExchangeSetup_beta hunit] using h

/-- The negative first norm generator is represented by the corrected head. -/
theorem negFirstGenerator_mem_correctedHead
    (hunit : IsValuationUnit K (1 + z)) :
    -(D.firstGenerator : K) ∈
      normGroupSet (D.correctedHead hunit) (D.correctedHeadLattice hunit) := by
  apply (D.headShift hunit).normGroup_subset
  exact neg_mem_normGroupSet S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
    D.firstGenerator_targetFirst.1

/-- Negating the second coordinate identifies the binary exchange complement
with the general plane `A(delta,-c)`. -/
noncomputable def headExchangeComplementToGeneralPlane
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry (D.headExchangeSetup hunit).exchangeComplement
      (QuadraticSpace.omearaGeneralPlane (D.firstGenerator : K)
        (-D.coefficient) (by
          have h := (D.headExchangeSetup hunit).new_determinant_unit
          have h' : IsValuationUnit K
              ((D.firstGenerator : K) * (-D.coefficient) - 1) := by
            rw [show (D.firstGenerator : K) * (-D.coefficient) - 1 =
                -(D.firstGenerator : K) * D.coefficient - 1 by ring]
            simpa only [D.headExchangeSetup_newCoefficient hunit,
              D.headExchangeSetup_beta hunit] using h
          exact sub_ne_zero.mp
            (omearaExchange_ne_zero_of_isValuationUnit h')))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv :=
    { toFun := fun x ↦ ![x 0, -x 1]
      invFun := fun x ↦ ![x 0, -x 1]
      left_inv := by
        intro x
        funext i
        fin_cases i <;> simp
      right_inv := by
        intro x
        funext i
        fin_cases i <;> simp
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [add_comm]
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp }
  map_bilin x y := by
    unfold Omeara9319ExchangeSetup.exchangeComplement
    rw [QuadraticSpace.omearaExchangeComplement_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply]
    simp only [D.headExchangeSetup_alpha hunit,
      D.headExchangeSetup_beta hunit,
      D.headExchangeSetup_gamma hunit,
      Units.val_one, one_mul, neg_mul, neg_neg]
    simp
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx0, (IntegerRing K).toSubring.neg_mem hx1⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx0, by simpa using (IntegerRing K).toSubring.neg_mem hx1⟩

/-- The exchange complement adds no new values to the old first norm group. -/
theorem headExchangeComplement_normGroupSet_subset_targetFirst
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet (D.headExchangeSetup hunit).exchangeComplement
        (hyperbolicPlaneLattice (K := K)) ⊆
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  rw [← normGroupSet_eq_of_latticeIsometry
    (D.headExchangeComplementToGeneralPlane hunit)]
  apply normGroupSet_omearaGeneralPlane_subset_of_coefficients_mem
  · exact D.firstGenerator_integral
  · exact (IntegerRing K).neg_mem D.coefficient D.coefficient_integral
  · have h := (D.headExchangeSetup hunit).new_determinant_unit
    rw [show (D.firstGenerator : K) * (-D.coefficient) - 1 =
        -(D.firstGenerator : K) * D.coefficient - 1 by ring]
    simpa only [D.headExchangeSetup_newCoefficient hunit,
      D.headExchangeSetup_beta hunit] using h
  · exact S.targetFirstNormalized_unimodular
  · rw [S.targetFirstNormalized_finrank]
    omega
  · exact D.firstGenerator_targetFirst.1
  · exact neg_mem_normGroupSet S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      D.coefficient_mem_targetFirst

/-- The ambient lattice split by the first 93:19 exchange has exactly the
old first norm group. -/
theorem headExchangeAmbient_normGroupSet_eq_targetFirst
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet (D.headExchangeAmbient hunit)
        (D.headExchangeAmbientLattice hunit) =
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
  ext a
  rw [mem_normGroupSet_orthogonalProduct_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact add_mem_normGroupSet S.targetFirstNormalized
      (S.targetJordan.component 0).lattice
      (D.headExchangeComplement_normGroupSet_subset_targetFirst hunit hx) hy
  · intro ha
    exact ⟨0, zero_mem_normGroupSet
      (D.headExchangeSetup hunit).exchangeComplement
      (hyperbolicPlaneLattice (K := K)), a, ha, by simp⟩

/-- The corrected head has precisely the source first norm group. -/
theorem correctedHead_normGroupSet_eq_source
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      normGroupSet (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) := by
  exact S.firstNormalized_normGroupSet_eq.trans <|
    (D.headExchangeAmbient_normGroupSet_eq_targetFirst hunit).symm.trans <|
      (D.headShift_complement_normGroupSet_eq hunit).symm

theorem correctedHead_twoScaleIdeal_eq_source
    (hunit : IsValuationUnit K (1 + z)) :
    twoScaleIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      twoScaleIdeal (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) := by
  rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      S.sourceFirstNormalized_unimodular
      (by rw [S.sourceFirstNormalized_finrank]; omega),
    twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      (D.correctedHead_unimodular hunit)
      (by rw [D.headShift_complement_finrank hunit]; omega)]

theorem correctedHead_weightIdeal_eq_source
    (hunit : IsValuationUnit K (1 + z)) :
    weightIdeal S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdeal (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) := by
  exact weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    D.firstGenerator_sourceFirst
    ⟨D.firstGenerator, D.correctedHead_firstGenerator hunit⟩
    (D.correctedHead_normGroupSet_eq_source hunit)
    (D.correctedHead_twoScaleIdeal_eq_source hunit)

theorem correctedHead_weightIdealOrder_eq_source
    (hunit : IsValuationUnit K (1 + z)) :
    weightIdealOrder S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice =
      weightIdealOrder (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) := by
  apply powerIdeal_order_eq_of_eq (K := K)
  calc
    powerIdeal (K := K)
        (weightIdealOrder S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice) =
        weightIdeal S.sourceFirstNormalized
          (S.sourceJordan.component 0).lattice :=
      (weightIdeal_eq_powerIdeal _ _).symm
    _ = weightIdeal (D.correctedHead hunit)
          (D.correctedHeadLattice hunit) :=
      D.correctedHead_weightIdeal_eq_source hunit
    _ = powerIdeal (K := K)
        (weightIdealOrder (D.correctedHead hunit)
          (D.correctedHeadLattice hunit)) :=
      weightIdeal_eq_powerIdeal _ _

theorem correctedHead_parity_iff_source
    (hunit : IsValuationUnit K (1 + z)) :
    Odd S.firstNormWeightParity ↔
      Odd (ordUnit K D.firstGenerator +
        weightIdealOrder (D.correctedHead hunit)
          (D.correctedHeadLattice hunit)) := by
  have horder : ordUnit K D.firstGenerator =
      ordUnit K S.firstNormGenerator := by
    apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact D.firstGenerator_sourceFirst.2.symm.trans
      S.firstNormGenerator_source.2
  unfold Omeara9328RankFourReductionSystem.firstNormWeightParity
  rw [horder, D.correctedHead_weightIdealOrder_eq_source hunit]

/-- The first coordinate of the exchange complement represents the coherent
first norm generator used in condition 93:28(iii). -/
theorem headExchangeComplementRepresentsFirstGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    (D.headExchangeSetup hunit).exchangeComplement.Represents
      (QuadraticSpace.scaledLine D.firstGenerator) := by
  refine ⟨{
    toLinearMap :=
      { toFun := fun x ↦ ![x, 0]
        map_add' := by
          intro x y
          funext i
          fin_cases i <;> simp
        map_smul' := by
          intro c x
          funext i
          fin_cases i <;> simp }
    injective := ?_
    map_bilin := ?_ }⟩
  · intro x y hxy
    have hzero := congrFun hxy 0
    simpa using hzero
  · intro x y
    unfold Omeara9319ExchangeSetup.exchangeComplement
    rw [QuadraticSpace.omearaExchangeComplement_bilin_apply,
      QuadraticSpace.scaledLine_bilin_apply]
    simp only [D.headExchangeSetup_alpha hunit,
      D.headExchangeSetup_beta hunit,
      D.headExchangeSetup_gamma hunit,
      Units.val_one, one_mul, neg_mul, neg_neg]
    simp

set_option maxHeartbeats 1000000 in
/-- Once the corrected head is hyperbolic over the field, equality of norm
groups upgrades the field isometry to an integral lattice isometry. -/
noncomputable def sourceToCorrectedHeadIsometryOfHyperbolic
    (hunit : IsValuationUnit K (1 + z))
    (htower : (D.correctedHead hunit).IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)) :
    Isometry S.sourceFirstNormalized (D.correctedHead hunit)
      (S.sourceJordan.component 0).lattice
      (D.correctedHeadLattice hunit) := by
  let fieldIsometry := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    (Classical.choice htower).symm
  exact latticeIsometryToUnimodularModel
    S.sourceFirstNormalized_unimodular
    (D.correctedHead_unimodular hunit)
    fieldIsometry (D.correctedHead_normGroupSet_eq_source hunit)

/-- The determinant-corrected Step-7 head in the even parity branch is the
rank-four case of O'Meara 93:18(ii). -/
noncomputable def correctedHeadEvenData
    (hunit : IsValuationUnit K (1 + z))
    (heven : Even S.firstNormWeightParity) :
    Omeara9318vData (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) (1 : Kˣ) := by
  apply omeara9318iiData (D.correctedHead_unimodular hunit)
    (by rw [D.headShift_complement_finrank hunit]; omega)
    D.firstGenerator (D.correctedHead_firstGenerator hunit)
  have hnotSource : ¬ Odd S.firstNormWeightParity :=
    Int.not_odd_iff_even.mpr heven
  have hnotCorrected : ¬ Odd
      (ordUnit K D.firstGenerator +
        weightIdealOrder (D.correctedHead hunit)
          (D.correctedHeadLattice hunit)) := by
    intro hodd
    exact hnotSource ((D.correctedHead_parity_iff_source hunit).mpr hodd)
  exact Int.not_odd_iff_even.mp hnotCorrected

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 3000000 in
/-- The even determinant-one corrected head is a hyperbolic tower over the
field. -/
noncomputable def correctedHeadEvenToHyperbolicTowerSpaceIsometry
    (hunit : IsValuationUnit K (1 + z))
    (heven : Even S.firstNormWeightParity)
    (hdet : determinantClass (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) = 1) :
    QuadraticSpace.Isometry (D.correctedHead hunit)
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let E := D.correctedHeadEvenData hunit heven
  exact E.toHyperbolicTowerSpaceIsometry
    (D.headShift_complement_finrank hunit) hdet

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 3000000 in
/-- Integral source-to-head alignment in the even Step-7 branch. -/
noncomputable def sourceToCorrectedHeadEvenIsometry
    (hunit : IsValuationUnit K (1 + z))
    (heven : Even S.firstNormWeightParity)
    (hdet : determinantClass (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) = 1) :
    Isometry S.sourceFirstNormalized (D.correctedHead hunit)
      (S.sourceJordan.component 0).lattice
      (D.correctedHeadLattice hunit) := by
  apply D.sourceToCorrectedHeadIsometryOfHyperbolic hunit
  exact ⟨D.correctedHeadEvenToHyperbolicTowerSpaceIsometry
    hunit heven hdet⟩

/-- Determinant-one 93:18(vi) data for the odd Step-7 corrected head. -/
noncomputable def correctedHeadOddDeterminantOneData
    (hunit : IsValuationUnit K (1 + z))
    (hodd : Odd S.firstNormWeightParity)
    (hdet : determinantClass (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) = 1) :
    Omeara9318viOddData (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) D.firstGenerator := by
  apply omeara9318viOddData (D.correctedHead_unimodular hunit)
    (D.headShift_complement_finrank hunit) D.firstGenerator
    (D.correctedHead_firstGenerator hunit)
  · exact (D.correctedHead_parity_iff_source hunit).mp hodd
  · exact hdet

/-- The final 93:13 move turns `A(-delta,0)` back into the common
hyperbolic plane. -/
noncomputable def absorbNegativeGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry
      (((QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
        |>.rescaleUnit (1 : Kˣ)).orthogonalSum (D.correctedHead hunit))
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum (D.correctedHead hunit))
      (product (hyperbolicPlaneLattice (K := K))
        (D.correctedHeadLattice hunit))
      (product (hyperbolicPlaneLattice (K := K))
        (D.correctedHeadLattice hunit)) := by
  have hmem : -(D.firstGenerator : K) ∈
      normGroupSet (D.correctedHead hunit)
        (omearaScaleTruncation (D.correctedHead hunit)
          (D.correctedHeadLattice hunit) (1 : Kˣ)) := by
    rw [omearaScaleTruncation_eq_of_isModular
      (D.correctedHead_unimodular hunit)]
    exact D.negFirstGenerator_mem_correctedHead hunit
  let f := omeara9313 (D.correctedHead hunit)
    (D.correctedHeadLattice hunit) (1 : Kˣ)
    0 (-(D.firstGenerator : K)) hmem
  simpa only [Units.val_inv_eq_inv_val, Units.val_one, inv_one, one_mul,
    zero_add] using f

/-- The complete stabilized Step-7 calculation before applying 93:14. -/
noncomputable def stabilizedPairIsometry
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          ((D.correctedHead hunit).orthogonalSum (D.newTail hunit)))
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice))
      (product (hyperbolicPlaneLattice (K := K))
        (product (D.correctedHeadLattice hunit)
          (D.newTailLattice hunit))) := by
  let firstIdentity := Isometry.refl S.targetFirstNormalized
    (S.targetJordan.component 0).lattice
  let secondIdentity := Isometry.refl S.targetSecondNormalized
    (S.targetJordan.component 1).lattice
  let correctedIdentity := Isometry.refl (D.correctedHead hunit)
    (D.correctedHeadLattice hunit)
  let newTailIdentity := Isometry.refl (D.newTail hunit)
    (D.newTailLattice hunit)
  let exposeFirst : Isometry
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized))
      ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (product (S.targetJordan.component 0).lattice
          (S.targetJordan.component 1).lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    orthogonalProductAssoc.symm
  let changeCoefficient : Isometry
      ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      ((((QuadraticSpace.omearaPlane D.coefficient).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    D.insertCoefficient.orthogonalProductBasic secondIdentity
  let identifyHeadOld : Isometry
      ((((QuadraticSpace.omearaPlane D.coefficient).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum S.targetFirstNormalized).orthogonalSum
          S.targetSecondNormalized)
      (((D.headExchangeSetup hunit).oldPlane.orthogonalSum
          S.targetFirstNormalized).orthogonalSum S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice) :=
    ((D.headOldPlaneToPositiveCoefficient hunit).symm
      |>.orthogonalProductBasic firstIdentity)
      |>.orthogonalProductBasic secondIdentity
  let shiftHead : Isometry
      (((D.headExchangeSetup hunit).oldPlane.orthogonalSum
          S.targetFirstNormalized).orthogonalSum S.targetSecondNormalized)
      (((D.headExchangeSetup hunit).newPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 0).lattice)
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (S.targetJordan.component 1).lattice) :=
    (D.headShift hunit).shifted.orthogonalProductBasic secondIdentity
  let identifyTailOld : Isometry
      (((D.headExchangeSetup hunit).newPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum S.targetSecondNormalized)
      (((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum S.targetSecondNormalized)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (S.targetJordan.component 1).lattice)
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (S.targetJordan.component 1).lattice) :=
    (D.headNewPlaneToTailOldPlane hunit
      |>.orthogonalProductBasic correctedIdentity)
      |>.orthogonalProductBasic secondIdentity
  let associateOld : Isometry
      (((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum S.targetSecondNormalized)
      ((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
        ((D.correctedHead hunit).orthogonalSum S.targetSecondNormalized))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (S.targetJordan.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product (D.correctedHeadLattice hunit)
          (S.targetJordan.component 1).lattice)) :=
    orthogonalProductAssoc
  let rotateOld : Isometry
      ((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
        ((D.correctedHead hunit).orthogonalSum S.targetSecondNormalized))
      (((D.correctedHead hunit).orthogonalSum
          (D.tailExchangeSetup hunit).oldPlane).orthogonalSum
            S.targetSecondNormalized)
      (product (hyperbolicPlaneLattice (K := K))
        (product (D.correctedHeadLattice hunit)
          (S.targetJordan.component 1).lattice))
      (product
        (product (D.correctedHeadLattice hunit)
          (hyperbolicPlaneLattice (K := K)))
        (S.targetJordan.component 1).lattice) :=
    orthogonalProductRotateLeft
  let hideOld : Isometry
      (((D.correctedHead hunit).orthogonalSum
          (D.tailExchangeSetup hunit).oldPlane).orthogonalSum
            S.targetSecondNormalized)
      ((D.correctedHead hunit).orthogonalSum
        ((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
          S.targetSecondNormalized))
      (product
        (product (D.correctedHeadLattice hunit)
          (hyperbolicPlaneLattice (K := K)))
        (S.targetJordan.component 1).lattice)
      (product (D.correctedHeadLattice hunit)
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 1).lattice)) :=
    orthogonalProductAssoc
  let shiftTail : Isometry
      ((D.correctedHead hunit).orthogonalSum
        ((D.tailExchangeSetup hunit).oldPlane.orthogonalSum
          S.targetSecondNormalized))
      ((D.correctedHead hunit).orthogonalSum
        ((D.tailExchangeSetup hunit).newPlane.orthogonalSum
          (D.newTail hunit)))
      (product (D.correctedHeadLattice hunit)
        (product (hyperbolicPlaneLattice (K := K))
          (S.targetJordan.component 1).lattice))
      (product (D.correctedHeadLattice hunit)
        (product (hyperbolicPlaneLattice (K := K))
          (D.newTailLattice hunit))) :=
    correctedIdentity.orthogonalProductBasic (D.tailShift hunit).shifted
  let rotateNew : Isometry
      ((D.correctedHead hunit).orthogonalSum
        ((D.tailExchangeSetup hunit).newPlane.orthogonalSum
          (D.newTail hunit)))
      (((D.tailExchangeSetup hunit).newPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum (D.newTail hunit))
      (product (D.correctedHeadLattice hunit)
        (product (hyperbolicPlaneLattice (K := K))
          (D.newTailLattice hunit)))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit)) :=
    orthogonalProductRotateLeft
  let identifyNegative : Isometry
      (((D.tailExchangeSetup hunit).newPlane.orthogonalSum
          (D.correctedHead hunit)).orthogonalSum (D.newTail hunit))
      (((((QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
          |>.rescaleUnit (1 : Kˣ)).orthogonalSum (D.correctedHead hunit)))
        |>.orthogonalSum (D.newTail hunit))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit)) :=
    (D.tailNewPlaneToNegativeGenerator hunit
      |>.orthogonalProductBasic correctedIdentity)
      |>.orthogonalProductBasic newTailIdentity
  let absorb : Isometry
      (((((QuadraticSpace.omearaPlane (-(D.firstGenerator : K)))
          |>.rescaleUnit (1 : Kˣ)).orthogonalSum (D.correctedHead hunit)))
        |>.orthogonalSum (D.newTail hunit))
      (((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
          |>.orthogonalSum (D.correctedHead hunit)))
        |>.orthogonalSum (D.newTail hunit))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit)) :=
    (D.absorbNegativeGenerator hunit)
      |>.orthogonalProductBasic newTailIdentity
  let hideHead : Isometry
      (((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
          |>.orthogonalSum (D.correctedHead hunit)))
        |>.orthogonalSum (D.newTail hunit))
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ))
        |>.orthogonalSum
          ((D.correctedHead hunit).orthogonalSum (D.newTail hunit)))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (D.correctedHeadLattice hunit))
        (D.newTailLattice hunit))
      (product (hyperbolicPlaneLattice (K := K))
        (product (D.correctedHeadLattice hunit)
          (D.newTailLattice hunit))) :=
    orthogonalProductAssoc
  exact exposeFirst.trans <| changeCoefficient.trans <|
    identifyHeadOld.trans <| shiftHead.trans <| identifyTailOld.trans <|
      associateOld.trans <| rotateOld.trans <| hideOld.trans <|
        shiftTail.trans <| rotateNew.trans <| identifyNegative.trans <|
          absorb.trans hideHead

/-- Cancel the common normalized hyperbolic plane by O'Meara 93:14. -/
noncomputable def normalizedPairIsometry
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry
      (S.targetFirstNormalized.orthogonalSum S.targetSecondNormalized)
      ((D.correctedHead hunit).orthogonalSum (D.newTail hunit))
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product (D.correctedHeadLattice hunit)
        (D.newTailLattice hunit)) := by
  exact omeara9314_scaled_of_isometric_summand (1 : Kˣ)
    (scaledZeroOmearaPlaneLatticeIsometry (1 : Kˣ))
    (scaledZeroOmearaPlaneLatticeIsometry (1 : Kˣ))
    (D.stabilizedPairIsometry hunit)

end Omeara9328RankFourReductionSystem.GapTwoErrorData

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- Condition 93:28(iii) at the first boundary, transported to the
normalized heads and the coherent first norm generator. -/
theorem normalizedConditionIIIRepresentation
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    (S.targetFirstNormalized.orthogonalSum
        (QuadraticSpace.scaledLine
          (S.firstNormalizedNormGeneratorWith A))).Represents
      S.sourceFirstNormalized := by
  let sourcePrefix :=
    S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1
  let targetPrefix :=
    S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1
  letI : Module.Finite K sourcePrefix.carrier := sourcePrefix.lattice.moduleFinite
  letI : Module.Finite K targetPrefix.carrier := targetPrefix.lattice.moduleFinite
  have hindex : boundaryLeftIndex (0 : Fin (n + 1)) =
      (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp [boundaryLeftIndex]
  have hrawRaw := conditions.2.2 (0 : Fin (n + 1)) htrigger
  change
    ((S.targetJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
        |>.orthogonalSum
          (QuadraticSpace.scaledLine
            (A.value (boundaryLeftIndex (0 : Fin (n + 1)))))).Represents
      (S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice 1).space
    at hrawRaw
  have hraw :
      (targetPrefix.space.orthogonalSum
          (QuadraticSpace.scaledLine (A.value 0))).Represents
        sourcePrefix.space := by
    simpa only [hindex] using hrawRaw
  rcases hraw with ⟨f⟩
  let fScaled := f.rescaleUnitBoth S.firstScale⁻¹
  let distribute := QuadraticSpace.rescaleUnitOrthogonalSumIsometry
    targetPrefix.space (QuadraticSpace.scaledLine (A.value 0))
      S.firstScale⁻¹
  let sourcePrefixIso :=
    S.sourceJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry
  let targetPrefixIso :=
    S.targetJordan.toOrthogonalDecomposition
      |>.firstComponentPrefixLatticeIsometry
  let sourceNormalize : QuadraticSpace.Isometry S.sourceFirstNormalized
      (sourcePrefix.space.rescaleUnit S.firstScale⁻¹) := by
    exact sourcePrefixIso.toQuadraticSpaceIsometry.rescaleUnitBoth
      S.firstScale⁻¹
  let targetNormalize : QuadraticSpace.Isometry
      (targetPrefix.space.rescaleUnit S.firstScale⁻¹)
      S.targetFirstNormalized := by
    exact (targetPrefixIso.toQuadraticSpaceIsometry.rescaleUnitBoth
      S.firstScale⁻¹).symm
  let lineNormalize : QuadraticSpace.Isometry
      ((QuadraticSpace.scaledLine (A.value 0)).rescaleUnit S.firstScale⁻¹)
      (QuadraticSpace.scaledLine
        (S.firstNormalizedNormGeneratorWith A)) := by
    exact QuadraticSpace.scaledLineRescaleUnitIsometry
      S.firstScale⁻¹ (A.value 0)
  let normalizeTarget := distribute.trans
    (targetNormalize.orthogonalSum lineNormalize)
  exact ⟨normalizeTarget.toRepresentation.trans
    (fScaled.trans sourceNormalize.toRepresentation)⟩

/-- Step-7 scalar data specialized to the congruence error supplied by
condition 93:28(i). -/
noncomputable def gapTwoCongruenceErrorData
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    S.GapTwoErrorData
      (S.targetFirstCongruenceError A conditions).error :=
  S.gapTwoErrorData A
    (S.targetFirstCongruenceError A conditions).error hgap hscale
    (S.targetFirstCongruenceError A conditions).error_mem

/-- The concrete congruence error has a valuation-unit `1+z`. -/
theorem gapTwoCongruenceError_one_isValuationUnit
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A) :
    IsValuationUnit K
      (1 + (S.targetFirstCongruenceError A conditions).error) := by
  let C := S.targetFirstCongruenceError A conditions
  rw [← C.errorUnit_coe]
  exact C.errorUnit_isValuationUnit

/-- The corrected Step-7 head has determinant class one. -/
theorem gapTwo_correctedHead_determinantClass_eq_one
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    let C := S.targetFirstCongruenceError A conditions
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    determinantClass
      (D.correctedHead (S.gapTwoCongruenceError_one_isValuationUnit A conditions))
      (D.correctedHeadLattice
        (S.gapTwoCongruenceError_one_isValuationUnit A conditions)) = 1 := by
  let C := S.targetFirstCongruenceError A conditions
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  change determinantClass (D.correctedHead hunit)
    (D.correctedHeadLattice hunit) = 1
  apply D.correctedHead_determinantClass_eq_one hunit
    C.errorUnit C.errorUnit_coe
  change unitSquareClass K
      (determinantUnit S.targetFirstNormalized
        (S.targetJordan.component 0).lattice) =
    unitSquareClass K C.errorUnit
  exact C.unitSquareClass_eq_errorUnit

/-- In the condition-(iii) branch, the determinant-corrected head
represents a hyperbolic plane. -/
theorem gapTwoCorrectedHeadRepresentsHyperbolicOfConditionIII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    (D.correctedHead hunit).Represents
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  change (D.correctedHead hunit).Represents
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
  letI : Module.Finite K (S.sourceJordan.component 0).carrier :=
    (S.sourceJordan.component 0).lattice.moduleFinite
  letI : Module.Finite K (S.targetJordan.component 0).carrier :=
    (S.targetJordan.component 0).lattice.moduleFinite
  letI : Module.Finite K
      ((D.headShift hunit).splitting.decomposition.component 1).carrier :=
    (D.correctedHeadLattice hunit).moduleFinite
  have hcondition := S.normalizedConditionIIIRepresentation
    A conditions htrigger
  have hline : D.firstGenerator =
      S.firstNormalizedNormGeneratorWith A := by
    rfl
  rw [← hline] at hcondition
  rcases hcondition with ⟨sourceInOldLine⟩
  rcases D.headExchangeComplementRepresentsFirstGenerator hunit with
    ⟨lineInExchange⟩
  let replaceLine :=
    (QuadraticSpace.Representation.refl S.targetFirstNormalized).orthogonalSum
      lineInExchange
  let sourceInOldExchange := replaceLine.trans sourceInOldLine
  let swap : QuadraticSpace.Isometry
      (S.targetFirstNormalized.orthogonalSum
        (D.headExchangeSetup hunit).exchangeComplement)
      (D.headExchangeAmbient hunit) :=
    (orthogonalProductSwap
      (q := S.targetFirstNormalized)
      (r := (D.headExchangeSetup hunit).exchangeComplement)
      (L := (S.targetJordan.component 0).lattice)
      (M := hyperbolicPlaneLattice (K := K))).toQuadraticSpaceIsometry
  let targetToSplit := swap.trans
    (D.headShift hunit).splitting.displayedIsometry.toQuadraticSpaceIsometry
  have sourceInSplit :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (D.correctedHead hunit)).Represents S.sourceFirstNormalized :=
    ⟨targetToSplit.toRepresentation.trans sourceInOldExchange⟩
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  let sourceToPair := S.sourceFirstNormalizedHyperbolicTowerIsometry.trans
    pairToTower.symm
  have pairInSplit :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (D.correctedHead hunit)).Represents
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (QuadraticSpace.hyperbolicPlane (1 : Kˣ))) :=
    sourceInSplit.trans ⟨sourceToPair.symm.toRepresentation⟩
  exact QuadraticSpace.orthogonalSumLeftCancelRepresents
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
    (D.correctedHead hunit) pairInSplit

/-- The determinant-one rank-four criterion makes the corrected head the
standard two-plane hyperbolic tower in the condition-(iii) branch. -/
theorem gapTwoCorrectedHeadIsHyperbolicOfConditionIII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    (D.correctedHead hunit).IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  change (D.correctedHead hunit).IsIsometric
    (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)
  letI : Module.Finite K
      ((D.headShift hunit).splitting.decomposition.component 1).carrier :=
    (D.correctedHeadLattice hunit).moduleFinite
  have hpair :=
    QuadraticSpace.rankFour_isIsometric_hyperbolicPair_of_determinantClass_eq_one
      (D.correctedHead hunit) (D.correctedHeadLattice hunit)
      (D.headShift_complement_finrank hunit)
      (S.gapTwo_correctedHead_determinantClass_eq_one
        A conditions hgap hscale)
      (S.gapTwoCorrectedHeadRepresentsHyperbolicOfConditionIII
        A conditions hgap hscale htrigger)
  let hyperbolicToZero :=
    (scaledZeroOmearaPlaneLatticeIsometry (K := K) (1 : Kˣ)).symm
      |>.toQuadraticSpaceIsometry
  let pairToTower :=
    (hyperbolicToZero.orthogonalSum hyperbolicToZero).trans
      (twoZeroPlaneProductToTowerTwoSpaceIsometry (K := K))
  rcases hpair with ⟨f⟩
  exact ⟨f.trans pairToTower⟩

/-- Integral source-to-corrected-head alignment in the condition-(iii)
branch. -/
noncomputable def gapTwoSourceToCorrectedHeadIsometryOfConditionIII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    Isometry S.sourceFirstNormalized (D.correctedHead hunit)
      (S.sourceJordan.component 0).lattice
      (D.correctedHeadLattice hunit) := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  change Isometry S.sourceFirstNormalized (D.correctedHead hunit)
    (S.sourceJordan.component 0).lattice (D.correctedHeadLattice hunit)
  exact D.sourceToCorrectedHeadIsometryOfHyperbolic hunit
    (S.gapTwoCorrectedHeadIsHyperbolicOfConditionIII
      A conditions hgap hscale htrigger)

namespace GapTwoErrorData

variable {S : Omeara9328RankFourReductionSystem J H}
  {z : K} (D : S.GapTwoErrorData z)

/-- Corrected first component at the original Jordan scale. -/
noncomputable abbrev correctedHeadUnnormalized
    (hunit : IsValuationUnit K (1 + z)) : QuadraticSpace K
      ((D.headShift hunit).splitting.decomposition.component 1).carrier :=
  (D.correctedHead hunit).rescaleUnit S.firstScale

/-- Corrected second component at the original Jordan scale. -/
noncomputable abbrev newTailUnnormalized
    (hunit : IsValuationUnit K (1 + z)) : QuadraticSpace K
      ((D.tailShift hunit).splitting.decomposition.component 1).carrier :=
  (D.newTail hunit).rescaleUnit S.firstScale

/-- Undo the first-scale normalization on the complete corrected pair. -/
noncomputable def originalPairIsometry
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry
      ((S.targetJordan.component 0).space.orthogonalSum
        (S.targetJordan.component 1).space)
      ((D.correctedHeadUnnormalized hunit).orthogonalSum
        (D.newTailUnnormalized hunit))
      (product (S.targetJordan.component 0).lattice
        (S.targetJordan.component 1).lattice)
      (product (D.correctedHeadLattice hunit)
        (D.newTailLattice hunit)) := by
  let scaled := (D.normalizedPairIsometry hunit).rescaleUnitBoth S.firstScale
  let distributeSource := rescaleUnitOrthogonalProductIsometry
    S.targetFirstNormalized S.targetSecondNormalized
    (S.targetJordan.component 0).lattice
    (S.targetJordan.component 1).lattice S.firstScale
  let undoFirstRaw := rescaleUnitMulLatticeIsometry
    (S.targetJordan.component 0).space
    (S.targetJordan.component 0).lattice S.firstScale⁻¹ S.firstScale
  let undoFirst : Isometry
      (S.targetFirstNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.targetJordan.component 0).lattice := by
    have hscale : S.firstScale * S.firstScale⁻¹ = (1 : Kˣ) := by simp
    let finish : Isometry
        ((S.targetJordan.component 0).space.rescaleUnit
          (S.firstScale * S.firstScale⁻¹))
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice
        (S.targetJordan.component 0).lattice := by
      simpa only [hscale] using Isometry.rescaleUnitOne
        (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice
    simpa only [targetFirstNormalized] using undoFirstRaw.trans finish
  let undoSecondRaw := rescaleUnitMulLatticeIsometry
    (S.targetJordan.component 1).space
    (S.targetJordan.component 1).lattice S.firstScale⁻¹ S.firstScale
  let undoSecond : Isometry
      (S.targetSecondNormalized.rescaleUnit S.firstScale)
      (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.targetJordan.component 1).lattice := by
    have hscale : S.firstScale * S.firstScale⁻¹ = (1 : Kˣ) := by simp
    let finish : Isometry
        ((S.targetJordan.component 1).space.rescaleUnit
          (S.firstScale * S.firstScale⁻¹))
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice
        (S.targetJordan.component 1).lattice := by
      simpa only [hscale] using Isometry.rescaleUnitOne
        (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice
    simpa only [targetSecondNormalized] using undoSecondRaw.trans finish
  let undoSource := distributeSource.trans
    (undoFirst.orthogonalProductBasic undoSecond)
  let distributeTarget := rescaleUnitOrthogonalProductIsometry
    (D.correctedHead hunit) (D.newTail hunit)
    (D.correctedHeadLattice hunit) (D.newTailLattice hunit) S.firstScale
  exact undoSource.symm.trans (scaled.trans distributeTarget)

theorem firstScale_mul_relativeSecondScale :
    S.firstScale * S.relativeSecondScale =
      S.targetJordan.scaleGenerator 1 := by
  unfold Omeara9328RankFourReductionSystem.firstScale
    Omeara9328RankFourReductionSystem.relativeSecondScale
  rw [S.targetJordan_scaleGenerator]
  group

theorem targetFirst_unscaledNormGenerator :
    IsNormGeneratorValue (S.targetJordan.component 0).space
      (S.targetJordan.component 0).lattice
      (S.firstScale * D.firstGenerator) := by
  have h := D.firstGenerator_targetFirst.unscaleQuadraticUnit
  simpa only [Omeara9328RankFourReductionSystem.targetFirstNormalized,
    inv_inv] using h

theorem targetSecond_unscaledNormGenerator :
    IsNormGeneratorValue (S.targetJordan.component 1).space
      (S.targetJordan.component 1).lattice
      (S.firstScale * D.secondGenerator) := by
  have h := D.secondGenerator_targetSecond.unscaleQuadraticUnit
  simpa only [Omeara9328RankFourReductionSystem.targetSecondNormalized,
    inv_inv] using h

theorem correctedHeadUnnormalized_modular
    (hunit : IsValuationUnit K (1 + z)) :
    IsModular (D.correctedHeadUnnormalized hunit)
      (D.correctedHeadLattice hunit)
      (S.targetJordan.scaleGenerator 0) := by
  have h := (D.correctedHead_unimodular hunit)
    |>.rescaleQuadraticUnit S.firstScale
  simpa only [correctedHeadUnnormalized,
    S.targetJordan_scaleGenerator,
    Omeara9328RankFourReductionSystem.firstScale, mul_one] using h

theorem newTailUnnormalized_modular
    (hunit : IsValuationUnit K (1 + z)) :
    IsModular (D.newTailUnnormalized hunit) (D.newTailLattice hunit)
      (S.targetJordan.scaleGenerator 1) := by
  have h := (D.tailShift hunit).splitting.complement_modular
    |>.rescaleQuadraticUnit S.firstScale
  simpa only [newTailUnnormalized,
    firstScale_mul_relativeSecondScale (S := S)] using h

theorem correctedHeadUnnormalized_normGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    IsNormGeneratorValue (D.correctedHeadUnnormalized hunit)
      (D.correctedHeadLattice hunit)
      (S.firstScale * D.firstGenerator) :=
  (D.correctedHead_firstGenerator hunit).rescaleQuadraticUnit S.firstScale

theorem newTailUnnormalized_normGenerator
    (hunit : IsValuationUnit K (1 + z)) :
    IsNormGeneratorValue (D.newTailUnnormalized hunit)
      (D.newTailLattice hunit)
      (S.firstScale * D.secondGenerator) :=
  (D.newTail_secondGenerator hunit).rescaleQuadraticUnit S.firstScale

theorem correctedHeadUnnormalized_scaleIdeal
    (hunit : IsValuationUnit K (1 + z)) :
    scaleIdeal (D.correctedHeadUnnormalized hunit)
        (D.correctedHeadLattice hunit) =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 0 : K) :=
  (D.correctedHeadUnnormalized_modular hunit).scaleIdeal_eq_principal
    (by rw [D.headShift_complement_finrank hunit]; omega)

theorem newTailUnnormalized_scaleIdeal
    (hunit : IsValuationUnit K (1 + z)) :
    scaleIdeal (D.newTailUnnormalized hunit) (D.newTailLattice hunit) =
      principalIdeal (K := K) (S.targetJordan.scaleGenerator 1 : K) :=
  (D.newTailUnnormalized_modular hunit).scaleIdeal_eq_principal
    (by rw [D.newTail_finrank hunit]; omega)

theorem correctedHeadUnnormalized_normIdeal
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.correctedHeadUnnormalized hunit)
        (D.correctedHeadLattice hunit) =
      principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) := by
  calc
    normIdeal (D.correctedHeadUnnormalized hunit)
        (D.correctedHeadLattice hunit) =
        principalIdeal (K := K)
          ((S.firstScale * D.firstGenerator : Kˣ) : K) :=
      (D.correctedHeadUnnormalized_normGenerator hunit).2
    _ = normIdeal (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice :=
      D.targetFirst_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 0 : K) :=
      S.targetJordan.normIdeal_eq 0

theorem newTailUnnormalized_normIdeal
    (hunit : IsValuationUnit K (1 + z)) :
    normIdeal (D.newTailUnnormalized hunit) (D.newTailLattice hunit) =
      principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) := by
  calc
    normIdeal (D.newTailUnnormalized hunit) (D.newTailLattice hunit) =
        principalIdeal (K := K)
          ((S.firstScale * D.secondGenerator : Kˣ) : K) :=
      (D.newTailUnnormalized_normGenerator hunit).2
    _ = normIdeal (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice :=
      D.targetSecond_unscaledNormGenerator.2.symm
    _ = principalIdeal (K := K) (S.targetJordan.normGenerator 1 : K) :=
      S.targetJordan.normIdeal_eq 1

theorem targetFirst_normGroupSet_subset_correctedHeadUnnormalized
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet (S.targetJordan.component 0).space
        (S.targetJordan.component 0).lattice ⊆
      normGroupSet (D.correctedHeadUnnormalized hunit)
        (D.correctedHeadLattice hunit) := by
  intro a ha
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  have hnormalized : ((S.firstScale⁻¹ : Kˣ) : K) * a ∈
      normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice := by
    rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
    simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using ha
  have heq : normGroupSet S.targetFirstNormalized
        (S.targetJordan.component 0).lattice =
      normGroupSet (D.correctedHead hunit)
        (D.correctedHeadLattice hunit) :=
    S.firstNormalized_normGroupSet_eq.symm.trans
      (D.correctedHead_normGroupSet_eq_source hunit)
  rw [← heq]
  exact hnormalized

theorem targetSecond_normGroupSet_subset_newTailUnnormalized
    (hunit : IsValuationUnit K (1 + z)) :
    normGroupSet (S.targetJordan.component 1).space
        (S.targetJordan.component 1).lattice ⊆
      normGroupSet (D.newTailUnnormalized hunit)
        (D.newTailLattice hunit) := by
  intro a ha
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  apply (D.tailShift hunit).normGroup_subset
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff]
  simpa only [Units.val_inv_eq_inv_val, inv_inv, ← mul_assoc,
    mul_inv_cancel₀ (Units.ne_zero S.firstScale), one_mul] using ha

noncomputable def firstPairReplacementIsometry
    (hunit : IsValuationUnit K (1 + z)) :
    Isometry
      ((D.correctedHeadUnnormalized hunit).orthogonalSum
        (D.newTailUnnormalized hunit))
      S.targetJordan.firstPairSublattice.space
      (product (D.correctedHeadLattice hunit) (D.newTailLattice hunit))
      S.targetJordan.firstPairSublattice.lattice :=
  (D.originalPairIsometry hunit).symm.trans
    (S.targetJordan.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      firstIndex_ne_secondIndex)

/-- Install the Step-7 determinant correction as a saturated target Jordan
splitting. -/
noncomputable def jordanReplacement
    (hunit : IsValuationUnit K (1 + z)) :
    Omeara9319JordanReplacement S.targetJordan := by
  let f := D.firstPairReplacementIsometry hunit
  let T := S.targetJordan.replaceFirstPairOfIsometry f
    (D.correctedHeadUnnormalized_modular hunit)
    (D.newTailUnnormalized_modular hunit)
    (D.correctedHeadUnnormalized_scaleIdeal hunit)
    (D.newTailUnnormalized_scaleIdeal hunit)
    (D.correctedHeadUnnormalized_normIdeal hunit)
    (D.newTailUnnormalized_normIdeal hunit)
  exact
    { target := T
      fundamentalType :=
        S.targetJordan.replaceFirstPairOfIsometry_sameFundamentalType f
          (D.correctedHeadUnnormalized_modular hunit)
          (D.newTailUnnormalized_modular hunit)
          (D.correctedHeadUnnormalized_scaleIdeal hunit)
          (D.newTailUnnormalized_scaleIdeal hunit)
          (D.correctedHeadUnnormalized_normIdeal hunit)
          (D.newTailUnnormalized_normIdeal hunit)
      saturated :=
        S.targetJordan.replaceFirstPairOfIsometry_isSaturated f
          (D.correctedHeadUnnormalized_modular hunit)
          (D.newTailUnnormalized_modular hunit)
          (D.correctedHeadUnnormalized_scaleIdeal hunit)
          (D.newTailUnnormalized_scaleIdeal hunit)
          (D.correctedHeadUnnormalized_normIdeal hunit)
          (D.newTailUnnormalized_normIdeal hunit)
          S.targetJordan_isSaturated
          (D.targetFirst_normGroupSet_subset_correctedHeadUnnormalized hunit)
          (D.targetSecond_normGroupSet_subset_newTailUnnormalized hunit)
      laterPrefixIsometry := by
        intro k hk
        exact S.targetJordan.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (S.targetJordan.firstPairDecompositionOfIsometry f) k hk }

end GapTwoErrorData

/-- The saturated target Jordan splitting produced by the Step-7
determinant correction. -/
noncomputable def gapTwoJordanReplacement
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    Omeara9319JordanReplacement S.targetJordan :=
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  D.jordanReplacement hunit

/-- The displayed corrected head maps onto the first component of the
installed Step-7 replacement. -/
noncomputable def gapTwoReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let R := S.gapTwoJordanReplacement A conditions hgap hscale
    Isometry (D.correctedHeadUnnormalized hunit) (R.target.component 0).space
      (D.correctedHeadLattice hunit) (R.target.component 0).lattice := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let R := S.gapTwoJordanReplacement A conditions hgap hscale
  change Isometry (D.correctedHeadUnnormalized hunit)
    (R.target.component 0).space
    (D.correctedHeadLattice hunit) (R.target.component 0).lattice
  rw [show R.target = S.targetJordan.replaceFirstPairOfIsometry
      (D.firstPairReplacementIsometry hunit)
      (D.correctedHeadUnnormalized_modular hunit)
      (D.newTailUnnormalized_modular hunit)
      (D.correctedHeadUnnormalized_scaleIdeal hunit)
      (D.newTailUnnormalized_scaleIdeal hunit)
      (D.correctedHeadUnnormalized_normIdeal hunit)
      (D.newTailUnnormalized_normIdeal hunit) by rfl]
  exact S.targetJordan.replaceFirstPairOfIsometry_leftIsometry
    (D.firstPairReplacementIsometry hunit)
    (D.correctedHeadUnnormalized_modular hunit)
    (D.newTailUnnormalized_modular hunit)
    (D.correctedHeadUnnormalized_scaleIdeal hunit)
    (D.newTailUnnormalized_scaleIdeal hunit)
    (D.correctedHeadUnnormalized_normIdeal hunit)
    (D.newTailUnnormalized_normIdeal hunit)

noncomputable abbrev gapTwoTargetFirstNormalized
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    QuadraticSpace K
      ((S.gapTwoJordanReplacement A conditions hgap hscale)
        |>.target.component 0).carrier :=
  ((S.gapTwoJordanReplacement A conditions hgap hscale)
    |>.target.component 0).space.rescaleUnit S.firstScale⁻¹

/-- After normalization, the displayed corrected head is the actual first
component of the installed replacement. -/
noncomputable def gapTwoNormalizedHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1) :
    let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
    let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
    let R := S.gapTwoJordanReplacement A conditions hgap hscale
    Isometry (D.correctedHead hunit)
      (S.gapTwoTargetFirstNormalized A conditions hgap hscale)
      (D.correctedHeadLattice hunit) (R.target.component 0).lattice := by
  let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
  let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
  let R := S.gapTwoJordanReplacement A conditions hgap hscale
  let head := S.gapTwoReplacementHeadIsometry A conditions hgap hscale
  let scaled := head.rescaleUnitBoth S.firstScale⁻¹
  let collapseRaw := rescaleUnitMulLatticeIsometry (D.correctedHead hunit)
    (D.correctedHeadLattice hunit) S.firstScale S.firstScale⁻¹
  have hscaleUnit : S.firstScale⁻¹ * S.firstScale = (1 : Kˣ) := by simp
  let finish : Isometry ((D.correctedHead hunit).rescaleUnit
      (S.firstScale⁻¹ * S.firstScale)) (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) (D.correctedHeadLattice hunit) := by
    simpa only [hscaleUnit] using Isometry.rescaleUnitOne
      (D.correctedHead hunit) (D.correctedHeadLattice hunit)
  let collapse : Isometry
      ((D.correctedHeadUnnormalized hunit).rescaleUnit S.firstScale⁻¹)
      (D.correctedHead hunit)
      (D.correctedHeadLattice hunit) (D.correctedHeadLattice hunit) := by
    simpa only [GapTwoErrorData.correctedHeadUnnormalized] using
      collapseRaw.trans finish
  exact collapse.symm.trans scaled

/-- Any normalized source-to-corrected-head isometry gives an isometry to
the installed replacement head after restoring the first scale. -/
noncomputable def gapTwoSourceToReplacementHeadIsometry
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (head : let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      Isometry S.sourceFirstNormalized (D.correctedHead hunit)
        (S.sourceJordan.component 0).lattice
        (D.correctedHeadLattice hunit)) :
    let R := S.gapTwoJordanReplacement A conditions hgap hscale
    Isometry (S.sourceJordan.component 0).space (R.target.component 0).space
      (S.sourceJordan.component 0).lattice
      (R.target.component 0).lattice := by
  let R := S.gapTwoJordanReplacement A conditions hgap hscale
  let normalized := head.trans
    (S.gapTwoNormalizedHeadIsometry A conditions hgap hscale)
  let scaled := normalized.rescaleUnitBoth S.firstScale
  let undoSource := undoInverseRescaleLatticeIsometry
    (S.sourceJordan.component 0).space
    (S.sourceJordan.component 0).lattice S.firstScale
  let undoTarget := undoInverseRescaleLatticeIsometry
    (R.target.component 0).space (R.target.component 0).lattice S.firstScale
  exact undoSource.symm.trans (scaled.trans undoTarget)

/-- Package a normalized Step-7 head alignment as the replacement consumed
by the saturated 93:28 induction. -/
noncomputable def gapTwoHeadAlignedReplacementOfNormalizedHead
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (headNormalized :
      let D := S.gapTwoCongruenceErrorData A conditions hgap hscale
      let hunit := S.gapTwoCongruenceError_one_isValuationUnit A conditions
      Isometry S.sourceFirstNormalized (D.correctedHead hunit)
        (S.sourceJordan.component 0).lattice
        (D.correctedHeadLattice hunit)) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A := by
  let R := S.gapTwoJordanReplacement A conditions hgap hscale
  let head := S.gapTwoSourceToReplacementHeadIsometry
    A conditions hgap hscale headNormalized
  let boundary := omeara9328BoundaryZeroConditionsWith_of_headIsometry
    S.sourceJordan R.target A head
  exact R.headAlignedReplacement S.residualFundamentalType A conditions
    boundary head

/-- Condition-(iii) half of O'Meara 93:28, Step 7. -/
noncomputable def gapTwoHeadAlignedReplacementOfConditionIII
    (A : FundamentalNormGeneratorChoice S.sourceJordan)
    (conditions : S.sourceJordan.Omeara9328ConditionsWith
      S.targetJordan A)
    (hgap : ordUnit K (S.secondNormalizedNormGeneratorWith A) =
      ordUnit K S.firstNormGenerator + 2)
    (hscale : ordUnit K S.relativeSecondScale = 1)
    (htrigger : S.sourceJordan.fundamentalIdeal 0 <
      S.sourceJordan.fourNormOverWeightIdealWith A
        (boundaryLeftIndex 0)) :
    Omeara9328HeadAlignedReplacement S.sourceJordan S.targetJordan A :=
  S.gapTwoHeadAlignedReplacementOfNormalizedHead
    A conditions hgap hscale
      (S.gapTwoSourceToCorrectedHeadIsometryOfConditionIII
        A conditions hgap hscale htrigger)

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
