/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCPublishedProfiles

/-!
# An actual lattice at the unresolved binary-testing boundary

Raising the second coefficient of the discriminant endpoint by a uniformizer
square gives an integral binary lattice. Adjoining the literal half-hyperbolic
plane realizes the profile `0,-2e,1,3-2e` in the second discriminant space.
This file checks existence and nonmaximality only. It does not assert that the
candidate is 2-ADC or that a published theorem has been refuted.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Admissibility after raising the second endpoint coefficient by a square. -/
theorem heADCBoundaryTail_admissible :
    IsBinaryParameterAdmissible
      ((heHuDiscriminantEndpointValues (K := K) 1 1 * uniformizerPowerUnit K 1 ^ 2) /
        heHuDiscriminantEndpointValues (K := K) 1 0) := by
  have h := (heHuDiscriminantEndpoint_admissible (K := K) 1).mul_integral_square
    (uniformizerPowerUnit_nat_mem_integerRing (K := K) 1)
  simpa only [Nat.cast_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The actual binary tail with orders `1,3-2e`; no ADC property is assumed. -/
noncomputable def heADCBoundaryTail :
    GoodBONG
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCBoundaryTail_admissible (K := K)))
      (BONG.binaryDiagonalModelLattice (K := K)) 2 :=
  BONG.binaryDiagonalExactGoodBONG _ _ (heADCBoundaryTail_admissible (K := K))

/-- Both exact orders of the raised discriminant tail. -/
theorem heADCBoundaryTail_orders (i : Fin 2) :
    (heADCBoundaryTail (K := K)).order i =
      (![1, 3 - 2 * (ramificationIndex K : Int)] : Fin 2 → Int) i := by
  rw [heADCBoundaryTail, BONG.binaryDiagonalExactGoodBONG_order]
  have hdelta := (isValuationUnit_iff_ordUnit_eq_zero K
    (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).mp
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_isValuationUnit
  fin_cases i
  · simp [heHuDiscriminantEndpointValues, ordUnit_uniformizerPowerUnit]
  · change ordUnit K (heHuDiscriminantEndpointValues (K := K) 1 1 *
      uniformizerPowerUnit K 1 ^ 2) = 3 - 2 * (ramificationIndex K : Int)
    rw [ordUnit_mul, ordUnit_pow, heHuDiscriminantEndpointValues_one, ordUnit_neg,
      ordUnit_mul, ordUnit_uniformizerPowerUnit, ordUnit_uniformizerPowerUnit, hdelta]
    ring

/-- The raised tail is an integral lattice, not merely a formal coefficient list. -/
theorem heADCBoundaryTail_integral :
    Lattice.IsIntegral
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCBoundaryTail_admissible (K := K)))
      (BONG.binaryDiagonalModelLattice (K := K)) :=
  heHuIntegral_of_firstOrder_nonneg (heADCBoundaryTail (K := K))
    (by rw [heADCBoundaryTail_orders]; norm_num)

/-- A full, integral rank-four candidate on an actual half-hyperbolic extension. -/
noncomputable def heADCQuaternaryBoundaryCandidate :=
  heHu2022Lemma310BONG (heADCBoundaryTail (K := K)) (heADCBoundaryTail_integral (K := K)) 1

/-- The full candidate profile is realized without an ADC assumption. -/
theorem heADCQuaternaryBoundaryCandidate_orders (i : Fin 4) :
    (heADCQuaternaryBoundaryCandidate (K := K)).order i =
      (![0, -(2 * (ramificationIndex K : Int)), 1,
        3 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i := by
  have h := heADC2025Remark410 (heADCBoundaryTail (K := K))
    (heADCBoundaryTail_integral (K := K)) 1 _ heADCBoundaryTail_orders i
  change (heADCQuaternaryBoundaryCandidate (K := K)).order i = _ at h
  rw [h]
  fin_cases i <;> simp [heADCMaximalOrderProfile]

/-- A coordinate square identifies the tail space, but not the integral tail lattice. -/
theorem heADCBoundaryTail_represents_endpoint :
    DiagonalRepresents (diagonalUnitCoefficients (heADCBoundaryTail (K := K)).valueUnit)
      (diagonalUnitCoefficients (heHuDiscriminantEndpointGoodBONG (K := K) 1).valueUnit) := by
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square _ _
    (![1, uniformizerPowerUnit K 1] : Fin 2 → Kˣ)
  intro i
  rw [heADCBoundaryTail, BONG.binaryDiagonalExactGoodBONG_valueUnit,
    heHuDiscriminantEndpointGoodBONG_valueUnit]
  fin_cases i <;> simp

/-- The actual candidate has the second discriminant ambient space. -/
theorem heADCQuaternaryBoundaryCandidate_represents_second :
    DiagonalRepresents
      (diagonalUnitCoefficients (heADCQuaternaryBoundaryCandidate (K := K)).valueUnit)
      (diagonalUnitCoefficients (heADCW2Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 1))) := by
  have htail := (heADCBoundaryTail_represents_endpoint (K := K)).trans
    (heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 1)
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 1 =
      heHuDiscriminantBinary
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuDiscriminantBinary, heHuBinaryTwist, mul_comm]
  rw [htarget] at htail
  have hlift := heADCTower_represents (heADCBoundaryTail (K := K))
    (heADCBoundaryTail_integral (K := K)) 1 _ htail
  rw [← heHuLemma43_evenSecond_eq_model (K := K) 1] at hlift
  exact hlift

/-- The remaining profile occurs on a nonmaximal integral lattice in the actual `W_2`.
This existence statement makes no claim that the lattice is 2-ADC. -/
theorem exists_heADCQuaternaryBoundaryCandidate :
    let w := heADCW2Even 1
      (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
      (heHuLemma43_evenSecondDefined (K := K) 1)
    ∃ (L : Lattice K (Fin 4 → K)) (a : GoodBONG (BONG.coefficientDiagonalSpace w) L 4),
      Lattice.IsIntegral (BONG.coefficientDiagonalSpace w) L ∧
        ¬ Lattice.IsOMaximal (BONG.coefficientDiagonalSpace w) L ∧
        ∀ i, a.order i = (![0, -(2 * (ramificationIndex K : Int)), 1,
          3 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i := by
  dsimp only
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let w := heADCW2Even 1
    (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
    (heHuLemma43_evenSecondDefined (K := K) 1)
  have hspace := a.ambientIsometric_of_diagonalRepresents w rfl
    (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  let f := Lattice.Isometry.toMap _ (Classical.choice hspace)
    (Lattice.halfHyperbolicExtensionLattice (BONG.binaryDiagonalModelLattice (K := K)) 1)
  let a' := a.mapLatticeIsometry f
  have horders : ∀ i, a'.order i = (![0, -(2 * (ramificationIndex K : Int)), 1,
      3 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i := by
    intro i
    rw [show a'.order i = a.order i from order_mapLatticeIsometry f a i]
    exact heADCQuaternaryBoundaryCandidate_orders i
  have hIntegral := heHuIntegral_of_firstOrder_nonneg a' (by rw [horders]; norm_num)
  refine ⟨_, a', hIntegral, ?_, horders⟩
  intro hmaximal
  have hmodel := Lattice.oMaximal_isIsometric_of_isometric hmaximal
    (heHuOMaximalLattice_isOMaximal w) ⟨QuadraticSpace.Isometry.refl _⟩
  have hcriterion := (heADC2025Lemma411iiDeltaPublished 1 a' hIntegral
    ⟨QuadraticSpace.Isometry.refl _⟩).mp hmodel
  have hlast := hcriterion 3
  rw [horders] at hlast
  norm_num [heADCMaximalOrderProfile] at hlast
  change 3 - 2 * (ramificationIndex K : Int) = 1 - 2 * (ramificationIndex K : Int) at hlast
  omega

end BONG.GoodBONG

end Bong
