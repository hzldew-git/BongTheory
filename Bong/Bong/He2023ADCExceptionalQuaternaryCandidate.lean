/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenMixedTests
import Bong.Bong.He2023ADCSignedDeterminant

/-!
# The exceptional quaternary lattice in He (2025), Lemmas 6.10--6.12

Multiplying the second coefficient of the order-zero discriminant endpoint by
a uniformizer square gives the binary lattice
`<1, -Delta*pi^(2-2e)>`.  Adjoining one literal half-hyperbolic plane realizes
the published order profile `0,-2e,0,2-2e` in `W_1^4(Delta)`.

This file constructs the lattice and proves its ambient space, integrality,
split head, full discriminant defect, and nonmaximality.  Its 2-ADC and
non-3-ADC properties are treated separately.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Admissibility of the raised order-zero discriminant endpoint. -/
theorem heADCExceptionalTail_admissible :
    IsBinaryParameterAdmissible
      ((heHuDiscriminantEndpointValues (K := K) 0 1 * uniformizerPowerUnit K 1 ^ 2) /
        heHuDiscriminantEndpointValues (K := K) 0 0) := by
  have h := (heHuDiscriminantEndpoint_admissible (K := K) 0).mul_integral_square
    (uniformizerPowerUnit_nat_mem_integerRing (K := K) 1)
  simpa only [Nat.cast_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The actual binary tail of the exceptional lattice. -/
noncomputable def heADCExceptionalTail :
    GoodBONG
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCExceptionalTail_admissible (K := K)))
      (BONG.binaryDiagonalModelLattice (K := K)) 2 :=
  BONG.binaryDiagonalExactGoodBONG _ _ (heADCExceptionalTail_admissible (K := K))

/-- The exact orders `0,2-2e` of the exceptional binary tail. -/
theorem heADCExceptionalTail_orders (i : Fin 2) :
    (heADCExceptionalTail (K := K)).order i =
      (![0, 2 - 2 * (ramificationIndex K : Int)] : Fin 2 → Int) i := by
  rw [heADCExceptionalTail, BONG.binaryDiagonalExactGoodBONG_order]
  have hdelta := (isValuationUnit_iff_ordUnit_eq_zero K
    (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).mp
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_isValuationUnit
  fin_cases i
  · simp [heHuDiscriminantEndpointValues, ordUnit_uniformizerPowerUnit]
  · change ordUnit K (heHuDiscriminantEndpointValues (K := K) 0 1 *
      uniformizerPowerUnit K 1 ^ 2) = 2 - 2 * (ramificationIndex K : Int)
    rw [ordUnit_mul, ordUnit_pow, heHuDiscriminantEndpointValues_one, ordUnit_neg,
      ordUnit_mul, ordUnit_uniformizerPowerUnit, ordUnit_uniformizerPowerUnit, hdelta]
    ring

/-- The exceptional binary tail is an integral lattice. -/
theorem heADCExceptionalTail_integral :
    Lattice.IsIntegral
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCExceptionalTail_admissible (K := K)))
      (BONG.binaryDiagonalModelLattice (K := K)) :=
  heHuIntegral_of_firstOrder_nonneg (heADCExceptionalTail (K := K))
    (by rw [heADCExceptionalTail_orders]; norm_num)

/-- The actual good BONG of the exceptional quaternary lattice. -/
noncomputable def heADCExceptionalQuaternaryCandidate :=
  heHu2022Lemma310BONG (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1

/-- The published exceptional profile `0,-2e,0,2-2e` is realized. -/
theorem heADCExceptionalQuaternaryCandidate_orders (i : Fin 4) :
    (heADCExceptionalQuaternaryCandidate (K := K)).order i =
      (![0, -(2 * (ramificationIndex K : Int)), 0,
        2 - 2 * (ramificationIndex K : Int)] : Fin 4 → Int) i := by
  have h := heADC2025Remark410 (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1 _ heADCExceptionalTail_orders i
  change (heADCExceptionalQuaternaryCandidate (K := K)).order i = _ at h
  rw [h]
  fin_cases i <;> simp [heADCMaximalOrderProfile]

/-- The raised tail represents the unraised order-zero discriminant endpoint. -/
theorem heADCExceptionalTail_represents_endpoint :
    DiagonalRepresents (diagonalUnitCoefficients (heADCExceptionalTail (K := K)).valueUnit)
      (diagonalUnitCoefficients
        (heHuDiscriminantEndpointGoodBONG (K := K) 0).valueUnit) := by
  apply Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square _ _
    (![1, uniformizerPowerUnit K 1] : Fin 2 → Kˣ)
  intro i
  rw [heADCExceptionalTail, BONG.binaryDiagonalExactGoodBONG_valueUnit,
    heHuDiscriminantEndpointGoodBONG_valueUnit]
  fin_cases i <;> simp

/-- The exceptional candidate has ambient space `W_1^4(Delta)`. -/
theorem heADCExceptionalQuaternaryCandidate_represents_first :
    DiagonalRepresents
      (diagonalUnitCoefficients (heADCExceptionalQuaternaryCandidate (K := K)).valueUnit)
      (diagonalUnitCoefficients (heADCW1Even 1
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)) := by
  have htail := (heADCExceptionalTail_represents_endpoint (K := K)).trans
    (heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 0)
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 0 =
      heHuBinaryFirst
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuBinaryFirst, uniformizerPowerUnit]
  rw [htarget] at htail
  exact heADCBinaryTower_represents_evenFirst (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1 _ htail

/-- The quadratic form on the exceptional candidate's product carrier. -/
noncomputable abbrev heADCExceptionalQuaternaryForm :=
  Lattice.halfHyperbolicExtensionForm
    (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
      (heHuDiscriminantEndpointValues (K := K) 0 1 * uniformizerPowerUnit K 1 ^ 2)
      (heADCExceptionalTail_admissible (K := K))) 1

/-- The full exceptional lattice on its product carrier. -/
noncomputable abbrev heADCExceptionalQuaternaryLattice :=
  Lattice.halfHyperbolicExtensionLattice (BONG.binaryDiagonalModelLattice (K := K)) 1

/-- The first two coefficients form the literal half-hyperbolic summand. -/
theorem heADCExceptionalQuaternaryCandidate_splitHead :
    IsSquare ((-1 : Kˣ) *
      (heADCExceptionalQuaternaryCandidate (K := K)).prefixProduct 2) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  have hvalues := heHu2022Lemma310HyperbolicValues (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1 0
  change a.valueUnit 0 = 1 ∧ a.valueUnit 1 =
    -(uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int)))) at hvalues
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  change IsSquare ((-1 : Kˣ) * a.prefixProduct 2)
  rw [hproduct, hvalues.1, hvalues.2, one_mul, neg_one_mul, neg_neg]
  exact isSquare_uniformizerPowerUnit_of_even _
    ⟨-(ramificationIndex K : Int), by ring⟩

/-- The full raw defect is the discriminant defect `2e`. -/
theorem heADCExceptionalQuaternaryCandidate_fullDefect :
    defectOrder (K := K)
        ((heADCExceptionalQuaternaryCandidate (K := K)).prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW1Even 1 δ
  have ambient := a.ambientIsometric_of_diagonalRepresents w rfl
    (heADCExceptionalQuaternaryCandidate_represents_first (K := K))
  have hclass := heADCEvenFirst_determinantClass 1 δ
  have h := a.heADC_signedFullDefectOrder_of_ambient w rfl 2 rfl δ ambient hclass
  have hδ : defectOrder (K := K) δ =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    unfold defectOrder
    rw [show quadraticDefect K δ = (2 * ramificationIndex K : Nat) from
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) = _
    norm_num
  rw [hδ] at h
  simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct, a] using h

/-- The exceptional candidate is integral. -/
theorem heADCExceptionalQuaternaryCandidate_integral :
    Lattice.IsIntegral (heADCExceptionalQuaternaryForm (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) :=
  heHuIntegral_of_firstOrder_nonneg (heADCExceptionalQuaternaryCandidate (K := K))
    (by rw [heADCExceptionalQuaternaryCandidate_orders]; norm_num)

/-- The exceptional candidate is not O'Meara-maximal in `W_1^4(Delta)`. -/
theorem heADCExceptionalQuaternaryCandidate_not_isOMaximal :
    ¬ Lattice.IsOMaximal (heADCExceptionalQuaternaryForm (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) := by
  intro hmaximal
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW1Even 1 δ
  have hiso := a.ambientIsometric_of_diagonalRepresents w rfl
    (heADCExceptionalQuaternaryCandidate_represents_first (K := K))
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric hmaximal
    (heHuOMaximalLattice_isOMaximal w) hiso
  have hprofile := (heADC2025Lemma411iDeltaPublished 1 a hmaximal.isIntegral hiso).mp
    hintegral
  have hlast := hprofile 3
  rw [show a.order 3 = _ from heADCExceptionalQuaternaryCandidate_orders 3] at hlast
  norm_num [heADCMaximalOrderProfile] at hlast
  change 2 - 2 * (ramificationIndex K : Int) =
    -(2 * (ramificationIndex K : Int)) at hlast
  omega

end BONG.GoodBONG

end Bong
