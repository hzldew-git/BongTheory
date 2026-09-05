/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryConditions

/-!
# Actual representation tests for the exceptional quaternary lattice

The abstract conditions from the preceding file are applied to the constructed
lattice.  We also expose its literal split head and its third coefficient,
which supply the endpoint prefix representations in He (2025), Lemma 6.12(i).
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The actual candidate represents every relevant finite-defect binary test
once its published profile data are supplied. -/
theorem heADCExceptionalQuaternaryCandidate_represents_finite
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} (b : GoodBONG r M 2)
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hparity : d = 0 ∨ Odd d) (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = 1 - (d : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents r) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K)) r
      (heADCExceptionalQuaternaryLattice (K := K)) M := by
  have hbeta := b.alphaValue_zero_eq_one_of_finiteProfile d hd hparity hbzero hbone hb
  exact heADCExceptional_represents_finite
    (heADCExceptionalQuaternaryCandidate (K := K)) b
    (heADCExceptionalQuaternaryCandidate_hasOrders (K := K))
    (heADCExceptionalQuaternaryCandidate_splitHead (K := K))
    (heADCExceptionalQuaternaryCandidate_fullDefect (K := K))
    d hd hbzero hbone hbeta hb ambient

/-- The split head is isotropic as an actual binary prefix. -/
theorem heADCExceptionalQuaternaryCandidate_firstTwoIsotropic :
    (heADCExceptionalQuaternaryCandidate (K := K)).UniversalFirstTwoIsotropic := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  have hsquare := heADCExceptionalQuaternaryCandidate_splitHead (K := K)
  change IsSquare ((-1 : Kˣ) * a.prefixProduct 2) at hsquare
  rw [hproduct, neg_one_mul] at hsquare
  have hiso := diagonalBinary_isotropic_of_isSquare_neg_product _ _ hsquare
  change DiagonalIsotropic (a.prefixValues 2 (by omega))
  convert hiso using 1
  funext i
  fin_cases i <;> rfl

/-- The third coefficient of the actual candidate is one. -/
theorem heADCExceptionalQuaternaryCandidate_thirdValue :
    (heADCExceptionalQuaternaryCandidate (K := K)).valueUnit 2 = 1 := by
  have h := heHu2022Lemma310TailValues (heADCExceptionalTail (K := K))
    (heADCExceptionalTail_integral (K := K)) 1 0
  change (heADCExceptionalQuaternaryCandidate (K := K)).valueUnit 2 =
    (heADCExceptionalTail (K := K)).valueUnit 0 at h
  rw [h, heADCExceptionalTail, BONG.binaryDiagonalExactGoodBONG_valueUnit]
  simp [heHuDiscriminantEndpointValues, uniformizerPowerUnit]

/-- The ternary prefix represents every binary diagonal form beginning with one. -/
theorem heADCExceptionalQuaternaryCandidate_firstThree_represents (c : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients (![1, c] : Fin 2 → Kˣ))
      ((heADCExceptionalQuaternaryCandidate (K := K)).prefixValues 3 (by omega)) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let line : Fin 1 → K := fun _ ↦ 1
  have hline := a.firstTwo_represents_of_isotropic
    (heADCExceptionalQuaternaryCandidate_firstTwoIsotropic (K := K)) c
  have happend := DiagonalRepresents.appendBoth (diagonalRepresents_refl line) hline
  have hcomm := DiagonalRepresents.append_comm line (a.prefixValues 2 (by omega))
  have hrep := happend.trans hcomm
  convert hrep using 1
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change (a.valueUnit 2 : K) = (1 : K)
      exact congrArg Units.val
        (heADCExceptionalQuaternaryCandidate_thirdValue (K := K))

end BONG.GoodBONG

end Bong
