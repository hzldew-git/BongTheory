/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCTheorem62Stable
import Bong.Bong.ValueIsometry

/-!
# He (2025), Remark 6.3

When the ramification index is one, the exceptional binary tail has literal
coefficients `<1,-Delta>`.  The value-preserving BONG isometry below proves
the corresponding integral isometry after adjoining the hyperbolic plane.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- At `e=1`, the raised second endpoint coefficient is literally `-Delta`. -/
theorem heADCExceptionalTail_second_eq_neg_discriminant
    (heOne : ramificationIndex K = 1) :
    heHuDiscriminantEndpointValues (K := K) 0 1 *
        uniformizerPowerUnit K 1 ^ 2 =
      -(dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit := by
  rw [heHuDiscriminantEndpointValues_one, heOne]
  unfold uniformizerPowerUnit
  rw [pow_two, ← zpow_add]
  norm_num

/-- The literal `<1,-Delta>` tail is admissible when `e=1`. -/
theorem heADCRemark63Tail_admissible
    (heOne : ramificationIndex K = 1) :
    IsBinaryParameterAdmissible
      ((-(dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit) /
        (1 : Kˣ)) := by
  have h := heADCExceptionalTail_admissible (K := K)
  rw [heADCExceptionalTail_second_eq_neg_discriminant heOne] at h
  simpa [heHuDiscriminantEndpointValues, uniformizerPowerUnit] using h

/-- The exact good BONG on the binary lattice `<1,-Delta>`. -/
noncomputable def heADCRemark63Tail
    (heOne : ramificationIndex K = 1) :
    GoodBONG
      (BONG.binaryDiagonalModelSpace 1
        (-(dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
        (heADCRemark63Tail_admissible heOne))
      (BONG.binaryDiagonalModelLattice (K := K)) 2 :=
  BONG.binaryDiagonalExactGoodBONG _ _ (heADCRemark63Tail_admissible heOne)

/-- The literal tail in Remark 6.3 is integral. -/
theorem heADCRemark63Tail_integral
    (heOne : ramificationIndex K = 1) :
    Lattice.IsIntegral
      (BONG.binaryDiagonalModelSpace 1
        (-(dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
        (heADCRemark63Tail_admissible heOne))
      (BONG.binaryDiagonalModelLattice (K := K)) := by
  apply heHuIntegral_of_firstOrder_nonneg (heADCRemark63Tail heOne)
  rw [heADCRemark63Tail, BONG.binaryDiagonalExactGoodBONG_order]
  change 0 ≤ ordUnit K (1 : Kˣ)
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  rw [hone]

/-- A good BONG on the literal lattice `H perp <1,-Delta>`. -/
noncomputable def heADCRemark63Candidate
    (heOne : ramificationIndex K = 1) :=
  heHu2022Lemma310BONG (heADCRemark63Tail heOne)
    (heADCRemark63Tail_integral heOne) 1

/-- He (2025), Remark 6.3: for `e=1`, the exceptional lattice is integrally
isometric to `H perp <1,-Delta>`. -/
theorem heADC2025Remark63 (heOne : ramificationIndex K = 1) :
    Lattice.IsIsometric
      (heADCExceptionalQuaternaryForm (K := K))
      (Lattice.halfHyperbolicExtensionForm
        (BONG.binaryDiagonalModelSpace 1
          (-(dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
          (heADCRemark63Tail_admissible heOne)) 1)
      (heADCExceptionalQuaternaryLattice (K := K))
      (Lattice.halfHyperbolicExtensionLattice
        (BONG.binaryDiagonalModelLattice (K := K)) 1) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let b := heADCRemark63Candidate heOne
  let aTail := heADCExceptionalTail (K := K)
  let bTail := heADCRemark63Tail heOne
  have hvaluesUnit : ∀ i, a.valueUnit i = b.valueUnit i := by
    intro i
    fin_cases i
    · exact (heHu2022Lemma310HyperbolicValues aTail
        (heADCExceptionalTail_integral (K := K)) 1 0).1.trans
          (heHu2022Lemma310HyperbolicValues bTail
            (heADCRemark63Tail_integral heOne) 1 0).1.symm
    · exact (heHu2022Lemma310HyperbolicValues aTail
        (heADCExceptionalTail_integral (K := K)) 1 0).2.trans
          (heHu2022Lemma310HyperbolicValues bTail
            (heADCRemark63Tail_integral heOne) 1 0).2.symm
    · calc
        a.valueUnit 2 = aTail.valueUnit 0 := by
          dsimp only [a, aTail, heADCExceptionalQuaternaryCandidate]
          simpa using heHu2022Lemma310TailValues
            (heADCExceptionalTail (K := K))
            (heADCExceptionalTail_integral (K := K)) 1 (0 : Fin 2)
        _ = bTail.valueUnit 0 := by
          dsimp only [aTail, bTail]
          simp [heADCExceptionalTail, heADCRemark63Tail,
            BONG.binaryDiagonalExactGoodBONG_valueUnit,
            heHuDiscriminantEndpointValues, uniformizerPowerUnit]
        _ = b.valueUnit 2 := by
          symm
          dsimp only [b, bTail, heADCRemark63Candidate]
          simpa using heHu2022Lemma310TailValues
            (heADCRemark63Tail heOne)
            (heADCRemark63Tail_integral heOne) 1 (0 : Fin 2)
    · calc
        a.valueUnit 3 = aTail.valueUnit 1 := by
          dsimp only [a, aTail, heADCExceptionalQuaternaryCandidate]
          simpa using heHu2022Lemma310TailValues
            (heADCExceptionalTail (K := K))
            (heADCExceptionalTail_integral (K := K)) 1 (1 : Fin 2)
        _ = bTail.valueUnit 1 := by
          dsimp only [aTail, bTail]
          rw [heADCExceptionalTail, heADCRemark63Tail,
            BONG.binaryDiagonalExactGoodBONG_valueUnit,
            BONG.binaryDiagonalExactGoodBONG_valueUnit]
          exact heADCExceptionalTail_second_eq_neg_discriminant heOne
        _ = b.valueUnit 3 := by
          symm
          dsimp only [b, bTail, heADCRemark63Candidate]
          simpa using heHu2022Lemma310TailValues
            (heADCRemark63Tail heOne)
            (heADCRemark63Tail_integral heOne) 1 (1 : Fin 2)
  have hvalues : ∀ i, a.toBONG.value i = b.toBONG.value i := by
    intro i
    exact congrArg (fun z : Kˣ ↦ (z : K)) (hvaluesUnit i)
  exact ⟨a.toBONG.latticeIsometryOfValueEq b.toBONG hvalues⟩

end BONG.GoodBONG

end Bong
