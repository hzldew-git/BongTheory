/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryConditions
import Bong.Bong.He2023ADCSignedDeterminant
import Bong.Bong.He2023ADCEvenMixedTests

/-!
# Actual test representations for the quaternary boundary candidate

The split head and full defect are proved for the constructed lattice itself.
The results below do not assert a complete maximal-testing reduction or 2-ADC.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The actual quadratic form on the candidate's hyperbolic-extension carrier. -/
noncomputable abbrev heADCQuaternaryBoundaryForm :=
  Lattice.halfHyperbolicExtensionForm
    (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 1 0)
      (heHuDiscriminantEndpointValues (K := K) 1 1 * uniformizerPowerUnit K 1 ^ 2)
      (heADCBoundaryTail_admissible (K := K))) 1

/-- The candidate's actual full lattice on that carrier. -/
noncomputable abbrev heADCQuaternaryBoundaryLattice :=
  Lattice.halfHyperbolicExtensionLattice (BONG.binaryDiagonalModelLattice (K := K)) 1

/-- The candidate has an actual split binary head, not just even head orders. -/
theorem heADCQuaternaryBoundaryCandidate_splitHead :
    IsSquare ((-1 : Kˣ) * (heADCQuaternaryBoundaryCandidate (K := K)).prefixProduct 2) := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  have hvalues := heHu2022Lemma310HyperbolicValues (heADCBoundaryTail (K := K))
    (heADCBoundaryTail_integral (K := K)) 1 0
  change a.valueUnit 0 = 1 ∧ a.valueUnit 1 =
    -(uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int)))) at hvalues
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  change IsSquare ((-1 : Kˣ) * a.prefixProduct 2)
  rw [hproduct, hvalues.1, hvalues.2, one_mul, neg_one_mul, neg_neg]
  exact isSquare_uniformizerPowerUnit_of_even _ ⟨-(ramificationIndex K : Int), by ring⟩

/-- The candidate's full raw defect is the discriminant defect `2e`. -/
theorem heADCQuaternaryBoundaryCandidate_fullDefect :
    defectOrder (K := K) ((heADCQuaternaryBoundaryCandidate (K := K)).prefixProduct 4) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW2Even 1 δ (heHuLemma43_evenSecondDefined (K := K) 1)
  have ambient := a.ambientIsometric_of_diagonalRepresents w rfl
    (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hclass := heADCEvenSecond_determinantClass 1 δ
    (heHuLemma43_evenSecondDefined (K := K) 1)
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

/-- The actual candidate represents each ambiently represented finite-defect binary test.
The displayed target profile is explicit; completeness of the test family is not assumed. -/
theorem heADCQuaternaryBoundaryCandidate_represents_finite
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W} (b : GoodBONG r M 2)
    (d : Nat) (hd : d < 2 * ramificationIndex K)
    (hbzero : b.order 0 = 0) (hbone : b.order 1 = 1 - (d : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) = (d : ℚ))
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents r) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K)) r
      (heADCQuaternaryBoundaryLattice (K := K)) M := by
  exact heADCBoundary_represents_finite (heADCQuaternaryBoundaryCandidate (K := K)) b
    (heADCQuaternaryBoundaryCandidate_hasOrders (K := K))
    (heADCQuaternaryBoundaryCandidate_splitHead (K := K))
    (heADCQuaternaryBoundaryCandidate_fullDefect (K := K)) d hd hbzero hbone hb ambient

end BONG.GoodBONG

end Bong
