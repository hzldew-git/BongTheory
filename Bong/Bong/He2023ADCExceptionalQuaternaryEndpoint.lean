/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryTests

/-!
# Endpoint tests for the exceptional quaternary lattice

The discriminant endpoint has orders `0,-2e` and defect `2e`, so it lies
outside the finite-defect argument.  Its final central condition is supplied
by an explicit representation into the ternary prefix, as in He (2025),
Lemma 6.12(i).
-/

namespace Bong

open Dyadic Module

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The discriminant endpoint satisfies all four representation conditions
once its binary form embeds into the source ternary prefix. -/
theorem heADCExceptional_represents_endpoint (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCExceptionalQuaternaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2))
    (hbzero : b.order 0 = 0)
    (hbone : b.order 1 = -(2 * (ramificationIndex K : Int)))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hprefix : DiagonalRepresents (b.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)))
    (ambient : q.Represents r) : Lattice.Represents q r L M := by
  have hintegral : Lattice.IsIntegral r M :=
    b.toBONG.beliUniversalLemma22.mpr (by change 0 ≤ b.order 0; rw [hbzero])
  apply (heADC2025Theorem36Published (by omega) ambient a b).mpr
  refine ⟨a.heADCExceptional_orderCondition b ha hintegral, ?_, ?_,
    a.heADCExceptional_longConditions b ha hintegral⟩
  · intro i
    have hi : i.val = 1 ∨ i.val = 2 := by have := i.pos; have := i.le_small; omega
    rcases hi with hi | hi
    · simpa only [hi] using a.heADCExceptional_firstDefect b ha hintegral i hi
    · have hcomparison := a.heADCExceptional_secondComparisonDefect b ha hsplit
        (2 * ramificationIndex K) le_rfl
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb)
      simp only [hi, hcomparison, coe_representationAlphaValue]
      apply (a.representationAlpha_le_halfGap b i).trans
      unfold representationHalfGap
      have haTwo : a.order 2 = 0 := ha 2
      simp only [hi]
      change (((((a.order 2 - b.order 1 : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) ≤ _
      rw [haTwo, hbone]
      apply WithTop.coe_le_coe.mpr
      push_cast
      linarith
  · intro i htrigger
    have hi : i.val = 2 ∨ i.val = 3 := by
      have := i.one_lt
      have := i.le_small_succ
      omega
    rcases hi with hi | hi
    · have h := htrigger.1
      simp only [hi] at h
      change b.order 0 < a.order 2 at h
      rw [hbzero, ha 2] at h
      exact (lt_irrefl (0 : Int) h).elim
    · rcases i with ⟨j, hj1, hj2, hj3⟩
      change j = 3 at hi
      subst j
      exact hprefix

/-- The actual exceptional candidate represents the literal discriminant
endpoint lattice. -/
theorem heADCExceptionalQuaternaryCandidate_represents_endpointTarget :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0))
      (heADCExceptionalQuaternaryLattice (K := K))
      (BONG.binaryDiagonalModelLattice (K := K)) := by
  let a := heADCExceptionalQuaternaryCandidate (K := K)
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
  let delta := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let c := -(delta * uniformizerPowerUnit K (-(2 * (ramificationIndex K : Int))))
  have hcoeff : b.prefixValues 2 (by omega) =
      diagonalUnitCoefficients (![1, c] : Fin 2 → Kˣ) := by
    funext i
    fin_cases i
    · change (b.valueUnit 0 : K) = (1 : K)
      rw [heHuDiscriminantEndpointGoodBONG_valueUnit]
      simp [heHuDiscriminantEndpointValues, uniformizerPowerUnit]
    · change (b.valueUnit 1 : K) = (c : K)
      rw [heHuDiscriminantEndpointGoodBONG_valueUnit]
      simp [c, delta, heHuDiscriminantEndpointValues]
  have hprefix : DiagonalRepresents (b.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
    rw [hcoeff]
    exact heADCExceptionalQuaternaryCandidate_firstThree_represents c
  have hdiag : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients a.valueUnit) :=
    hprefix.trans (DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients a.valueUnit) (by omega : 3 ≤ 4))
  have ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0)) :=
    (QuadraticSpace.represents_iff_of_isometries b.toBONG.exactDiagonalizationIsometry
      a.toBONG.exactDiagonalizationIsometry).mpr
        ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
          b.valueUnit a.valueUnit).mpr hdiag)
  have horders : ∀ i, b.order i =
      (![0, -(2 * (ramificationIndex K : Int))] : Fin 2 → Int) i := by
    intro i
    simp [b]
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 0 =
      heHuBinaryFirst delta := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuBinaryFirst, uniformizerPowerUnit, delta]
  have htail := heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 0
  rw [htarget] at htail
  have hw : heADCW1Even 0 delta = heHuBinaryFirst delta := by
    funext i
    fin_cases i <;> rfl
  have hmodel : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW1Even 0 delta)) := by
    rw [hw]
    exact htail
  have hiso := b.ambientIsometric_of_diagonalRepresents
    (heADCW1Even 0 delta) rfl hmodel
  have hbRaw := b.heADC_signedFullDefectOrder_of_ambient
    (heADCW1Even 0 delta) rfl 1 rfl delta hiso
      (by simpa only [Nat.zero_add, pow_one] using heADCEvenFirst_determinantClass 0 delta)
  have hdelta : defectOrder (K := K) delta =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    unfold defectOrder
    rw [show quadraticDefect K delta = (2 * ramificationIndex K : Nat) from
      (dyadicDiscriminantClassLawsProved (K := K)).discriminant_defect]
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) = _
    norm_num
  have hdefect : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    rw [← hdelta]
    simpa only [BONG.signedEvenPrefixProduct, pow_one, GoodBONG.prefixProduct] using hbRaw
  exact heADCExceptional_represents_endpoint a b
    (heADCExceptionalQuaternaryCandidate_hasOrders (K := K))
    (heADCExceptionalQuaternaryCandidate_splitHead (K := K))
    (horders 0) (horders 1) hdefect hprefix ambient

/-- The endpoint representation transports to the named maximal lattice
`N_1^2(Delta)`. -/
theorem heADCExceptionalQuaternaryCandidate_represents_N1Delta :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heADCN1Even 0
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice := by
  let b := heHuDiscriminantEndpointGoodBONG (K := K) 0
  let delta := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW1Even 0 delta
  have htarget : heHuDiscriminantEndpointStandardValues (K := K) 0 =
      heHuBinaryFirst delta := by
    funext i
    fin_cases i <;> simp [heHuDiscriminantEndpointStandardValues,
      heHuBinaryFirst, uniformizerPowerUnit, delta]
  have hrep := heHuDiscriminantEndpointGoodBONG_diagonalRepresents_standard (K := K) 0
  rw [htarget] at hrep
  have hw : w = heHuBinaryFirst delta := by
    funext i
    fin_cases i <;> rfl
  have hdiag : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients w) := by
    rw [hw]
    exact hrep
  have ambient := b.ambientIsometric_of_diagonalRepresents w rfl hdiag
  have hmaximal : Lattice.IsOMaximal
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1)
        (heHuDiscriminantEndpoint_admissible (K := K) 0))
      (BONG.binaryDiagonalModelLattice (K := K)) :=
    heHu2022Proposition37EvenFirstDelta (K := K) 0
  have hisometry := Lattice.oMaximal_isIsometric_of_isometric hmaximal
    (heHuOMaximalLattice_isOMaximal w) ambient
  exact (heADCExceptionalQuaternaryCandidate_represents_endpointTarget (K := K)).trans
    ⟨(Classical.choice hisometry).symm.toRepresentation⟩

/-- The literal half-hyperbolic plane is an integral summand of the candidate. -/
theorem heADCExceptionalQuaternaryCandidate_represents_halfHyperbolic :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K)))
      (heADCExceptionalQuaternaryLattice (K := K))
      (Lattice.hyperbolicPlaneLattice (K := K)) := by
  refine ⟨{
    toLinearMap := LinearMap.inl K (Fin 2 → K) (Fin 2 → K)
    injective := fun _ _ h ↦ congrArg Prod.fst h
    map_bilin := ?_
    map_mem := ?_ }⟩
  · intro x y
    change ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K))).bilin x y +
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 0 0)
        (heHuDiscriminantEndpointValues (K := K) 0 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCExceptionalTail_admissible (K := K))).bilin 0 0 =
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K))).bilin x y
    simp only [map_zero, add_zero]
  · intro x hx
    exact ⟨hx, (BONG.binaryDiagonalModelLattice (K := K)).zero_mem⟩

/-- The half-hyperbolic summand supplies the named square endpoint `N_1^2(1)`. -/
theorem heADCExceptionalQuaternaryCandidate_represents_N1One :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 (1 : Kˣ)))
      (heADCExceptionalQuaternaryLattice (K := K)) (heADCN1Even 0 (1 : Kˣ)).lattice := by
  let b := heHuHyperbolicHeadGoodBONG (K := K)
  let w := heADCW1Even 0 (1 : Kˣ)
  have hvalues : b.valueUnit = heHuLemma45HyperbolicBONGValues (K := K) 1 := by
    funext i
    fin_cases i <;> simp [b, heHuLemma45HyperbolicBONGValues]
  have htarget : AlternatingEndpointTower.standardHyperbolicEndpointTower (K := K) 1 = w := by
    funext i
    fin_cases i <;> rfl
  have hrep : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients w) := by
    rw [hvalues, ← htarget]
    exact heHuLemma45HyperbolicBONGValues_represents_standard 1
  have ambient := b.ambientIsometric_of_diagonalRepresents w rfl hrep
  have hisometry := Lattice.oMaximal_isIsometric_of_isometric
    (heHu2022Proposition37EvenFirstOne (K := K) 0)
    (heHuOMaximalLattice_isOMaximal w) ambient
  exact (heADCExceptionalQuaternaryCandidate_represents_halfHyperbolic (K := K)).trans
    ⟨(Classical.choice hisometry).symm.toRepresentation⟩

end BONG.GoodBONG

end Bong
