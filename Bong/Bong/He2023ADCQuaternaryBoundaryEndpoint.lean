/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryTests

/-!
# The discriminant binary test at the quaternary boundary

The first order of this exceptional target is 1, not 0. Its terminal alpha
cap is omitted. The central conclusion is a quadratic-space embedding only.
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

/-- The endpoint binary profile satisfies all four conditions once its ternary
prefix embedding is supplied. The required first order is explicitly 1. -/
theorem heADCBoundary_represents_endpoint (a : GoodBONG q L 4)
    (b : GoodBONG r M 2) (ha : HeADCQuaternaryBoundaryOrders a)
    (hsplit : IsSquare ((-1 : Kˣ) * a.prefixProduct 2))
    (hbzero : b.order 0 = 1)
    (hbone : b.order 1 = 1 - 2 * (ramificationIndex K : Int))
    (hb : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ))
    (hprefix : DiagonalRepresents (b.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)))
    (ambient : q.Represents r) : Lattice.Represents q r L M := by
  have hintegral : Lattice.IsIntegral r M :=
    b.toBONG.beliUniversalLemma22.mpr (by change 0 ≤ b.order 0; rw [hbzero]; omega)
  apply (heADC2025Theorem36Published (by omega) ambient a b).mpr
  refine ⟨a.heADCBoundary_orderCondition b ha hintegral, ?_, ?_,
    a.heADCBoundary_longConditions b ha hintegral⟩
  · intro i
    have hi : i.val = 1 ∨ i.val = 2 := by have := i.pos; have := i.le_small; omega
    rcases hi with hi | hi
    · simpa only [hi] using a.heADCBoundary_firstDefect b ha hintegral i hi
    · have hcomparison := a.heADCBoundary_secondComparisonDefect b ha hsplit
        (2 * ramificationIndex K) le_rfl (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb)
      simp only [hi, hcomparison, coe_representationAlphaValue]
      apply (a.representationAlpha_le_halfGap b i).trans
      unfold representationHalfGap
      have haTwo : a.order 2 = 1 := ha 2
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
      exact (lt_irrefl (1 : Int) h).elim
    · rcases i with ⟨j, hj1, hj2, hj3⟩
      change j = 3 at hi
      subst j
      exact hprefix

/-- The actual third coefficient is the uniformizer, not merely an element of order 1. -/
theorem heADCQuaternaryBoundaryCandidate_thirdValue :
    (heADCQuaternaryBoundaryCandidate (K := K)).valueUnit 2 = uniformizerPowerUnit K 1 := by
  have h := heHu2022Lemma310TailValues (heADCBoundaryTail (K := K))
    (heADCBoundaryTail_integral (K := K)) 1 0
  change (heADCQuaternaryBoundaryCandidate (K := K)).valueUnit 2 =
    (heADCBoundaryTail (K := K)).valueUnit 0 at h
  rw [h, heADCBoundaryTail, BONG.binaryDiagonalExactGoodBONG_valueUnit]
  rfl

/-- The split head is isotropic as an actual prefix quadratic space. -/
theorem heADCQuaternaryBoundaryCandidate_firstTwoIsotropic :
    (heADCQuaternaryBoundaryCandidate (K := K)).UniversalFirstTwoIsotropic := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  have hproduct : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    unfold GoodBONG.prefixProduct
    rw [a.toBONG.prefixProduct_succ 1 (by omega),
      a.toBONG.prefixProduct_succ 0 (by omega), BONG.prefixProduct_zero, one_mul]
    rfl
  have hsquare := heADCQuaternaryBoundaryCandidate_splitHead (K := K)
  change IsSquare ((-1 : Kˣ) * a.prefixProduct 2) at hsquare
  rw [hproduct, neg_one_mul] at hsquare
  have hiso := diagonalBinary_isotropic_of_isSquare_neg_product _ _ hsquare
  change DiagonalIsotropic (a.prefixValues 2 (by omega))
  convert hiso using 1
  funext i
  fin_cases i <;> rfl

/-- The ternary prefix represents every binary form whose first coefficient is the uniformizer.
This assertion is a field embedding and does not assert an integral lattice embedding. -/
theorem heADCQuaternaryBoundaryCandidate_firstThree_represents (c : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients (![uniformizerPowerUnit K 1, c] : Fin 2 → Kˣ))
      ((heADCQuaternaryBoundaryCandidate (K := K)).prefixValues 3 (by omega)) := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let line : Fin 1 → K := fun _ ↦ (uniformizerPowerUnit K 1 : K)
  have hline := a.firstTwo_represents_of_isotropic
    (heADCQuaternaryBoundaryCandidate_firstTwoIsotropic (K := K)) c
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
    · change (a.valueUnit 2 : K) = (uniformizerPowerUnit K 1 : K)
      exact congrArg Units.val (heADCQuaternaryBoundaryCandidate_thirdValue (K := K))

/-- The actual candidate represents the constructed maximal discriminant binary lattice. -/
theorem heADCQuaternaryBoundaryCandidate_represents_endpointTarget :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (heHuLemma43TargetSpace (K := K) 0) (heADCQuaternaryBoundaryLattice (K := K))
      (heHuLemma43TargetLattice (K := K) 0) := by
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let b := heHuLemma43Target (K := K) 0
  let c := -((dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit *
    uniformizerPowerUnit K (1 - 2 * (ramificationIndex K : Int)))
  have hvalues := heHuLemma43Target_lastValues (K := K) 0
  have hcoeff : b.prefixValues 2 (by omega) =
      diagonalUnitCoefficients (![uniformizerPowerUnit K 1, c] : Fin 2 → Kˣ) := by
    funext i
    fin_cases i
    · change (b.valueUnit 0 : K) = (uniformizerPowerUnit K 1 : K)
      exact congrArg Units.val hvalues.1
    · change (b.valueUnit 1 : K) = (c : K)
      exact congrArg Units.val hvalues.2
  have hprefix : DiagonalRepresents (b.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
    rw [hcoeff]
    exact heADCQuaternaryBoundaryCandidate_firstThree_represents c
  have hdiag : DiagonalRepresents (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients a.valueUnit) :=
    hprefix.trans (DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients a.valueUnit) (by omega : 3 ≤ 4))
  have ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (heHuLemma43TargetSpace (K := K) 0) :=
    (QuadraticSpace.represents_iff_of_isometries b.toBONG.exactDiagonalizationIsometry
      a.toBONG.exactDiagonalizationIsometry).mpr
        ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
          b.valueUnit a.valueUnit).mpr hdiag)
  have horders := heHuLemma43Target_lastOrders (K := K) 0
  have hdefect : defectOrder (K := K) ((-1 : Kˣ) * b.prefixProduct 2) =
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct, b] using
      heHuLemma43Target_fullSignedDefect (K := K) 0
  exact heADCBoundary_represents_endpoint a b
    (heADCQuaternaryBoundaryCandidate_hasOrders (K := K))
    (heADCQuaternaryBoundaryCandidate_splitHead (K := K))
    horders.1 horders.2 hdefect hprefix ambient

/-- The endpoint representation transports to the literal named `N_2^2(Delta)`.
This is an integral representation of the actual maximal test, not just its ambient space. -/
theorem heADCQuaternaryBoundaryCandidate_represents_N2Delta :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW2Even 0
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 0)))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heADCN2Even 0 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 0)).lattice := by
  let b := heHuLemma43Target (K := K) 0
  let w := heADCW2Even 0 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
    (heHuLemma43_evenSecondDefined (K := K) 0)
  have ambient := b.ambientIsometric_of_diagonalRepresents w rfl
    (heHuLemma43Target_represents_evenSecond (K := K) 0)
  have hmaximal : Lattice.IsOMaximal (heHuLemma43TargetSpace (K := K) 0)
      (heHuLemma43TargetLattice (K := K) 0) :=
    heHu2022Proposition37EvenSecondDelta (K := K) 0
  have hisometry := Lattice.oMaximal_isIsometric_of_isometric hmaximal
    (heHuOMaximalLattice_isOMaximal w) ambient
  exact (heADCQuaternaryBoundaryCandidate_represents_endpointTarget (K := K)).trans
    ⟨(Classical.choice hisometry).symm.toRepresentation⟩

/-- The literal half-hyperbolic plane is an integral summand of the actual candidate. -/
theorem heADCQuaternaryBoundaryCandidate_represents_halfHyperbolic :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (Lattice.dyadicHalfUnit (K := K)))
      (heADCQuaternaryBoundaryLattice (K := K)) (Lattice.hyperbolicPlaneLattice (K := K)) := by
  refine ⟨{
    toLinearMap := LinearMap.inl K (Fin 2 → K) (Fin 2 → K)
    injective := fun _ _ h ↦ congrArg Prod.fst h
    map_bilin := ?_
    map_mem := ?_ }⟩
  · intro x y
    change ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K))).bilin x y +
      (BONG.binaryDiagonalModelSpace (heHuDiscriminantEndpointValues (K := K) 1 0)
        (heHuDiscriminantEndpointValues (K := K) 1 1 * uniformizerPowerUnit K 1 ^ 2)
        (heADCBoundaryTail_admissible (K := K))).bilin 0 0 =
      ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit
        (Lattice.dyadicHalfUnit (K := K))).bilin x y
    simp only [map_zero, add_zero]
  · intro x hx
    exact ⟨hx, (BONG.binaryDiagonalModelLattice (K := K)).zero_mem⟩

/-- The actual half-hyperbolic summand supplies the named maximal square binary test. -/
theorem heADCQuaternaryBoundaryCandidate_represents_N1One :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCW1Even 0 (1 : Kˣ)))
      (heADCQuaternaryBoundaryLattice (K := K)) (heADCN1Even 0 (1 : Kˣ)).lattice := by
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
  exact (heADCQuaternaryBoundaryCandidate_represents_halfHyperbolic (K := K)).trans
    ⟨(Classical.choice hisometry).symm.toRepresentation⟩

end BONG.GoodBONG

end Bong
