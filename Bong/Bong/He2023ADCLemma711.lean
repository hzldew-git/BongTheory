/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma713
import Bong.Bong.HeHu2022Lemma57

/-!
# He (2025), Lemma 7.11

The published symbol `d(a_1...a_4)=infinity` means that the four-entry
prefix determinant is a square.  We first expose the odd-valuation tests
`N_2^3(delta*pi)` from the published testing set.  Two parameters differing
by the distinguished nonsquare unit cannot both be the unique ternary class
missed by the source ambient space, so at least one such test is represented
by the full rank-five space.  Lemma 5.7 then gives the condition-(iii')
obstruction at paper index `4`.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The odd-valuation half of He, Lemma 7.11.  This is the branch used in
the rank-three necessity argument below. -/
theorem heADC2025Lemma711Odd (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    ¬ a.CentralRepresentationConditionsPrime
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta) := by
  exact a.heHu2022Lemma57_not_centralRepresentationConditionsPrime
    (m := 3) (by omega) hAIntegral hI1 hR4 hR5 hprefix delta hdelta

/-- A rank-five source space represents at least one of two odd-valuation
second-column tests whose unit parameters differ by `Delta`. -/
theorem heADC2025Lemma711_exists_represented_oddTarget
    (a : GoodBONG q L 5) :
    ∃ (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)),
      DiagonalRepresents
        (diagonalUnitCoefficients
          (heHuLemma311OddSecondUnitUniformizerTail delta hdelta).valueUnit)
        (diagonalUnitCoefficients a.valueUnit) := by
  let laws := heHuDiscriminantClassLaws (K := K)
  let Delta : Kˣ := laws.discriminantUnit
  let c : Kˣ := uniformizerPowerUnit K 1
  let targetOne := heADCW2Odd (K := K) 0 c
  let targetDelta := heADCW2Odd (K := K) 0 (c * Delta)
  have hDelta : ¬ IsSquare Delta := by
    exact AlternatingEndpointNormalization.discriminantUnit_not_isSquare
      (K := K) (laws := laws)
  have htwist : ¬ DiagonalRepresents
      (diagonalUnitCoefficients targetDelta)
      (diagonalUnitCoefficients targetOne) := by
    apply heADC2025Lemma713_twisted_not_represents 0 c Delta hDelta
      targetOne targetDelta
    · exact (heADC2025Proposition42iOdd (K := K) 0 c).determinantSquare
    · exact (heADC2025Proposition42iOdd
        (K := K) 0 (c * Delta)).determinantSquare
  have select {excluded : Fin 3 → Kˣ} {large : Fin 5 → Kˣ}
      (hexact : HeHuMissesExactly excluded large) :
      DiagonalRepresents (diagonalUnitCoefficients targetOne)
          (diagonalUnitCoefficients large) ∨
        DiagonalRepresents (diagonalUnitCoefficients targetDelta)
          (diagonalUnitCoefficients large) := by
    by_cases hone : DiagonalRepresents
        (diagonalUnitCoefficients targetOne)
        (diagonalUnitCoefficients excluded)
    · right
      apply hexact.represents_other targetDelta
      intro hdelta
      exact htwist (hdelta.trans hone.symm_of_sameRank)
    · left
      exact hexact.represents_other targetOne hone
  have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).2
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [one_mul] at h
    omega
  have hDeltaUnit : IsValuationUnit K (Delta : K) := by
    exact laws.discriminant_isValuationUnit
  have hliteralOne : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitUniformizerTail 1 honeUnit).valueUnit)
      (diagonalUnitCoefficients targetOne) := by
    simpa only [targetOne, c, heADCW2Odd, heHuLemma57Parameter, one_mul] using
      heHuLemma57Target_represents_oddSecond (K := K) 1 honeUnit
  have hliteralDelta : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitUniformizerTail Delta hDeltaUnit).valueUnit)
      (diagonalUnitCoefficients targetDelta) := by
    simpa only [targetDelta, c, heADCW2Odd, heHuLemma57Parameter,
      mul_comm] using
        heHuLemma57Target_represents_oddSecond (K := K) Delta hDeltaUnit
  rcases a.heADC2025Lemma713_sourceDiagonal (k := 0) with hsource | hsource
  · rcases select
        (heADC2025Proposition42iiiOddSecond
          (K := K) 0 (heHuLemma59C a 0)).exactness with hone | hdelta
    · exact ⟨1, honeUnit, hliteralOne.trans (hone.trans hsource)⟩
    · exact ⟨Delta, hDeltaUnit,
        hliteralDelta.trans (hdelta.trans hsource)⟩
  · rcases select
        (heADC2025Proposition42iiiOddFirst
          (K := K) 0 (heHuLemma59C a 0)).exactness with hone | hdelta
    · exact ⟨1, honeUnit, hliteralOne.trans (hone.trans hsource)⟩
    · exact ⟨Delta, hDeltaUnit,
        hliteralDelta.trans (hdelta.trans hsource)⟩

/-- Under `3`-ADC, the exceptional rank-three branch in the necessity proof
of Lemma 7.5 cannot occur. -/
theorem heADC2025Lemma711_badBranch_impossible
    (a : GoodBONG q L 5)
    (hADC : Lattice.IsNADC.{u, u, u} q L 3)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤) : False := by
  rcases a.heADC2025Lemma711_exists_represented_oddTarget with
    ⟨delta, hdelta, hdiag⟩
  let r :=
    (BONG.binaryDiagonalModelSpace
      (heHuDiscriminantEndpointValues (K := K) 0 0)
      (heHuDiscriminantEndpointValues (K := K) 0 1)
      (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
        (QuadraticSpace.rescaleUnit
          (heHuLemma311OddSecondUnitUniformizerValue delta)
          (QuadraticSpace.line K))
  let M := Lattice.product
    (BONG.binaryDiagonalModelLattice (K := K))
    (BONG.unaryModelLattice (K := K))
  let b : GoodBONG r M 3 :=
    heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  have hM : Lattice.IsIntegral r M :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [show b.order 0 = 0 by simp [b]])
  have hrep : Lattice.Represents q r L M := by
    apply hADC.represents r M b.toBONG.length_eq_finrank.symm hM
    have hSource : q.Represents
        (BONG.coefficientDiagonalSpace a.valueUnit) :=
      ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
    have hdiag' : DiagonalRepresents
        (diagonalUnitCoefficients b.valueUnit)
        (diagonalUnitCoefficients a.valueUnit) := by
      convert hdiag using 1
    have hDiagonal :
        (BONG.coefficientDiagonalSpace a.valueUnit).Represents
          (BONG.coefficientDiagonalSpace b.valueUnit) :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        b.valueUnit a.valueUnit).2 hdiag'
    exact (hSource.trans hDiagonal).trans
      ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  have hcentral :=
    ((heADC2025Theorem36Published (by omega) hrep.ambient a b).mp hrep)
      |>.centralRepresentations
  exact (a.heADC2025Lemma711Odd hADC.isIntegral hI1 hR4 hR5 hprefix
    delta hdelta) hcentral

end BONG.GoodBONG

end Bong
