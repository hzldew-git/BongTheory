/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryNormalization
import Bong.Bong.He2023ADCExceptionalQuaternaryEndpoint

/-!
# Complete binary testing for the exceptional quaternary lattice

The square, discriminant, and nonexceptional parameter classes are treated
separately.  Proposition 4.2(iii) removes precisely the second-column
discriminant test that is not represented by the ambient space
`W_1^4(Delta)`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Transport a represented maximal binary lattice through an equal-rank
field isometry. -/
theorem heADCExceptional_represents_of_diagonalRepresents (w w' : Fin 2 → Kˣ)
    (hspace : DiagonalRepresents (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients w'))
    (hrep : Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace w') (heADCExceptionalQuaternaryLattice (K := K))
      (heHuOMaximalLattice w')) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace w) (heADCExceptionalQuaternaryLattice (K := K))
      (heHuOMaximalLattice w) := by
  have hiso : (BONG.coefficientDiagonalSpace w).IsIsometric
      (BONG.coefficientDiagonalSpace w') :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      w w' hspace
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal w) (heHuOMaximalLattice_isOMaximal w') hiso
  exact hrep.trans ⟨(Classical.choice hintegral).toRepresentation⟩

/-- The second-column discriminant binary space is the unique binary space
not represented by the candidate's ambient space. -/
theorem heADCExceptionalQuaternaryCandidate_misses_N2Delta :
    ¬ (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW2Even 0
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        (heHuLemma43_evenSecondDefined (K := K) 0))) := by
  let delta := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let source := heADCW2Even 0 delta (heHuLemma43_evenSecondDefined (K := K) 0)
  let target := heADCW1Even 1 delta
  have hiso := (heADCExceptionalQuaternaryCandidate (K := K))
    |>.ambientIsometric_of_diagonalRepresents target rfl
      (heADCExceptionalQuaternaryCandidate_represents_first (K := K))
  have hmiss : ¬ DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target) := by
    simpa only [source, target, heHuFinFamilyCast_self] using
      (heADC2025Proposition42iiiEvenSecond 0 delta
        (heHuLemma43_evenSecondDefined (K := K) 0)).exactness.misses
  intro hrep
  apply hmiss
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).mp
  exact (show (BONG.coefficientDiagonalSpace target).Represents
    (heADCExceptionalQuaternaryForm (K := K)) from
      ⟨(Classical.choice hiso).toRepresentation⟩).trans hrep

/-- Every relevant member of the complete binary maximal catalogue is represented. -/
theorem heADCExceptionalQuaternaryCandidate_represents_evenTest
    (i : HeHuEvenTestingIndex (K := K) 0)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace i.coefficients)) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace i.coefficients)
      (heADCExceptionalQuaternaryLattice (K := K))
      (heHuOMaximalLattice i.coefficients) := by
  classical
  let delta := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  cases i with
  | first c =>
      by_cases hsquare : IsSquare c
      · obtain ⟨s, hs⟩ := hsquare
        have hc : c = 1 * s ^ 2 := by simpa only [one_mul, pow_two] using hs
        apply heADCExceptional_represents_of_diagonalRepresents _ (heADCW1Even 0 1)
          (Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square
            0 c 1 s hc)
        exact heADCExceptionalQuaternaryCandidate_represents_N1One (K := K)
      · by_cases hdelta : IsSquare (c / delta)
        · obtain ⟨s, hs⟩ := hdelta
          have hc : c = delta * s ^ 2 := by
            calc
              c = (c / delta) * delta := (div_mul_cancel c delta).symm
              _ = delta * s ^ 2 := by rw [hs, pow_two]; ac_rfl
          apply heADCExceptional_represents_of_diagonalRepresents _
            (heADCW1Even 0 delta)
            (Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square
              0 c delta s hc)
          exact heADCExceptionalQuaternaryCandidate_represents_N1Delta (K := K)
        · exact heADCExceptionalQuaternaryCandidate_represents_sharp false c
            ⟨hsquare, hdelta⟩ ambient
  | second c hdefined =>
      have hnonsquare : ¬ IsSquare c := hdefined.resolve_left (by omega)
      by_cases hdelta : IsSquare (c / delta)
      · obtain ⟨s, hs⟩ := hdelta
        have hc : c = delta * s ^ 2 := by
          calc
            c = (c / delta) * delta := (div_mul_cancel c delta).symm
            _ = delta * s ^ 2 := by rw [hs, pow_two]; ac_rfl
        have hiso : (BONG.coefficientDiagonalSpace (heADCW2Even 0 c hdefined)).IsIsometric
            (BONG.coefficientDiagonalSpace (heADCW2Even 0 delta
              (heHuLemma43_evenSecondDefined (K := K) 0))) :=
          Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
            _ _ (Lattice.QuadraticLatticeModel.heHuEvenSecond_represents_of_mul_square
              0 c delta s hdefined hc)
        exact False.elim (heADCExceptionalQuaternaryCandidate_misses_N2Delta
          (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩))
      · exact heADCExceptionalQuaternaryCandidate_represents_sharp true c
          ⟨hnonsquare, hdelta⟩ ambient

/-- Complete testing of actual maximal binary lattices, with no catalogue
completeness premise left to the caller. -/
theorem heADCExceptionalQuaternaryCandidate_representsAllRelevantOMaximal :
    Lattice.RepresentsAllRelevantOMaximalOfRank.{u, u, u}
      (heADCExceptionalQuaternaryForm (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) 2 := by
  intro W _ _ r M hRank hMaximal ambient
  let X : Lattice.QuadraticLatticeModel (K := K) :=
    { Carrier := W, form := r, lattice := M }
  obtain ⟨i, hi⟩ :=
    Lattice.QuadraticLatticeModel.exists_evenTestingIndex_ambientlyIsometric 0 X hRank
  have hiso : r.IsIsometric (BONG.coefficientDiagonalSpace i.coefficients) := hi
  have htest := heADCExceptionalQuaternaryCandidate_represents_evenTest i
    (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩)
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric hMaximal
    (heHuOMaximalLattice_isOMaximal i.coefficients) hiso
  exact htest.trans ⟨(Classical.choice hintegral).toRepresentation⟩

/-- He (2025), Lemma 6.12(i): the actual exceptional quaternary lattice is 2-ADC. -/
theorem heADCExceptionalQuaternaryCandidate_is2ADC :
    Lattice.IsNADC.{u, u, u} (heADCExceptionalQuaternaryForm (K := K))
      (heADCExceptionalQuaternaryLattice (K := K)) 2 := by
  apply (Lattice.isNADC_iff_representsAllRelevantOMaximal _ _ 2).mpr
  exact ⟨heADCExceptionalQuaternaryCandidate_integral (K := K),
    heADCExceptionalQuaternaryCandidate_representsAllRelevantOMaximal (K := K)⟩

end BONG.GoodBONG

end Bong
