/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryNormalization

/-!
# Complete binary testing for the quaternary boundary lattice

The square, discriminant, and nonexceptional classes are treated separately.
The maximal-testing reduction concerns actual integral lattices.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Transport a represented maximal binary lattice through an equal-rank field isometry. -/
theorem heADCBoundary_represents_of_diagonalRepresents (w w' : Fin 2 → Kˣ)
    (hspace : DiagonalRepresents (diagonalUnitCoefficients w) (diagonalUnitCoefficients w'))
    (hrep : Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace w') (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice w')) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace w) (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice w) := by
  have hiso : (BONG.coefficientDiagonalSpace w).IsIsometric (BONG.coefficientDiagonalSpace w') :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      w w' hspace
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal w) (heHuOMaximalLattice_isOMaximal w') hiso
  exact hrep.trans ⟨(Classical.choice hintegral).toRepresentation⟩

/-- The first discriminant binary space is not represented by the candidate's ambient space. -/
theorem heADCQuaternaryBoundaryCandidate_misses_N1Delta :
    ¬ (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCW1Even 0
        (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)) := by
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let w := heADCW2Even 1 δ (heHuLemma43_evenSecondDefined (K := K) 1)
  have hiso := (heADCQuaternaryBoundaryCandidate (K := K)).ambientIsometric_of_diagonalRepresents
    w rfl (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hmiss : ¬ DiagonalRepresents (diagonalUnitCoefficients (heADCW1Even 0 δ))
      (diagonalUnitCoefficients w) := by
    simpa only [w, heADCW2Even, heHuEvenSecondNext, heHuFinFamilyCast_self] using
      (heADC2025Proposition42iiiEvenFirst 0 δ).exactness.misses
  intro hrep
  apply hmiss
  apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).mp
  exact (show (BONG.coefficientDiagonalSpace w).Represents
    (heADCQuaternaryBoundaryForm (K := K)) from
      ⟨(Classical.choice hiso).toRepresentation⟩).trans hrep

/-- Every relevant binary member of the full two-column maximal catalogue is represented. -/
theorem heADCQuaternaryBoundaryCandidate_represents_evenTest
    (i : HeHuEvenTestingIndex (K := K) 0)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace i.coefficients)) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace i.coefficients) (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice i.coefficients) := by
  classical
  let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  cases i with
  | first c =>
      by_cases hsquare : IsSquare c
      · obtain ⟨s, hs⟩ := hsquare
        have hc : c = 1 * s ^ 2 := by simpa only [one_mul, pow_two] using hs
        apply heADCBoundary_represents_of_diagonalRepresents _ (heADCW1Even 0 1)
          (Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square 0 c 1 s hc)
        exact heADCQuaternaryBoundaryCandidate_represents_N1One (K := K)
      · by_cases hdelta : IsSquare (c / δ)
        · obtain ⟨s, hs⟩ := hdelta
          have hc : c = δ * s ^ 2 := by
            calc
              c = (c / δ) * δ := (div_mul_cancel c δ).symm
              _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
          have hiso : (BONG.coefficientDiagonalSpace (heADCW1Even 0 c)).IsIsometric
              (BONG.coefficientDiagonalSpace (heADCW1Even 0 δ)) :=
            Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
              _ _ (Lattice.QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square
                0 c δ s hc)
          exact False.elim (heADCQuaternaryBoundaryCandidate_misses_N1Delta
            (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩))
        · exact heADCQuaternaryBoundaryCandidate_represents_sharp false c
            ⟨hsquare, hdelta⟩ ambient
  | second c hdefined =>
      have hnonsquare : ¬ IsSquare c := hdefined.resolve_left (by omega)
      by_cases hdelta : IsSquare (c / δ)
      · obtain ⟨s, hs⟩ := hdelta
        have hc : c = δ * s ^ 2 := by
          calc
            c = (c / δ) * δ := (div_mul_cancel c δ).symm
            _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
        apply heADCBoundary_represents_of_diagonalRepresents _
          (heADCW2Even 0 δ (heHuLemma43_evenSecondDefined (K := K) 0))
          (Lattice.QuadraticLatticeModel.heHuEvenSecond_represents_of_mul_square
            0 c δ s hdefined hc)
        exact heADCQuaternaryBoundaryCandidate_represents_N2Delta (K := K)
      · exact heADCQuaternaryBoundaryCandidate_represents_sharp true c
          ⟨hnonsquare, hdelta⟩ ambient

/-- Complete testing of actual maximal binary lattices, without a catalogue-completeness premise. -/
theorem heADCQuaternaryBoundaryCandidate_representsAllRelevantOMaximal :
    Lattice.RepresentsAllRelevantOMaximalOfRank.{u, u, u}
      (heADCQuaternaryBoundaryForm (K := K)) (heADCQuaternaryBoundaryLattice (K := K)) 2 := by
  intro W _ _ r M hRank hMaximal ambient
  let X : Lattice.QuadraticLatticeModel (K := K) :=
    { Carrier := W, form := r, lattice := M }
  obtain ⟨i, hi⟩ :=
    Lattice.QuadraticLatticeModel.exists_evenTestingIndex_ambientlyIsometric 0 X hRank
  have hiso : r.IsIsometric (BONG.coefficientDiagonalSpace i.coefficients) := hi
  have htest := heADCQuaternaryBoundaryCandidate_represents_evenTest i
    (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩)
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric hMaximal
    (heHuOMaximalLattice_isOMaximal i.coefficients) hiso
  exact htest.trans ⟨(Classical.choice hintegral).toRepresentation⟩

/-- The actual integral quaternary boundary lattice is 2-ADC. -/
theorem heADCQuaternaryBoundaryCandidate_is2ADC :
    Lattice.IsNADC.{u, u, u} (heADCQuaternaryBoundaryForm (K := K))
      (heADCQuaternaryBoundaryLattice (K := K)) 2 := by
  apply (Lattice.isNADC_iff_representsAllRelevantOMaximal _ _ 2).mpr
  refine ⟨?_, heADCQuaternaryBoundaryCandidate_representsAllRelevantOMaximal (K := K)⟩
  exact heHuIntegral_of_firstOrder_nonneg (heADCQuaternaryBoundaryCandidate (K := K))
    (by rw [heADCQuaternaryBoundaryCandidate_orders]; norm_num)

/-- The same actual 2-ADC candidate is not maximal on its ambient space. -/
theorem heADCQuaternaryBoundaryCandidate_not_isOMaximal :
    ¬ Lattice.IsOMaximal (heADCQuaternaryBoundaryForm (K := K))
      (heADCQuaternaryBoundaryLattice (K := K)) := by
  intro hmaximal
  let a := heADCQuaternaryBoundaryCandidate (K := K)
  let w := heADCW2Even 1 (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
    (heHuLemma43_evenSecondDefined (K := K) 1)
  have hiso := a.ambientIsometric_of_diagonalRepresents w rfl
    (heADCQuaternaryBoundaryCandidate_represents_second (K := K))
  have hintegral := Lattice.oMaximal_isIsometric_of_isometric hmaximal
    (heHuOMaximalLattice_isOMaximal w) hiso
  have hprofile := (heADC2025Lemma411iiDeltaPublished 1 a hmaximal.isIntegral hiso).mp hintegral
  have hlast := hprofile 3
  rw [show a.order 3 = _ from heADCQuaternaryBoundaryCandidate_orders 3] at hlast
  norm_num [heADCMaximalOrderProfile] at hlast
  change 3 - 2 * (ramificationIndex K : Int) = 1 - 2 * (ramificationIndex K : Int) at hlast
  omega

end BONG.GoodBONG

end Bong
