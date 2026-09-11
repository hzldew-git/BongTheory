/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCQuaternaryBoundaryGeneric
import Bong.Bong.He2023ADCEvenCorankTwoGeneric

/-!
# Removing the parameter normalization from the boundary tests

Only the proved square-normalization helpers are reused from the corank-two
generic module. No assertion of Lemma 6.8 is used in these proofs.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A normalized sharp parameter is covered by the unit or unit-uniformizer test. -/
theorem heADCQuaternaryBoundaryCandidate_represents_sharp_normalized
    (second : Bool) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hnorm : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice (heADCEvenSharpSpace second 0 c hs)) := by
  rcases hnorm with hzero | hone
  · have hunit := (isValuationUnit_iff_ordUnit_eq_zero K c).mpr hzero
    cases second with
    | false => exact heADCQuaternaryBoundaryCandidate_represents_unitFirst c hunit hs ambient
    | true => exact heADCQuaternaryBoundaryCandidate_represents_unitSecond c hunit hs ambient
  · obtain ⟨δ, hδ, hc⟩ : ∃ δ : Kˣ, IsValuationUnit K (δ : K) ∧
        c = δ * uniformizerPowerUnit K 1 := by
      refine ⟨normalizedUnitPart K c, normalizedUnitPart_isValuationUnit K c, ?_⟩
      simpa only [hone, mul_comm] using (uniformizerPower_mul_normalizedUnitPart K c).symm
    subst c
    cases second with
    | false => exact heADCQuaternaryBoundaryCandidate_represents_uniformizerFirst δ hδ ambient
    | true => exact heADCQuaternaryBoundaryCandidate_represents_uniformizerSecond δ hδ ambient

/-- Every relevant nonexceptional binary maximal test is represented with its original parameter. -/
theorem heADCQuaternaryBoundaryCandidate_represents_sharp
    (second : Bool) (c : Kˣ) (hs : HeHuSharpDomain c)
    (ambient : (heADCQuaternaryBoundaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))) :
    Lattice.Represents (heADCQuaternaryBoundaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))
      (heADCQuaternaryBoundaryLattice (K := K))
      (heHuOMaximalLattice (heADCEvenSharpSpace second 0 c hs)) := by
  obtain ⟨d, s, hdOrder, hc⟩ := exists_order_zero_or_one_mul_square_any (K := K) c
  have hd := heADCSharpDomain_of_mul_square c d s hs hc
  have hrep := heADCEvenSharpSpace_represents_of_mul_square second 0 c d s hs hd hc
  have hiso : (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs)).IsIsometric
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 d hd)) :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      _ _ hrep
  have hnormalized := heADCQuaternaryBoundaryCandidate_represents_sharp_normalized
    second d hd hdOrder (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩)
  have hintegralIso := Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal _) (heHuOMaximalLattice_isOMaximal _) hiso
  exact hnormalized.trans ⟨(Classical.choice hintegralIso).toRepresentation⟩

end BONG.GoodBONG

end Bong
