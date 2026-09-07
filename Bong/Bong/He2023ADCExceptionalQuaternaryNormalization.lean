/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCExceptionalQuaternaryGeneric
import Bong.Bong.He2023ADCEvenCorankTwoGeneric

/-!
# Removing the parameter normalization for the exceptional quaternary tests

Square normalization reduces every nonexceptional binary parameter to either
a unit or a unit times one uniformizer.  The integral target is then
transported through the resulting equal-rank isometry.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A normalized sharp parameter is covered by the unit or unit-uniformizer test. -/
theorem heADCExceptionalQuaternaryCandidate_represents_sharp_normalized
    (second : Bool) (c : Kˣ) (hs : HeHuSharpDomain c)
    (hnorm : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heHuOMaximalLattice (heADCEvenSharpSpace second 0 c hs)) := by
  rcases hnorm with hzero | hone
  · have hunit := (isValuationUnit_iff_ordUnit_eq_zero K c).mpr hzero
    cases second with
    | false => exact heADCExceptionalQuaternaryCandidate_represents_unitFirst c hunit hs ambient
    | true => exact heADCExceptionalQuaternaryCandidate_represents_unitSecond c hunit hs ambient
  · obtain ⟨delta, hdelta, hc⟩ : ∃ delta : Kˣ, IsValuationUnit K (delta : K) ∧
        c = delta * uniformizerPowerUnit K 1 := by
      refine ⟨normalizedUnitPart K c, normalizedUnitPart_isValuationUnit K c, ?_⟩
      simpa only [hone, mul_comm] using (uniformizerPower_mul_normalizedUnitPart K c).symm
    subst c
    cases second with
    | false =>
        exact heADCExceptionalQuaternaryCandidate_represents_uniformizerFirst delta hdelta ambient
    | true =>
        exact heADCExceptionalQuaternaryCandidate_represents_uniformizerSecond delta hdelta ambient

/-- Every relevant nonexceptional maximal binary test is represented with its
original, unnormalized parameter. -/
theorem heADCExceptionalQuaternaryCandidate_represents_sharp
    (second : Bool) (c : Kˣ) (hs : HeHuSharpDomain c)
    (ambient : (heADCExceptionalQuaternaryForm (K := K)).Represents
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))) :
    Lattice.Represents (heADCExceptionalQuaternaryForm (K := K))
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs))
      (heADCExceptionalQuaternaryLattice (K := K))
      (heHuOMaximalLattice (heADCEvenSharpSpace second 0 c hs)) := by
  obtain ⟨d, s, hdOrder, hc⟩ := exists_order_zero_or_one_mul_square_any (K := K) c
  have hd := heADCSharpDomain_of_mul_square c d s hs hc
  have hrep := heADCEvenSharpSpace_represents_of_mul_square second 0 c d s hs hd hc
  have hiso : (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 c hs)).IsIsometric
      (BONG.coefficientDiagonalSpace (heADCEvenSharpSpace second 0 d hd)) :=
    Lattice.QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      _ _ hrep
  have hnormalized := heADCExceptionalQuaternaryCandidate_represents_sharp_normalized
    second d hd hdOrder (ambient.trans ⟨(Classical.choice hiso).symm.toRepresentation⟩)
  have hintegralIso := Lattice.oMaximal_isIsometric_of_isometric
    (heHuOMaximalLattice_isOMaximal _) (heHuOMaximalLattice_isOMaximal _) hiso
  exact hnormalized.trans ⟨(Classical.choice hintegralIso).toRepresentation⟩

end BONG.GoodBONG

end Bong
