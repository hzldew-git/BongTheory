/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCDefinition716
import Bong.Bong.He2023ADCPublishedProfiles

/-!
# He (2025), Lemma 7.18

An odd-corank-two `n`-ADC lattice in the second ambient column with a unit
parameter cannot have the maximal penultimate order `-2e`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He (2025), Lemma 7.18. -/
theorem heADC2025Lemma718 (k : Nat) (epsilon : Kˣ)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon))) :
    a.order ⟨2 * k + 3, by omega⟩ ≠
      -(2 * (ramificationIndex K : Int)) := by
  intro hpenultimate
  have hmaximal :=
    a.heADC2025Lemma715_isOMaximal_of_penultimate k hADC hpenultimate
  have htarget :
      Lattice.IsOMaximal
        (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon))
        (heADCN2Odd (k + 1) epsilon).lattice := by
    exact heHuOMaximalModel_isOMaximal _
  have hisometry :
      Lattice.IsIsometric q
        (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) epsilon))
        L (heADCN2Odd (k + 1) epsilon).lattice :=
    Lattice.oMaximal_isIsometric_of_isometric hmaximal htarget ambient
  let ac := a.castLength (by omega : 2 * k + 5 = 3 + 2 * (k + 1))
  have hprofile := (heADC2025Lemma412iiPublished epsilon hepsilon (k + 1)
    ac hADC.isIntegral ambient).mp hisometry
  have hboundary := hprofile ⟨2 * k + 3, by omega⟩
  rw [order_castLength] at hboundary
  simp [heADCMaximalOrderProfile,
    show ¬2 * k + 3 < 2 * (k + 1) by omega,
    show 2 * k + 3 - 2 * (k + 1) = 1 by omega] at hboundary
  omega

/-- The equivalent undefinedness statement for the symbol in Definition
7.16. -/
theorem heADC2025Lemma718_not_definition716 (k : Nat) (epsilon : Kˣ)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (a : GoodBONG q L (2 * k + 5)) :
    ¬HeADC2025Definition716 k (ramificationIndex K)
      HeADC716Column.two epsilon a := by
  intro A
  apply a.heADC2025Lemma718 k epsilon hepsilon A.nADC
  · simpa only [HeADC716Column.coefficients] using A.ambient
  · simpa only [Nat.cast_ofNat, Nat.cast_mul] using A.penultimate

end BONG.GoodBONG

end Bong
