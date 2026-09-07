/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma610
import Bong.Bong.He2023ADCEvenCorankTwoTests
import Bong.Bong.He2023ADCEvenCorankTwoGenericTests
import Bong.Bong.He2023ADCEvenFirstTests

/-!
# He (2025), Lemma 6.11

A quaternary 2-ADC lattice in the first discriminant ambient space is either
the maximal lattice or the exceptional lattice constructed in Lemma 6.12.
The binary representations used in the published proof are derived here from
the 2-ADC hypothesis and the displayed ambient space.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Lemma 6.11 on a supplied good BONG.  All four maximal binary tests in
the paper are consequences of 2-ADC-ness, rather than extra assumptions. -/
theorem heADC2025Lemma611_of_goodBONG (a : GoodBONG q L 4)
    (hADC : Lattice.IsNADC.{u, u, u} q L 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even 1
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))) :
    Lattice.IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even 1
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
        L (heADCN1Even 1
          (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice ∨
      Lattice.IsIsometric q (heADCExceptionalQuaternaryForm (K := K)) L
        (heADCExceptionalQuaternaryLattice (K := K)) := by
  let δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  have hδnot : ¬ IsSquare (δ * (1 : Kˣ)) := by
    simpa only [mul_one] using
      AlternatingEndpointNormalization.discriminantUnit_not_isSquare (K := K)
  have hOne := Lattice.heADCEvenCorankTwoFirst_of_not_square 0 δ 1 hADC ambient hδnot
  have hDelta := Lattice.heADCEvenCorankTwoFirst_same 0 δ hADC ambient
  have he := ramificationIndex_pos (K := K)
  obtain ⟨κ, hunit, hκ⟩ := exists_unit_quadraticDefect_eq_odd (K := K)
    (2 * ramificationIndex K - 1) (by omega)
    ⟨ramificationIndex K - 1, by omega⟩ (by omega)
  let hs := heADCKappaSharpDomain κ hκ
  let hdefined : HeHuEvenSecondDefined 0 κ := Or.inr hs.notSquare
  have hκnot : ¬ IsSquare (δ * κ) := by
    simpa only [mul_comm] using heADCSharp_mul_discriminant_not_square κ hs
  have hKappaOne :=
    Lattice.heADCEvenCorankTwoFirst_of_not_square 0 δ κ hADC ambient hκnot
  have hKappaTwo :=
    Lattice.heADCEvenCorankTwoSecond_of_not_square 0 δ κ hdefined hADC ambient hκnot
  obtain ⟨_, hheadOrders, hthird⟩ :=
    a.heADC2025Lemma64ii 0 hADC.isIntegral hOne hDelta
  have hhead : HeADCLemma69HeadOrders a := by
    refine ⟨?_, ?_, hthird⟩
    · simpa using hheadOrders 0
    · have hodd : ¬ Even (1 : Nat) := by decide
      simpa [hodd] using hheadOrders 1
  rcases a.heADC2025Lemma69 κ hunit hκ hhead ambient hKappaOne hKappaTwo with
    hmaximal | hexceptional
  · left
    apply (heADC2025Lemma411iDeltaPublished 1 a hADC.isIntegral ambient).mpr
    intro i
    fin_cases i <;>
      simp [heADCMaximalOrderProfile, hhead.1, hhead.2.1, hhead.2.2, hmaximal]
  · right
    apply a.heADC2025Lemma610
    · intro i
      fin_cases i <;>
        simp [hhead.1, hhead.2.1, hhead.2.2, hexceptional]
    · exact ambient

end BONG.GoodBONG

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- He (2025), Lemma 6.11, stated directly for a quaternary 2-ADC lattice. -/
theorem heADC2025Lemma611
    (hADC : IsNADC.{u, u, u} q L 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even 1
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))) :
    IsIsometric q (BONG.coefficientDiagonalSpace (heADCW1Even 1
        (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
        L (heADCN1Even 1
          (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit).lattice ∨
      IsIsometric q (BONG.GoodBONG.heADCExceptionalQuaternaryForm (K := K)) L
        (BONG.GoodBONG.heADCExceptionalQuaternaryLattice (K := K)) := by
  have hrank := (Classical.choice ambient).toLinearEquiv.finrank_eq
  rw [finrank_fin_fun] at hrank
  let a := (BONG.GoodBONG.ofLattice q L).castLength (by omega : finrank K V = 4)
  exact a.heADC2025Lemma611_of_goodBONG hADC ambient

end Lattice

end Bong
