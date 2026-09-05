/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCTheorem62Discrepancy
import Bong.Bong.He2023ADCEvenCorankTwoFirst
import Bong.Bong.He2023ADCEvenCorankTwoSecond
import Bong.Bong.He2023ADCEvenCorankTwoGeneric

/-!
# He (2025), Theorem 6.2 above the false binary boundary

For every even `n >= 4`, the six ambient-space branches in Lemma 6.8 imply
that a rank-`n+2` lattice is `n`-ADC exactly when it is maximal.  Arbitrary
ambient parameters are split into the square, discriminant, and sharp
square-class domains; no finite representative system is assumed.
-/

namespace Bong

open Dyadic Module

universe u

namespace Lattice

open BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A square change of parameter transports the first even ambient column. -/
theorem heADCEvenFirst_ambient_of_parameter_mul_square (k : Nat)
    (c d s : Kˣ) (h : c = d * s ^ 2)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even k c))) :
    q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even k d)) := by
  have hrep := QuadraticLatticeModel.heHuEvenFirst_represents_of_mul_square
    k c d s h
  have hiso :=
    QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      (heADCW1Even k c) (heADCW1Even k d) hrep
  exact ⟨(Classical.choice ambient).trans (Classical.choice hiso)⟩

/-- A square change of parameter transports the second even ambient column. -/
theorem heADCEvenSecond_ambient_of_parameter_mul_square (k : Nat)
    (c d s : Kˣ) (hc : HeHuEvenSecondDefined k c) (h : c = d * s ^ 2)
    (ambient : q.IsIsometric
      (BONG.coefficientDiagonalSpace (heADCW2Even k c hc))) :
    q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even k d
      (QuadraticLatticeModel.heHuEvenSecondDefined_of_mul_square hc h))) := by
  have hrep := QuadraticLatticeModel.heHuEvenSecond_represents_of_mul_square
    k c d s hc h
  have hiso :=
    QuadraticLatticeModel.heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
      (heADCW2Even k c hc)
      (heADCW2Even k d
        (QuadraticLatticeModel.heHuEvenSecondDefined_of_mul_square hc h)) hrep
  exact ⟨(Classical.choice ambient).trans (Classical.choice hiso)⟩

/-- Theorem 6.2 with the corrected boundary `n >= 4`.  At `n = 2` the
published biconditional is refuted in `He2023ADCTheorem62Discrepancy`. -/
theorem heADC2025Theorem62_of_four_le (k : Nat) (hk : 0 < k)
    (hrank : finrank K V = 2 * k + 4) :
    IsNADC.{u, u, u} q L (2 * k + 2) ↔ IsOMaximal q L := by
  constructor
  · intro hADC
    let a := (BONG.GoodBONG.ofLattice q L).castLength hrank
    rcases heADC2025Proposition42iiEven (K := K) (k + 1) a.valueUnit with
      ⟨c, hfirst | ⟨hdefined, hsecond⟩⟩
    · have ambient : q.IsIsometric
          (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c)) :=
        a.ambientIsometric_of_diagonalRepresents _ rfl hfirst
      by_cases hsquare : IsSquare c
      · obtain ⟨s, hs⟩ := hsquare
        have hc : c = (1 : Kˣ) * s ^ 2 := by
          simpa only [one_mul, pow_two] using hs
        have ambientOne := heADCEvenFirst_ambient_of_parameter_mul_square
          (k + 1) c 1 s hc ambient
        have hiso := heADC2025Lemma68i k hADC ambientOne
        exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
          (Classical.choice hiso).symm
      · let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        by_cases hdelta : IsSquare (c / δ)
        · obtain ⟨s, hs⟩ := hdelta
          have hc : c = δ * s ^ 2 := by
            calc
              c = (c / δ) * δ := (div_mul_cancel c δ).symm
              _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
          have ambientDelta := heADCEvenFirst_ambient_of_parameter_mul_square
            (k + 1) c δ s hc ambient
          have hiso := heADC2025Lemma68ii k hk hADC ambientDelta
          exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hiso).symm
        · have hs : HeHuSharpDomain c := ⟨hsquare, hdelta⟩
          have hiso := heADC2025Lemma68v k c hs hADC ambient
          exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hiso).symm
    · have ambient : q.IsIsometric
          (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c hdefined)) :=
        a.ambientIsometric_of_diagonalRepresents _ rfl hsecond
      by_cases hsquare : IsSquare c
      · obtain ⟨s, hs⟩ := hsquare
        have hc : c = (1 : Kˣ) * s ^ 2 := by
          simpa only [one_mul, pow_two] using hs
        have ambientOneRaw := heADCEvenSecond_ambient_of_parameter_mul_square
          (k + 1) c 1 s hdefined hc ambient
        have ambientOne : q.IsIsometric (BONG.coefficientDiagonalSpace
            (heADCW2Even (k + 1) (1 : Kˣ) (Or.inl (by omega)))) := by
          simpa only [] using ambientOneRaw
        have hiso := heADC2025Lemma68iii k hADC ambientOne
        exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
          (Classical.choice hiso).symm
      · let δ := (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
        by_cases hdelta : IsSquare (c / δ)
        · obtain ⟨s, hs⟩ := hdelta
          have hc : c = δ * s ^ 2 := by
            calc
              c = (c / δ) * δ := (div_mul_cancel c δ).symm
              _ = δ * s ^ 2 := by rw [hs, pow_two]; ac_rfl
          have ambientDeltaRaw := heADCEvenSecond_ambient_of_parameter_mul_square
            (k + 1) c δ s hdefined hc ambient
          have ambientDelta : q.IsIsometric (BONG.coefficientDiagonalSpace
              (heADCW2Even (k + 1) δ
                (heHuLemma43_evenSecondDefined (K := K) (k + 1)))) := by
            simpa only [] using ambientDeltaRaw
          have hiso := heADC2025Lemma68iv_of_pos k hk hADC ambientDelta
          exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hiso).symm
        · have hs : HeHuSharpDomain c := ⟨hsquare, hdelta⟩
          have ambientSharp : q.IsIsometric (BONG.coefficientDiagonalSpace
              (heADCW2Even (k + 1) c (Or.inr hs.notSquare))) := by
            simpa only [] using ambient
          have hiso := heADC2025Lemma68vi k c hs hADC ambientSharp
          exact (heHuOMaximalLattice_isOMaximal _).of_latticeIsometry
            (Classical.choice hiso).symm
  · intro hmaximal
    exact hmaximal.isNADC (2 * k + 2)

end Lattice

end Bong
