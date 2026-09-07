/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankOneTests
import Bong.Bong.He2023ADCOddMaximalStructure

/-!
# Ambient rows in the raised-tail case of He (2025), Theorem 6.1

The required positive ambient embeddings are coordinate inclusions. They
are promoted to integral representations only through the n-ADC hypothesis.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The hyperbolic first even row embeds in every first odd row, without
requiring its odd-row parameter to have even valuation. -/
theorem heADCEvenFirstOne_represents_oddFirst (k : Nat) (c : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients (heADCW1Even k (1 : Kˣ)))
      (diagonalUnitCoefficients (heADCW1Odd k c)) := by
  have htail := diagonalRepresents_append_right_prefix (heHuBinaryFirst (1 : Kˣ)) ![c]
  have hfamily : Fin.append (heHuBinaryFirst (1 : Kˣ)) ![c] = heHuOddFirstTail c := by
    funext i
    fin_cases i <;> rfl
  rw [hfamily] at htail
  rw [heADCW1Even, heHuEvenFirst_eq_towerModel, heADCW1Odd, heHuOddFirst,
    diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
  exact (diagonalRepresents_refl _).appendBoth htail

/-- The discriminant first even row embeds in every unit-uniformizer
second odd row, including the binary-to-ternary boundary. -/
theorem heADCEvenFirstDelta_represents_oddSecondUniformizer (k : Nat)
    (δ : Kˣ) (hδ : IsValuationUnit K (δ : K)) :
    DiagonalRepresents (diagonalUnitCoefficients (heADCW1Even k
      (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit))
      (diagonalUnitCoefficients (heADCW2Odd k (δ * uniformizerPowerUnit K 1))) := by
  let Δ := (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit
  let c := δ * uniformizerPowerUnit K 1
  have hnotEven : ¬ Even (ordUnit K c) := by
    dsimp only [c]
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδ,
      ordUnit_uniformizerPowerUnit]
    norm_num
  have htail := diagonalRepresents_append_right_prefix (heHuBinaryFirst Δ) ![Δ * c]
  have hfamily : Fin.append (heHuBinaryFirst Δ) ![Δ * c] = heHuOddSecondTailOdd c := by
    funext i
    fin_cases i <;> rfl
  rw [hfamily] at htail
  change DiagonalRepresents (diagonalUnitCoefficients (heHuEvenFirst k Δ))
    (diagonalUnitCoefficients (heHuOddSecond k c))
  rw [heHuEvenFirst_eq_towerModel, heHuOddSecond_of_not_even k c hnotEven,
    diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
  exact (diagonalRepresents_refl _).appendBoth htail

namespace BONG.GoodBONG

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The raised penultimate order excludes both first-column endpoint
spaces, because ADC would lift their ambient representation to Lemma 6.4(i). -/
theorem heADCRaisedTail_not_represents_first (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int))
    (c : Kˣ)
    (hc : c = 1 ∨ c = (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit) :
    ¬ q.Represents (BONG.coefficientDiagonalSpace (heADCW1Even k c)) := by
  intro hspace
  have hrep := hADC.represents _ (heHuOMaximalLattice (heADCW1Even k c))
    (finrank_fin_fun K) (heHuOMaximalLattice_isOMaximal _).isIntegral hspace
  obtain ⟨_, horders, _⟩ := a.heADC2025Lemma64i k c hc hADC.isIntegral hrep
  have hodd : ¬ Even (2 * k + 1) := by rintro ⟨s, hs⟩; omega
  have H := horders ⟨2 * k + 1, by omega⟩
  rw [if_neg hodd, hlast] at H
  omega

/-- Only the unit second odd ambient row survives in the raised-tail
case of the even corank-one ADC classification. -/
theorem heADCCorankOne_raisedTail_ambient (k : Nat) (a : GoodBONG q L (2 * k + 3))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (hlast : a.order ⟨2 * k + 1, by omega⟩ = 2 - 2 * (ramificationIndex K : Int)) :
    ∃ δ : Kˣ, IsValuationUnit K (δ : K) ∧
      q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Odd k δ)) := by
  have hnotOne := a.heADCRaisedTail_not_represents_first k hADC hlast 1 (Or.inl rfl)
  have hnotDelta := a.heADCRaisedTail_not_represents_first k hADC hlast
    (Dyadic.dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit (Or.inr rfl)
  obtain ⟨δ, hδ, hfirst | hsecond | hfirstπ | hsecondπ⟩ := a.exists_heADCOddNormalizedAmbient k
  · apply False.elim
    apply hnotOne
    exact (show q.Represents (BONG.coefficientDiagonalSpace (heADCW1Odd k δ)) from
      ⟨(Classical.choice hfirst).symm.toRepresentation⟩).trans
        ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).2
          (heADCEvenFirstOne_represents_oddFirst k δ))
  · exact ⟨δ, hδ, hsecond⟩
  · apply False.elim
    apply hnotOne
    exact (show q.Represents (BONG.coefficientDiagonalSpace
      (heADCW1Odd k (δ * uniformizerPowerUnit K 1))) from
        ⟨(Classical.choice hfirstπ).symm.toRepresentation⟩).trans
          ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).2
            (heADCEvenFirstOne_represents_oddFirst k (δ * uniformizerPowerUnit K 1)))
  · apply False.elim
    apply hnotDelta
    exact (show q.Represents (BONG.coefficientDiagonalSpace
      (heADCW2Odd k (δ * uniformizerPowerUnit K 1))) from
        ⟨(Classical.choice hsecondπ).symm.toRepresentation⟩).trans
          ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents _ _).2
            (heADCEvenFirstDelta_represents_oddSecondUniformizer k δ hδ))

end BONG.GoodBONG

end Bong
