/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankOneTests

/-!
# Actual corank-two tests for He (2025), Lemma 6.8

The nonexceptional determinant criterion and the explicit hyperbolic lift
produce ambient embeddings. The n-ADC property then gives representation
of the named maximal lattices, without assuming a testing table.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Distinct signed determinant classes give an actual corank-two embedding. -/
theorem heADCEvenCodimensionTwo_represents_of_parameter_not_square
    (k : Nat) {m : Nat} (hm : m = (2 * k + 2) + 2)
    (source : Fin (2 * k + 2) → Kˣ) (target : Fin m → Kˣ) (c d : Kˣ)
    (hsource : IsSquare (diagonalUnitDeterminant source * ((-1 : Kˣ) ^ (k + 1) * c)))
    (htarget : IsSquare (diagonalUnitDeterminant target * ((-1 : Kˣ) ^ (k + 2) * d)))
    (hcd : ¬ IsSquare (c * d)) :
    DiagonalRepresents (diagonalUnitCoefficients source) (diagonalUnitCoefficients target) := by
  subst m
  apply dyadicDiagonalCodimensionTwo_represents
  intro hnegative
  let s : Kˣ := (-1 : Kˣ) ^ (k + 1)
  have htarget' : IsSquare ((s * d) * (-diagonalUnitDeterminant target)) := by
    simpa [s, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htarget
  have hproduct : IsSquare ((s * d) * (s * c)) :=
    isSquare_mul_trans _ (-diagonalUnitDeterminant target) _ htarget'
      (isSquare_mul_trans _ (diagonalUnitDeterminant source) _ hnegative hsource)
  have hquotient := hproduct.div (show IsSquare (s ^ 2) from ⟨s, pow_two s⟩)
  apply hcd
  simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hquotient

/-- The smaller first-column space embeds in its displayed hyperbolic extension. -/
theorem heADCEvenFirst_represents_previous (k : Nat) (c : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients (heADCW1Even k c))
      (diagonalUnitCoefficients (heADCW1Even (k + 1) c)) := by
  have hprefix := DiagonalRepresents.prefixOfLE
    (diagonalUnitCoefficients
      (Fin.append (heADCW1Even k c) (heHuHyperbolicPair (K := K))))
    (by omega : 2 * k + 2 ≤ (2 * k + 2) + 2)
  have hsource : DiagonalRepresents (diagonalUnitCoefficients (heADCW1Even k c))
      (diagonalUnitCoefficients
        (Fin.append (heADCW1Even k c) (heHuHyperbolicPair (K := K)))) := by
    convert hprefix using 1
    funext i
    change (heADCW1Even k c i : K) =
      (Fin.append (heADCW1Even k c) (heHuHyperbolicPair (K := K))
        ⟨i.val, by omega⟩ : Kˣ)
    have hi : (⟨i.val, by omega⟩ : Fin ((2 * k + 2) + 2)) = Fin.castAdd 2 i := Fin.ext rfl
    rw [hi, Fin.append_left]
  exact hsource.trans (heHuEvenFirst_hyperbolicLift k c)

namespace Lattice

variable {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Transporting a concrete ambient embedding into an n-ADC lattice gives a maximal test. -/
theorem heADCMaximal_represents_of_ambient_model {m n : Nat}
    (hADC : IsNADC.{u, u, u} q L n) (source : Fin n → Kˣ) (target : Fin m → Kˣ)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace target))
    (hrep : DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    Represents q (BONG.coefficientDiagonalSpace source) L (heHuOMaximalLattice source) := by
  apply hADC.represents _ _ (finrank_fin_fun K) (heHuOMaximalLattice_isOMaximal source).isIntegral
  exact (show q.Represents (BONG.coefficientDiagonalSpace target) from
    ⟨(Classical.choice ambient).symm.toRepresentation⟩).trans
      ((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents source target).mpr hrep)

/-- A first-column ambient model supplies the same-parameter smaller maximal test. -/
theorem heADCEvenCorankTwoFirst_same (k : Nat) (c : Kˣ)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c))) :
    Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k c))
      L (heADCN1Even k c).lattice :=
  heADCMaximal_represents_of_ambient_model hADC _ _ ambient
    (heADCEvenFirst_represents_previous k c)

/-- A distinct determinant parameter supplies the first-column maximal test. -/
theorem heADCEvenCorankTwoFirst_of_not_square (k : Nat) (c d : Kˣ)
    (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c)))
    (hcd : ¬ IsSquare (c * d)) :
    Represents q (BONG.coefficientDiagonalSpace (heADCW1Even k d))
      L (heADCN1Even k d).lattice := by
  apply heADCMaximal_represents_of_ambient_model hADC _ _ ambient
  exact heADCEvenCodimensionTwo_represents_of_parameter_not_square k (by omega) _ _ d c
    (heADCEvenFirst_determinantClass k d)
    (by simpa only [Nat.add_assoc] using heADCEvenFirst_determinantClass (k + 1) c)
    (by simpa only [mul_comm] using hcd)

/-- A distinct determinant parameter also supplies the defined second-column test. -/
theorem heADCEvenCorankTwoSecond_of_not_square (k : Nat) (c d : Kˣ)
    (hdefined : HeHuEvenSecondDefined k d) (hADC : IsNADC.{u, u, u} q L (2 * k + 2))
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) c)))
    (hcd : ¬ IsSquare (c * d)) :
    Represents q (BONG.coefficientDiagonalSpace (heADCW2Even k d hdefined))
      L (heADCN2Even k d hdefined).lattice := by
  apply heADCMaximal_represents_of_ambient_model hADC _ _ ambient
  exact heADCEvenCodimensionTwo_represents_of_parameter_not_square k (by omega) _ _ d c
    (heADCEvenSecond_determinantClass k d hdefined)
    (by simpa only [Nat.add_assoc] using heADCEvenFirst_determinantClass (k + 1) c)
    (by simpa only [mul_comm] using hcd)

end Lattice

end Bong
