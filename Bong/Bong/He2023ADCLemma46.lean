/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenCorankOneTests

/-!
# He (2025), Lemma 4.6

This file completes the dyadic actual-lattice specializations of Lemma 4.6.
Part (i) is proved for both parities and both source-rank alternatives. Part
(ii) is proved for both columns and both parities, using the exact excluding
space from Proposition 4.2(iii).
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Convert a diagonal exactly-one alternative into the corresponding
actual maximal-lattice alternative by `n`-ADC-ness. -/
private theorem heADC2025Lemma46i_of_diagonalExactlyOne
    {m n : Nat} (a : GoodBONG q L m)
    (hADC : Lattice.IsNADC.{u, u, u} q L n)
    (first second : Fin n → Kˣ)
    (hExact : HeHuRepresentsExactlyOne first second a.valueUnit) :
    (Lattice.Represents q (BONG.coefficientDiagonalSpace first)
        L (heHuOMaximalLattice first) ∧
      ¬ Lattice.Represents q (BONG.coefficientDiagonalSpace second)
        L (heHuOMaximalLattice second)) ∨
    (¬ Lattice.Represents q (BONG.coefficientDiagonalSpace first)
        L (heHuOMaximalLattice first) ∧
      Lattice.Represents q (BONG.coefficientDiagonalSpace second)
        L (heHuOMaximalLattice second)) := by
  have hFirst :=
    a.heADCMaximal_represents_iff_diagonalRepresents hADC first
  have hSecond :=
    a.heADCMaximal_represents_iff_diagonalRepresents hADC second
  rcases hExact with ⟨hRep, hNot⟩ | ⟨hNot, hRep⟩
  · exact Or.inl ⟨hFirst.mpr hRep, fun h ↦ hNot (hSecond.mp h)⟩
  · exact Or.inr ⟨fun h ↦ hNot (hFirst.mp h), hSecond.mpr hRep⟩

/-- He, Lemma 4.6(i), even rank and corank two. The determinant hypothesis
is the ordinary-determinant translation used in Lemma 4.5(i). -/
theorem heADC2025Lemma46iEvenCorankTwo
    (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (c : Kˣ) (hdefined : HeHuEvenSecondDefined k c)
    (hdet : IsSquare
      (-diagonalUnitDeterminant a.valueUnit *
        diagonalUnitDeterminant (heADCW1Even k c))) :
    (Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Even k c))
        L (heADCN1Even k c).lattice ∧
      ¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Even k c hdefined))
        L (heADCN2Even k c hdefined).lattice) ∨
    (¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Even k c))
        L (heADCN1Even k c).lattice ∧
      Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Even k c hdefined))
        L (heADCN2Even k c hdefined).lattice) := by
  apply a.heADC2025Lemma46i_of_diagonalExactlyOne hADC
  exact heADC2025Lemma45iCodimensionTwo
    (heADCW1Even k c) (heADCW2Even k c hdefined)
    (heADC2025Proposition42iEven k c hdefined) a.valueUnit hdet

/-- He, Lemma 4.6(i), odd rank and corank one. -/
theorem heADC2025Lemma46iOddCorankOne
    (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) (c : Kˣ) :
    (Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Odd k c))
        L (heADCN1Odd k c).lattice ∧
      ¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Odd k c))
        L (heADCN2Odd k c).lattice) ∨
    (¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Odd k c))
        L (heADCN1Odd k c).lattice ∧
      Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Odd k c))
        L (heADCN2Odd k c).lattice) := by
  apply a.heADC2025Lemma46i_of_diagonalExactlyOne hADC
  exact heADC2025Lemma45iCodimensionOne
    (heADCW1Odd k c) (heADCW2Odd k c)
    (heADC2025Proposition42iOdd k c) a.valueUnit

/-- He, Lemma 4.6(i), odd rank and corank two. -/
theorem heADC2025Lemma46iOddCorankTwo
    (k : Nat) (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) (c : Kˣ)
    (hdet : IsSquare
      (-diagonalUnitDeterminant a.valueUnit *
        diagonalUnitDeterminant (heADCW1Odd k c))) :
    (Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Odd k c))
        L (heADCN1Odd k c).lattice ∧
      ¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Odd k c))
        L (heADCN2Odd k c).lattice) ∨
    (¬ Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW1Odd k c))
        L (heADCN1Odd k c).lattice ∧
      Lattice.Represents q
        (BONG.coefficientDiagonalSpace (heADCW2Odd k c))
        L (heADCN2Odd k c).lattice) := by
  apply a.heADC2025Lemma46i_of_diagonalExactlyOne hADC
  exact heADC2025Lemma45iCodimensionTwo
    (heADCW1Odd k c) (heADCW2Odd k c)
    (heADC2025Proposition42iOdd k c) a.valueUnit hdet

/-- The actual-lattice lifting step in Lemma 4.6(ii). Equal-rank diagonal
representation in `hLarge` records the premise that the source ambient space
is the unique excluding space from Proposition 4.2(iii). -/
private theorem heADC2025Lemma46ii_of_missesExactly
    {n : Nat} (a : GoodBONG q L (n + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L n)
    (excluded : Fin n → Kˣ) (large : Fin (n + 2) → Kˣ)
    (hMisses : HeHuMissesExactly excluded large)
    (hLarge : DiagonalRepresents
      (diagonalUnitCoefficients large)
      (diagonalUnitCoefficients a.valueUnit))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (b : GoodBONG r N n) (hN : Lattice.IsIntegral r N)
    (hNotExceptional : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients excluded)) :
    Lattice.Represents q r L N := by
  apply hADC.represents r N b.toBONG.length_eq_finrank.symm hN
  have hDiagonal :=
    (hMisses.represents_other b.valueUnit hNotExceptional).trans hLarge
  exact
    (show q.Represents
        (BONG.coefficientDiagonalSpace a.valueUnit) from
      ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩).trans
      (((QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        b.valueUnit a.valueUnit).2 hDiagonal).trans
        ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩)

/-- He, Lemma 4.6(ii), even first column: a source on `W_1^(n+2)(c)`
represents every rank-`n` lattice outside `W_2^n(c)`. -/
theorem heADC2025Lemma46iiEvenFirst
    (k : Nat) (a : GoodBONG q L ((2 * k + 2) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2))
    (c : Kˣ) (hdefined : HeHuEvenSecondDefined k c)
    (hLarge : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
          2 * (k + 1) + 2 = (2 * k + 2) + 2)
          (heADCW1Even (k + 1) c)))
      (diagonalUnitCoefficients a.valueUnit))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (b : GoodBONG r N (2 * k + 2)) (hN : Lattice.IsIntegral r N)
    (hNotExceptional : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW2Even k c hdefined))) :
    Lattice.Represents q r L N := by
  exact a.heADC2025Lemma46ii_of_missesExactly hADC
    (heADCW2Even k c hdefined)
    (heHuFinFamilyCast (by omega :
      2 * (k + 1) + 2 = (2 * k + 2) + 2)
      (heADCW1Even (k + 1) c))
    (heADC2025Proposition42iiiEvenSecond k c hdefined).exactness
    hLarge b hN hNotExceptional

/-- He, Lemma 4.6(ii), even second column: a source on `W_2^(n+2)(c)`
represents every rank-`n` lattice outside `W_1^n(c)`. -/
theorem heADC2025Lemma46iiEvenSecond
    (k : Nat) (a : GoodBONG q L ((2 * k + 2) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 2)) (c : Kˣ)
    (hLarge : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
          2 * (k + 1) + 2 = (2 * k + 2) + 2)
          (heADCW2Even (k + 1) c (Or.inl (Nat.succ_pos k)))))
      (diagonalUnitCoefficients a.valueUnit))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (b : GoodBONG r N (2 * k + 2)) (hN : Lattice.IsIntegral r N)
    (hNotExceptional : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW1Even k c))) :
    Lattice.Represents q r L N := by
  exact a.heADC2025Lemma46ii_of_missesExactly hADC
    (heADCW1Even k c)
    (heHuFinFamilyCast (by omega :
      2 * (k + 1) + 2 = (2 * k + 2) + 2)
      (heADCW2Even (k + 1) c (Or.inl (Nat.succ_pos k))))
    (heADC2025Proposition42iiiEvenFirst k c).exactness
    hLarge b hN hNotExceptional

/-- He, Lemma 4.6(ii), odd first column: a source on `W_1^(n+2)(c)`
represents every rank-`n` lattice outside `W_2^n(c)`. -/
theorem heADC2025Lemma46iiOddFirst
    (k : Nat) (a : GoodBONG q L ((2 * k + 3) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) (c : Kˣ)
    (hLarge : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
          2 * (k + 1) + 3 = (2 * k + 3) + 2)
          (heADCW1Odd (k + 1) c)))
      (diagonalUnitCoefficients a.valueUnit))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (b : GoodBONG r N (2 * k + 3)) (hN : Lattice.IsIntegral r N)
    (hNotExceptional : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW2Odd k c))) :
    Lattice.Represents q r L N := by
  exact a.heADC2025Lemma46ii_of_missesExactly hADC
    (heADCW2Odd k c)
    (heHuFinFamilyCast (by omega :
      2 * (k + 1) + 3 = (2 * k + 3) + 2)
      (heADCW1Odd (k + 1) c))
    (heADC2025Proposition42iiiOddSecond k c).exactness
    hLarge b hN hNotExceptional

/-- He, Lemma 4.6(ii), odd second column: a source on `W_2^(n+2)(c)`
represents every rank-`n` lattice outside `W_1^n(c)`. -/
theorem heADC2025Lemma46iiOddSecond
    (k : Nat) (a : GoodBONG q L ((2 * k + 3) + 2))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) (c : Kˣ)
    (hLarge : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
          2 * (k + 1) + 3 = (2 * k + 3) + 2)
          (heADCW2Odd (k + 1) c)))
      (diagonalUnitCoefficients a.valueUnit))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (b : GoodBONG r N (2 * k + 3)) (hN : Lattice.IsIntegral r N)
    (hNotExceptional : ¬ DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heADCW1Odd k c))) :
    Lattice.Represents q r L N := by
  exact a.heADC2025Lemma46ii_of_missesExactly hADC
    (heADCW1Odd k c)
    (heHuFinFamilyCast (by omega :
      2 * (k + 1) + 3 = (2 * k + 3) + 2)
      (heADCW2Odd (k + 1) c))
    (heADC2025Proposition42iiiOddFirst k c).exactness
    hLarge b hN hNotExceptional

end BONG.GoodBONG

end Bong
