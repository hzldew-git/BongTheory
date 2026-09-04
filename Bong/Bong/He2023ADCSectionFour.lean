/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022PublishedTestingSet
import Bong.Bong.HeHu2022Lemma313
import Bong.Lattice.NADC

/-!
# He (2025), Section 4: maximal lattices and local `n`-ADC

This file gives ADC-numbered endpoints for the dyadic part of Section 4 of
the published paper.  The space classification and the exceptional
codimension-two targets are shared with the fully checked He--Hu development;
the lattice statements are obtained from the definition of `n`-ADC rather
than recorded as fresh assumptions.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- He, Definition 4.1: the first even-dimensional ambient-space family. -/
abbrev heADCW1Even (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ :=
  heHuEvenFirst pairs c

/-- He, Definition 4.1: the second even-dimensional ambient-space family. -/
noncomputable abbrev heADCW2Even (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    Fin (2 * pairs + 2) → Kˣ :=
  heHuEvenSecond pairs c hdefined

/-- He, Definition 4.1: the first odd-dimensional ambient-space family. -/
abbrev heADCW1Odd (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  heHuOddFirst pairs c

/-- He, Definition 4.1: the second odd-dimensional ambient-space family. -/
noncomputable abbrev heADCW2Odd (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  heHuOddSecond pairs c

/-- He, Definition 4.1: the maximal lattice `N_1` in the first even
ambient-space family. -/
noncomputable abbrev heADCN1Even (pairs : Nat) (c : Kˣ) :=
  heHuEvenFirstMaximalModel (K := K) pairs c

/-- He, Definition 4.1: the maximal lattice `N_2` in the second even
ambient-space family. -/
noncomputable abbrev heADCN2Even (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :=
  heHuEvenSecondMaximalModel (K := K) pairs c hdefined

/-- He, Definition 4.1: the maximal lattice `N_1` in the first odd
ambient-space family. -/
noncomputable abbrev heADCN1Odd (pairs : Nat) (c : Kˣ) :=
  heHuOddFirstMaximalModel (K := K) pairs c

/-- He, Definition 4.1: the maximal lattice `N_2` in the second odd
ambient-space family. -/
noncomputable abbrev heADCN2Odd (pairs : Nat) (c : Kˣ) :=
  heHuOddSecondMaximalModel (K := K) pairs c

/-- He, Proposition 4.2(i), odd-dimensional dyadic space table. -/
theorem heADC2025Proposition42iOdd (pairs : Nat) (c : Kˣ) :
    HeHuSpacePairProperties
      (heADCW1Odd (K := K) pairs c) (heADCW2Odd (K := K) pairs c) :=
  heHu2022Definition34Proposition35Odd pairs c

/-- He, Proposition 4.2(i), even-dimensional dyadic space table. -/
theorem heADC2025Proposition42iEven (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    HeHuSpacePairProperties
      (heADCW1Even (K := K) pairs c)
      (heADCW2Even (K := K) pairs c hdefined) :=
  heHu2022Definition34Proposition35Even pairs c hdefined

/-- He, Proposition 4.2(ii), even-dimensional exhaustion. -/
theorem heADC2025Proposition42iiEven (pairs : Nat)
    (w : Fin (2 * pairs + 2) → Kˣ) :
    ∃ c : Kˣ,
      DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heADCW1Even (K := K) pairs c)) ∨
        ∃ hdefined : HeHuEvenSecondDefined pairs c,
          DiagonalRepresents
            (diagonalUnitCoefficients w)
            (diagonalUnitCoefficients
              (heADCW2Even (K := K) pairs c hdefined)) :=
  heHu2022Proposition35iiEven pairs w

/-- He, Proposition 4.2(ii), odd-dimensional exhaustion. -/
theorem heADC2025Proposition42iiOdd (pairs : Nat)
    (w : Fin (2 * pairs + 3) → Kˣ) :
    ∃ c : Kˣ,
      DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heADCW1Odd (K := K) pairs c)) ∨
        DiagonalRepresents
          (diagonalUnitCoefficients w)
          (diagonalUnitCoefficients (heADCW2Odd (K := K) pairs c)) :=
  heHu2022Proposition35iiOdd pairs w

/-- He, Proposition 4.2(iii), odd first-column exceptional target. -/
theorem heADC2025Proposition42iiiOddFirst (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heADCW1Odd (K := K) pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heADCW2Odd (K := K) (pairs + 1) c)) :=
  heHu2022Proposition35iiiOddFirst pairs c

/-- He, Proposition 4.2(iii), odd second-column exceptional target. -/
theorem heADC2025Proposition42iiiOddSecond (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heADCW2Odd (K := K) pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heADCW1Odd (K := K) (pairs + 1) c)) :=
  heHu2022Proposition35iiiOddSecond pairs c

/-- He, Proposition 4.2(iii), even first-column exceptional target. -/
theorem heADC2025Proposition42iiiEvenFirst (pairs : Nat) (c : Kˣ) :
    HeHuUniqueExcludingTarget
      (heADCW1Even (K := K) pairs c)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heHuEvenSecondNext (K := K) pairs c)) :=
  heHu2022Proposition35iiiEvenFirst pairs c

/-- He, Proposition 4.2(iii), even second-column exceptional target. -/
theorem heADC2025Proposition42iiiEvenSecond (pairs : Nat) (c : Kˣ)
    (hdefined : HeHuEvenSecondDefined pairs c) :
    HeHuUniqueExcludingTarget
      (heADCW2Even (K := K) pairs c hdefined)
      (heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heADCW1Even (K := K) (pairs + 1) c)) :=
  heHu2022Proposition35iiiEvenSecond pairs c hdefined

/-- He, Remark 4.3: the number of odd-rank rows in the finite published
dyadic table. -/
theorem heADC2025Remark43OddCard
    (I : Type u) [Fintype I] :
    Fintype.card (HeHuPublishedOddTestingIndex I) =
      4 * Fintype.card I :=
  card_heHuPublishedOddTestingIndex I

/-- He, Remark 4.3: the number of even-rank rows above rank two. -/
theorem heADC2025Remark43EvenCardOfPos
    {I : Type u} [Fintype I] (U : I → Kˣ) {pairs : Nat}
    (hpairs : 0 < pairs) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U pairs) =
      4 * Fintype.card I :=
  card_heHuPublishedEvenTestingIndex_of_pos U hpairs

/-- He, Remark 4.3: the binary table omits its unique undefined entry. -/
theorem heADC2025Remark43EvenCardZero
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U) :
    Fintype.card (HeHuPublishedEvenTestingIndex (K := K) U 0) =
      4 * Fintype.card I - 1 :=
  card_heHuPublishedEvenTestingIndex_zero U hU

/-- He, Remark 4.3: every row in the finite even table is maximal. -/
theorem heADC2025Remark43EvenMaximal
    {I : Type u} [Fintype I] {U : I → Kˣ} {pairs : Nat}
    (i : HeHuPublishedEvenTestingIndex (K := K) U pairs) :
    (HeHuPublishedEvenTestingIndex.model (K := K) i).IsOMaximal :=
  HeHuPublishedEvenTestingIndex.model_isOMaximal i

/-- He, Remark 4.3: every row in the finite odd table is maximal. -/
theorem heADC2025Remark43OddMaximal
    {I : Type u} [Fintype I] {U : I → Kˣ} {pairs : Nat}
    (i : HeHuPublishedOddTestingIndex I) :
    (HeHuPublishedOddTestingIndex.model
      (K := K) (U := U) (pairs := pairs) i).IsOMaximal :=
  HeHuPublishedOddTestingIndex.model_isOMaximal i

/-- He, Lemma 4.4(i), for the finite even published table. -/
theorem heADC2025Lemma44iEven
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat} {i j : HeHuPublishedEvenTestingIndex (K := K) U pairs} :
    (HeHuPublishedEvenTestingIndex.model (K := K) i).IsAmbientlyIsometric
        (HeHuPublishedEvenTestingIndex.model (K := K) j) ↔ i = j := by
  constructor
  · exact
      Lattice.QuadraticLatticeModel.heHuPublishedEven_model_eq_of_ambientlyIsometric
        U hU
  · rintro rfl
    exact Lattice.QuadraticLatticeModel.IsAmbientlyIsometric.refl _

/-- He, Lemma 4.4(i), for the finite odd published table. -/
theorem heADC2025Lemma44iOdd
    {I : Type u} [Fintype I] (U : I → Kˣ)
    (hU : IsHeHuCompleteUnitRepresentativeSystem (K := K) U)
    {pairs : Nat} {i j : HeHuPublishedOddTestingIndex I} :
    (HeHuPublishedOddTestingIndex.model
        (K := K) (U := U) (pairs := pairs) i).IsAmbientlyIsometric
        (HeHuPublishedOddTestingIndex.model
          (K := K) (U := U) (pairs := pairs) j) ↔ i = j := by
  constructor
  · exact
      Lattice.QuadraticLatticeModel.heHuPublishedOdd_model_eq_of_ambientlyIsometric
        U hU
  · rintro rfl
    exact Lattice.QuadraticLatticeModel.IsAmbientlyIsometric.refl _

/-- He, Lemma 4.5(i), in codimension one. -/
theorem heADC2025Lemma45iCodimensionOne {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 1) → Kˣ) :
    HeHuRepresentsExactlyOne first second target :=
  heHu2022Lemma313CodimensionOne first second pair target

/-- He, Lemma 4.5(i), in the exceptional codimension-two determinant
class. -/
theorem heADC2025Lemma45iCodimensionTwo {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 2) → Kˣ)
    (hdet : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant first)) :
    HeHuRepresentsExactlyOne first second target :=
  heHu2022Lemma313CodimensionTwo first second pair target hdet

namespace Lattice.QuadraticLatticeModel

/-- Lattice-level version of representing exactly one of two objects. -/
def RepresentsExactlyOne
    (X A B : QuadraticLatticeModel (K := K)) : Prop :=
  (X.Represents A ∧ ¬ X.Represents B) ∨
    (¬ X.Represents A ∧ X.Represents B)

/-- Ambient-space version of representing exactly one of two objects. -/
def AmbientlyRepresentsExactlyOne
    (X A B : QuadraticLatticeModel (K := K)) : Prop :=
  (X.AmbientlyRepresents A ∧ ¬ X.AmbientlyRepresents B) ∨
    (¬ X.AmbientlyRepresents A ∧ X.AmbientlyRepresents B)

/-- He, Lemma 4.6(i): `n`-ADC lifts the exactly-one statement from
ambient spaces to integral rank-`n` lattices. -/
theorem IsNADC.representsExactlyOne_of_ambient
    {X A B : QuadraticLatticeModel (K := K)} {n : Nat}
    (hX : X.IsNADC n)
    (hArank : A.rank = n) (hAintegral : A.IsIntegral)
    (hBrank : B.rank = n) (hBintegral : B.IsIntegral)
    (hAmbient : X.AmbientlyRepresentsExactlyOne A B) :
    X.RepresentsExactlyOne A B := by
  rcases hAmbient with hfirst | hsecond
  · left
    refine ⟨hX.represents hArank hAintegral hfirst.1, ?_⟩
    exact fun hrep => hfirst.2 hrep.ambient
  · right
    refine ⟨?_, hX.represents hBrank hBintegral hsecond.2⟩
    exact fun hrep => hsecond.1 hrep.ambient

/-- He, Lemma 4.6(ii): `n`-ADC lifts every non-exceptional ambient
representation to an integral representation. -/
theorem IsNADC.represents_every_of_ambient
    {X E : QuadraticLatticeModel (K := K)} {n : Nat}
    (hX : X.IsNADC n)
    (hAmbient : ∀ Y : QuadraticLatticeModel (K := K),
      Y.rank = n → Y.IsIntegral →
      ¬ Y.IsAmbientlyIsometric E → X.AmbientlyRepresents Y) :
    ∀ Y : QuadraticLatticeModel (K := K),
      Y.rank = n → Y.IsIntegral →
      ¬ Y.IsAmbientlyIsometric E → X.Represents Y := by
  intro Y hRank hIntegral hNotExceptional
  exact hX.represents hRank hIntegral
    (hAmbient Y hRank hIntegral hNotExceptional)

end Lattice.QuadraticLatticeModel

end Bong
