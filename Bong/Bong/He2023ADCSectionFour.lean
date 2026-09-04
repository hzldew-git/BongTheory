/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022PublishedTestingSet
import Bong.Bong.HeHu2022Lemma313
import Bong.Bong.HeHu2022Lemma311
import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.DiagonalCodimensionTwoRepresentationProof
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

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

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

/-- He, Lemma 4.4(ii), in the invariant determinant--Hasse form used by
the repository.  Substituting the two published `W` rows reduces the sign
on the right to the paper's Hilbert-symbol equation
`(c',c) = (-1)^(nu'+nu)`. -/
theorem heADC2025Lemma44ii {n : Nat}
    (source : Fin n → Kˣ) (target : Fin (n + 1) → Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) ↔
      diagonalHasseSymbol K target * diagonalHasseSymbol K source *
          hilbertSymbol K (diagonalUnitDeterminant source)
            (diagonalUnitDeterminant target) *
          hilbertSymbol K (diagonalUnitDeterminant target) (-1) = 1 :=
  diagonalCodimensionOneRepresents_iff_sign_eq_one source target

/-- He, Lemma 4.4(iii), before substituting the finite `W` table.  In the
exceptional signed-determinant class, a codimension-two target represents
the source exactly when it is the source plus a hyperbolic plane; outside
that class representation is automatic. -/
theorem heADC2025Lemma44iii {n : Nat}
    (source : Fin n → Kˣ) (target : Fin (n + 2) → Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) ↔
      ¬ IsSquare
          (-diagonalUnitDeterminant target *
            diagonalUnitDeterminant source) ∨
        DiagonalRepresents
          (diagonalUnitCoefficients
            (Fin.append source (heHuHyperbolicPair (K := K))))
          (diagonalUnitCoefficients target) := by
  constructor
  · intro hrep
    by_cases hdet : IsSquare
        (-diagonalUnitDeterminant target *
          diagonalUnitDeterminant source)
    · right
      exact (diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
        source target hdet hrep).symm_of_sameRank
    · exact Or.inl hdet
  · rintro (hdet | hlift)
    · exact dyadicDiagonalCodimensionTwo_represents n source target hdet
    · exact (diagonalRepresents_append_right_prefix source
        (heHuHyperbolicPair (K := K))).trans hlift

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

/-- The direction of "represents exactly one" used in He, Lemma 4.5(ii):
the common smaller space is represented by exactly one member of the
ordered larger pair. -/
def HeADCIsRepresentedByExactlyOne {m n : Nat}
    (source : Fin m → Kˣ) (first second : Fin n → Kˣ) : Prop :=
  (DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients first) ∧
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients second)) ∨
  (¬ DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients first) ∧
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients second))

private theorem heADCIntUnitsExactlyOneEqOne
    (x y : ℤˣ) (hxy : x ≠ y) :
    (x = 1 ∧ y ≠ 1) ∨ (x ≠ 1 ∧ y = 1) := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact Or.inl ⟨hx, by simpa [hy]⟩
  · exact Or.inr ⟨by simpa [hx], hy⟩
  · exact (hxy (hx.trans hy.symm)).elim

/-- He, Lemma 4.5(ii), codimension-one case. -/
theorem heADC2025Lemma45iiCodimensionOne {n : Nat}
    (source : Fin n → Kˣ)
    (first second : Fin (n + 1) → Kˣ)
    (pair : HeHuSpacePairProperties first second) :
    HeADCIsRepresentedByExactlyOne source first second := by
  let Hs := diagonalHasseSymbol K source
  let H1 := diagonalHasseSymbol K first
  let H2 := diagonalHasseSymbol K second
  let Ds := diagonalUnitDeterminant source
  let D1 := diagonalUnitDeterminant first
  let D2 := diagonalUnitDeterminant second
  let B1 := hilbertSymbol K Ds D1
  let B2 := hilbertSymbol K Ds D2
  let C1 := hilbertSymbol K D1 (-1)
  let C2 := hilbertSymbol K D2 (-1)
  let s1 := H1 * Hs * B1 * C1
  let s2 := H2 * Hs * B2 * C2
  have hhasse : H1 ≠ H2 := by
    intro heq
    apply pair.nonisometric
    exact dyadicDiagonalClassification_represents (n + 1) second first
      pair.determinantSquare (by simpa only [H1, H2] using heq.symm)
  have hB : B1 = B2 := by
    apply hilbertSymbol_eq_of_isSquare_mul_right
    simpa only [D1, D2, mul_comm] using pair.determinantSquare
  have hC : C1 = C2 := by
    apply hilbertSymbol_eq_of_isSquare_mul_left
    simpa only [D1, D2, mul_comm] using pair.determinantSquare
  have hsign : s1 ≠ s2 := by
    intro heq
    apply hhasse
    have hcancel : H1 * (Hs * B1 * C1) =
        H2 * (Hs * B1 * C1) := by
      simpa only [s1, s2, hB, hC, mul_assoc, mul_comm,
        mul_left_comm] using heq
    exact mul_right_cancel hcancel
  have hfirst :
      DiagonalRepresents
          (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients first) ↔ s1 = 1 := by
    simpa only [s1, H1, Hs, B1, C1, Ds, D1] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one source first
  have hsecond :
      DiagonalRepresents
          (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients second) ↔ s2 = 1 := by
    simpa only [s2, H2, Hs, B2, C2, Ds, D2] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one source second
  rcases heADCIntUnitsExactlyOneEqOne s1 s2 hsign with hleft | hright
  · exact Or.inl ⟨hfirst.2 hleft.1,
      fun h => hleft.2 (hsecond.1 h)⟩
  · exact Or.inr ⟨(fun h => hright.1 (hfirst.1 h)),
      hsecond.2 hright.2⟩

/-- He, Lemma 4.5(ii), codimension-two case.  The determinant hypothesis is
the repository's ordinary-determinant translation of the paper's signed
determinant equality. -/
theorem heADC2025Lemma45iiCodimensionTwo {n : Nat}
    (source : Fin n → Kˣ)
    (first second : Fin (n + 2) → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (hdet : IsSquare
      (-diagonalUnitDeterminant first *
        diagonalUnitDeterminant source)) :
    HeADCIsRepresentedByExactlyOne source first second := by
  let hyperbolic := heHuHyperbolicPair (K := K)
  let extended := Fin.append source hyperbolic
  have hhyperbolic : diagonalUnitDeterminant hyperbolic = -1 := by
    simp [hyperbolic, heHuHyperbolicPair, diagonalUnitDeterminant,
      Fin.prod_univ_two]
  have hextendedDet : IsSquare
      (diagonalUnitDeterminant extended *
        diagonalUnitDeterminant first) := by
    change IsSquare
      (diagonalUnitDeterminant (Fin.append source hyperbolic) *
        diagonalUnitDeterminant first)
    rw [diagonalUnitDeterminant_append, hhyperbolic]
    simpa only [mul_neg, neg_mul, one_mul, mul_one, mul_comm,
      mul_left_comm, mul_assoc] using hdet
  have hdetSecond : IsSquare
      (-diagonalUnitDeterminant second *
        diagonalUnitDeterminant source) := by
    have h := isSquare_mul_trans
      (-diagonalUnitDeterminant source)
      (diagonalUnitDeterminant first)
      (diagonalUnitDeterminant second)
      (by simpa [mul_comm] using hdet)
      (by simpa only [mul_comm] using pair.determinantSquare)
    simpa [mul_comm] using h
  have hsourceExtended : DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients extended) := by
    exact diagonalRepresents_append_right_prefix source hyperbolic
  rcases pair.exhaustive extended hextendedDet with hfirst | hsecond
  · left
    refine ⟨hsourceExtended.trans hfirst, ?_⟩
    intro hrepSecond
    apply pair.nonisometric
    exact (diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
      source second hdetSecond hrepSecond).trans hfirst
  · right
    refine ⟨?_, hsourceExtended.trans hsecond⟩
    intro hrepFirst
    apply pair.nonisometric
    exact ((diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
      source first hdet hrepFirst).trans hsecond).symm_of_sameRank

/-! ## The explicit dyadic maximal-lattice table -/

set_option linter.defProp false

/-- He, Lemma 4.9(i), even first-column square row. -/
def heADC2025Lemma49EvenFirstOne :=
  heHu2022Proposition37EvenFirstOne (K := K)

/-- He, Lemma 4.9(i), even first-column discriminant row. -/
def heADC2025Lemma49EvenFirstDelta :=
  heHu2022Proposition37EvenFirstDelta (K := K)

/-- He, Lemma 4.9(i), even second-column square row. -/
def heADC2025Lemma49EvenSecondOne :=
  heHu2022Proposition37EvenSecondOne (K := K)

/-- He, Lemma 4.9(i), even second-column discriminant row. -/
def heADC2025Lemma49EvenSecondDelta :=
  heHu2022Proposition37EvenSecondDelta (K := K)

/-- He, Lemma 4.9(i), the two generic even unit rows. -/
def heADC2025Lemma49EvenGeneric :=
  heHu2022Proposition37EvenGeneric (K := K)

/-- He, Lemma 4.9(i), the two even unit-uniformizer rows. -/
def heADC2025Lemma49EvenUnitUniformizer :=
  heHu2022Proposition37EvenUnitUniformizer (K := K)

/-- He, Lemma 4.9(i), odd first-column unit row. -/
def heADC2025Lemma49OddFirstUnit :=
  heHu2022Proposition37OddFirstUnit (K := K)

/-- He, Lemma 4.9(i), odd first-column unit-uniformizer row. -/
def heADC2025Lemma49OddFirstUnitUniformizer :=
  heHu2022Proposition37OddFirstUnitUniformizer (K := K)

/-- He, Lemma 4.9(i), odd second-column unit row. -/
def heADC2025Lemma49OddSecondUnit
    [GoodBONGClassificationLaws.{u, u, u} K] :=
  heHu2022Proposition37OddSecondUnit (K := K)

/-- He, Lemma 4.9(i), odd second-column unit-uniformizer row. -/
def heADC2025Lemma49OddSecondUnitUniformizer :=
  heHu2022Proposition37OddSecondUnitUniformizer (K := K)

set_option linter.defProp true

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
