/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Proposition35iii
import Bong.Bong.DiagonalRepresentationParityProof
import Bong.Bong.DiagonalTailCancellation

/-!
# He--Hu (2024), Lemma 3.13

Two nonisometric spaces in one determinant square class are complementary
representation tests in ranks one and two above.  The codimension-one case
is the determinant--Hasse sign criterion.  In codimension two, after adding
a hyperbolic plane to both spaces, local classification supplies the two
possible target classes and Witt cancellation keeps them distinct.
-/

namespace Bong

open Dyadic BONG.GoodBONG
open AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A target represents exactly one member of an ordered pair of diagonal
spaces.  The disjunction records which member is represented. -/
def HeHuRepresentsExactlyOne {m n : Nat}
    (first second : Fin m → Kˣ) (target : Fin n → Kˣ) : Prop :=
  (DiagonalRepresents
      (diagonalUnitCoefficients first)
      (diagonalUnitCoefficients target) ∧
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients target)) ∨
  (¬ DiagonalRepresents
      (diagonalUnitCoefficients first)
      (diagonalUnitCoefficients target) ∧
    DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients target))

/-- Unequal integer units have complementary truth values for equality to
one. -/
private theorem intUnits_exactlyOne_eq_one (x y : ℤˣ) (hxy : x ≠ y) :
    (x = 1 ∧ y ≠ 1) ∨ (x ≠ 1 ∧ y = 1) := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact Or.inl ⟨hx, by simpa [hy]⟩
  · exact Or.inr ⟨by simpa [hx], hy⟩
  · exact (hxy (hx.trans hy.symm)).elim

/-- Lemma 3.13 in codimension one, for any pair carrying the complete
determinant-class package from Definition 3.4. -/
theorem heHuRepresentsExactlyOne_codimensionOne {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 1) → Kˣ) :
    HeHuRepresentsExactlyOne first second target := by
  let Ht := diagonalHasseSymbol K target
  let H1 := diagonalHasseSymbol K first
  let H2 := diagonalHasseSymbol K second
  let D1 := diagonalUnitDeterminant first
  let D2 := diagonalUnitDeterminant second
  let Dt := diagonalUnitDeterminant target
  let B1 := hilbertSymbol K D1 Dt
  let B2 := hilbertSymbol K D2 Dt
  let C := hilbertSymbol K Dt (-1)
  let s1 := Ht * H1 * B1 * C
  let s2 := Ht * H2 * B2 * C
  have hhasse : H1 ≠ H2 := by
    intro heq
    apply pair.nonisometric
    exact dyadicDiagonalClassification_represents n second first
      pair.determinantSquare (by simpa only [H1, H2] using heq.symm)
  have hbilinear : B1 = B2 := by
    apply hilbertSymbol_eq_of_isSquare_mul_left
    simpa only [D1, D2, mul_comm] using pair.determinantSquare
  have hsign : s1 ≠ s2 := by
    intro heq
    apply hhasse
    have hcancel : H1 * (Ht * B1 * C) = H2 * (Ht * B1 * C) := by
      simpa only [s1, s2, hbilinear, mul_assoc, mul_comm, mul_left_comm]
        using heq
    exact mul_right_cancel hcancel
  have hfirst :
      DiagonalRepresents
          (diagonalUnitCoefficients first)
          (diagonalUnitCoefficients target) ↔ s1 = 1 := by
    simpa only [s1, Ht, H1, B1, C, D1, Dt] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one first target
  have hsecond :
      DiagonalRepresents
          (diagonalUnitCoefficients second)
          (diagonalUnitCoefficients target) ↔ s2 = 1 := by
    simpa only [s2, Ht, H2, B2, C, D2, Dt] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one second target
  rcases intUnits_exactlyOne_eq_one s1 s2 hsign with hleft | hright
  · exact Or.inl ⟨hfirst.2 hleft.1, fun h => hleft.2 (hsecond.1 h)⟩
  · exact Or.inr ⟨(fun h => hright.1 (hfirst.1 h)), hsecond.2 hright.2⟩

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- The evident source copy in an appended diagonal block. -/
theorem diagonalRepresents_append_right_prefix {m r : Nat}
    (source : Fin m → Kˣ) (tail : Fin r → Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients (Fin.append source tail)) := by
  have hprefix := DiagonalRepresents.prefixOfLE
    (diagonalUnitCoefficients (Fin.append source tail))
    (by omega : m ≤ m + r)
  convert hprefix using 1
  funext i
  change (source i : K) =
    (Fin.append source tail (Fin.castAdd r i) : Kˣ)
  rw [Fin.append_left]

/-- Appending the same nondegenerate diagonal block preserves the complete
two-class package.  This is the right-handed form of
`HeHuSpacePairProperties.append`. -/
theorem HeHuSpacePairProperties.appendRight {n r : Nat}
    {first second : Fin n → Kˣ}
    (pair : HeHuSpacePairProperties first second)
    (common : Fin r → Kˣ) :
    HeHuSpacePairProperties
      (Fin.append first common) (Fin.append second common) := by
  apply HeHuSpacePairProperties.of_det_not
  · rw [diagonalUnitDeterminant_append,
      diagonalUnitDeterminant_append]
    have hcommon : IsSquare (diagonalUnitDeterminant common ^ 2) :=
      ⟨diagonalUnitDeterminant common,
        pow_two (diagonalUnitDeterminant common)⟩
    have hproduct := pair.determinantSquare.mul hcommon
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hproduct
  · intro hrep
    apply pair.nonisometric
    apply DiagonalRepresents.cancel_common_append
        (diagonalUnitCoefficients second)
        (diagonalUnitCoefficients first)
        (diagonalUnitCoefficients common)
    · intro i
      exact Units.ne_zero (second i)
    · intro i
      exact Units.ne_zero (first i)
    · intro i
      exact Units.ne_zero (common i)
    · simpa only [diagonalUnitCoefficients_append] using hrep

/-- Lemma 3.13 in its exceptional codimension-two determinant class. -/
theorem heHuRepresentsExactlyOne_codimensionTwo {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 2) → Kˣ)
    (hdet : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant first)) :
    HeHuRepresentsExactlyOne first second target := by
  let hyperbolic := heHuHyperbolicPair (K := K)
  let largeFirst := Fin.append first hyperbolic
  let largeSecond := Fin.append second hyperbolic
  have largePair : HeHuSpacePairProperties largeFirst largeSecond :=
    pair.appendRight hyperbolic
  have hhyperbolic : diagonalUnitDeterminant hyperbolic = -1 := by
    simp [hyperbolic, heHuHyperbolicPair, diagonalUnitDeterminant,
      Fin.prod_univ_two]
  have htargetClass : IsSquare
      (diagonalUnitDeterminant target *
        diagonalUnitDeterminant largeFirst) := by
    change IsSquare
      (diagonalUnitDeterminant target *
        diagonalUnitDeterminant (Fin.append first hyperbolic))
    rw [diagonalUnitDeterminant_append, hhyperbolic]
    simpa only [mul_neg, neg_mul, one_mul, mul_one, mul_comm,
      mul_left_comm, mul_assoc]
      using hdet
  have hdetSecond : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant second) := by
    apply isSquare_mul_trans
        (-diagonalUnitDeterminant target)
        (diagonalUnitDeterminant first)
        (diagonalUnitDeterminant second)
    · exact hdet
    · simpa only [mul_comm] using pair.determinantSquare
  rcases largePair.exhaustive target htargetClass with
      htargetFirst | htargetSecond
  · left
    constructor
    · exact (diagonalRepresents_append_right_prefix first hyperbolic).trans
        htargetFirst.symm_of_sameRank
    · intro hsecond
      apply largePair.nonisometric
      have htargetToSecond :=
        diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
          second target hdetSecond hsecond
      exact htargetToSecond.symm_of_sameRank.trans htargetFirst
  · right
    constructor
    · intro hfirst
      apply largePair.nonisometric
      have htargetToFirst :=
        diagonalRepresents_target_to_appendHyperbolic_of_negativeDetSquare
          first target hdet hfirst
      exact htargetSecond.symm_of_sameRank.trans htargetToFirst
    · exact (diagonalRepresents_append_right_prefix second hyperbolic).trans
        htargetSecond.symm_of_sameRank

/-- He--Hu (2024), Lemma 3.13, codimension-one endpoint. -/
theorem heHu2022Lemma313CodimensionOne {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 1) → Kˣ) :
    HeHuRepresentsExactlyOne first second target :=
  heHuRepresentsExactlyOne_codimensionOne first second pair target

/-- He--Hu (2024), Lemma 3.13, codimension-two endpoint under the paper's
condition `det V = -D`, expressed invariantly as a square-class equality. -/
theorem heHu2022Lemma313CodimensionTwo {n : Nat}
    (first second : Fin n → Kˣ)
    (pair : HeHuSpacePairProperties first second)
    (target : Fin (n + 2) → Kˣ)
    (hdet : IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant first)) :
    HeHuRepresentsExactlyOne first second target :=
  heHuRepresentsExactlyOne_codimensionTwo first second pair target hdet

end Bong
