/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma720Maximal
import Bong.Bong.He2023ADCLemma719Models
import Bong.Bong.DiagonalTailCancellation

/-!
# He (2025), Lemma 7.20(iii): the Hilbert-symbol ambient selection

This file proves the paper's equation
`(-1)^nu' = (-1)^nu * (omega,c)` as the exact criterion for the even
space `W_{nu'}(omega)` to occur as a codimension-one subspace of the odd
space `W_nu(c)`.  It is then used to identify the ambient quadratic space
of the named product in Lemma 7.19.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG AlternatingEndpointTower

universe u

namespace HeADC716Column

/-- The paper's sign `(-1)^nu`, where column one is indexed by `nu=1`
and column two by `nu=2`. -/
def paperSign : HeADC716Column → ℤˣ
  | one => -1
  | two => 1

end HeADC716Column

/-- The binary first row embeds in the first odd tail exactly when the
Hilbert symbol of their two parameters is positive. -/
theorem heADC2025Lemma720_firstTail_represents_iff_hilbertOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] (omega c : Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuBinaryFirst omega))
        (diagonalUnitCoefficients (heHuOddFirstTail c)) ↔
      hilbertSymbol K omega c = 1 := by
  let sourceTail : Fin 1 → K := fun _ ↦ (-omega : Kˣ)
  let targetTail : Fin 2 → K :=
    Fin.cons ((-1 : Kˣ) : K) (fun _ : Fin 1 ↦ (c : K))
  have hsource :
      diagonalUnitCoefficients (heHuBinaryFirst omega) =
        Fin.cons (1 : K) sourceTail := by
    funext i
    fin_cases i <;> rfl
  have htarget :
      diagonalUnitCoefficients (heHuOddFirstTail c) =
        Fin.cons (1 : K) targetTail := by
    funext i
    fin_cases i <;> rfl
  have htail :
      DiagonalRepresents sourceTail targetTail ↔
        hilbertSymbol K omega c = 1 := by
    have H := DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (K := K) (-1 : Kˣ) c (-omega)
    simpa only [sourceTail, targetTail, inv_neg, inv_one, neg_mul,
      mul_neg, neg_neg, mul_one, one_mul] using H
  constructor
  · intro hrep
    apply htail.mp
    apply DiagonalRepresents.cancel_common_head (1 : K)
      sourceTail targetTail
    · norm_num
    · intro i
      simp only [sourceTail]
      exact Units.ne_zero (-omega)
    · intro i
      fin_cases i <;> simp [targetTail]
    · rw [← hsource, ← htarget]
      exact hrep
  · intro hhilbert
    have hrep := diagonalRepresents_cons (htail.mpr hhilbert) (1 : K)
    rw [← hsource, ← htarget] at hrep
    exact hrep

/-- After cancelling the common hyperbolic tower, the first published
even and odd rows satisfy the same Hilbert-symbol criterion. -/
theorem heADC2025Lemma720_firstFirst_represents_iff_hilbertOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (pairs : Nat) (omega c : Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heADCW1Even pairs omega))
        (diagonalUnitCoefficients (heADCW1Odd pairs c)) ↔
      hilbertSymbol K omega c = 1 := by
  rw [heADCW1Even, heHuEvenFirst_eq_towerModel,
    heADCW1Odd, heHuOddFirst, diagonalUnitCoefficients_append,
    diagonalUnitCoefficients_append]
  let common := diagonalUnitCoefficients
    (standardHyperbolicEndpointTower (K := K) pairs)
  let source := diagonalUnitCoefficients (heHuBinaryFirst omega)
  let target := diagonalUnitCoefficients (heHuOddFirstTail c)
  have htail := heADC2025Lemma720_firstTail_represents_iff_hilbertOne
    (K := K) omega c
  constructor
  · intro hrep
    apply htail.mp
    exact DiagonalRepresents.cancel_common_prefix common source target
      (fun i ↦ Units.ne_zero _) (fun i ↦ Units.ne_zero _)
      (fun i ↦ Units.ne_zero _) hrep
  · intro hhilbert
    exact (diagonalRepresents_refl common).appendBoth
      (htail.mpr hhilbert)

/-- A fixed codimension-one source is represented by exactly one member
of a complete equal-determinant target pair. -/
def HeADCRepresentsExactlyOneTarget
    {K : Type u} [Field K] {n : Nat}
    (source : Fin n → Kˣ)
    (first second : Fin (n + 1) → Kˣ) : Prop :=
  (DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients first) ∧
    ¬ DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients second)) ∨
  (¬ DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients first) ∧
    DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients second))

private theorem heADCIntUnits_exactlyOne_eq_one
    (x y : ℤˣ) (hxy : x ≠ y) :
    (x = 1 ∧ y ≠ 1) ∨ (x ≠ 1 ∧ y = 1) := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · exact Or.inl ⟨hx, by simp [hy]⟩
  · exact Or.inr ⟨by simp [hx], hy⟩
  · exact (hxy (hx.trans hy.symm)).elim

/-- Target-pair dual of He--Hu Lemma 3.13 in codimension one.  It is
derived from the same determinant--Hasse criterion, not postulated as a
second classification law. -/
theorem heADCRepresentsExactlyOneTarget_codimensionOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] {n : Nat}
    (source : Fin n → Kˣ)
    (first second : Fin (n + 1) → Kˣ)
    (pair : HeHuSpacePairProperties first second) :
    HeADCRepresentsExactlyOneTarget source first second := by
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
    rw [mul_comm]
    exact pair.determinantSquare
  have hC : C1 = C2 := by
    apply hilbertSymbol_eq_of_isSquare_mul_left
    rw [mul_comm]
    exact pair.determinantSquare
  have hsign : s1 ≠ s2 := by
    intro heq
    apply hhasse
    have hcancel : H1 * (Hs * B1 * C1) =
        H2 * (Hs * B1 * C1) := by
      simpa only [s1, s2, hB, hC, mul_assoc, mul_comm,
        mul_left_comm] using heq
    exact mul_right_cancel hcancel
  have hfirst :
      DiagonalRepresents (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients first) ↔ s1 = 1 := by
    simpa only [s1, Hs, H1, B1, C1, Ds, D1] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one source first
  have hsecond :
      DiagonalRepresents (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients second) ↔ s2 = 1 := by
    simpa only [s2, Hs, H2, B2, C2, Ds, D2] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one source second
  rcases heADCIntUnits_exactlyOne_eq_one s1 s2 hsign with hleft | hright
  · exact Or.inl ⟨hfirst.2 hleft.1,
      fun h ↦ hleft.2 (hsecond.1 h)⟩
  · exact Or.inr ⟨(fun h ↦ hright.1 (hfirst.1 h)),
      hsecond.2 hright.2⟩

namespace HeADC716Column

/-- The even-dimensional row used as the base of Lemma 7.20(iii).  Its
pair count is positive, so the second column is always defined. -/
noncomputable def evenCoefficients
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (nu : HeADC716Column) (k : Nat) (c : Kˣ) :
    Fin (2 * (k + 1) + 2) → Kˣ :=
  match nu with
  | one => heADCW1Even (k + 1) c
  | two => heADCW2Even (k + 1) c (Or.inl (by omega))

end HeADC716Column

/-- Positive Hilbert sign selects equal column numbers. -/
theorem heADC2025Lemma720_representationPattern_of_hilbertOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ)
    (hh : hilbertSymbol K omega c = 1) :
    let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
      Or.inl (by omega)
    let S1 := heADCW1Even (k + 1) omega
    let S2 := heADCW2Even (k + 1) omega hdefined
    let T1 := heADCW1Odd (k + 1) c
    let T2 := heADCW2Odd (k + 1) c
    DiagonalRepresents (diagonalUnitCoefficients S1)
        (diagonalUnitCoefficients T1) ∧
      ¬ DiagonalRepresents (diagonalUnitCoefficients S2)
        (diagonalUnitCoefficients T1) ∧
      ¬ DiagonalRepresents (diagonalUnitCoefficients S1)
        (diagonalUnitCoefficients T2) ∧
      DiagonalRepresents (diagonalUnitCoefficients S2)
        (diagonalUnitCoefficients T2) := by
  dsimp only
  let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
    Or.inl (by omega)
  let S1 := heADCW1Even (K := K) (k + 1) omega
  let S2 := heADCW2Even (K := K) (k + 1) omega hdefined
  let T1 := heADCW1Odd (K := K) (k + 1) c
  let T2 := heADCW2Odd (K := K) (k + 1) c
  have h11 : DiagonalRepresents (diagonalUnitCoefficients S1)
      (diagonalUnitCoefficients T1) :=
    (heADC2025Lemma720_firstFirst_represents_iff_hilbertOne
      (K := K) (k + 1) omega c).2 hh
  have sourceChoice1 := heADC2025Lemma45iCodimensionOne S1 S2
    (heADC2025Proposition42iEven (K := K) (k + 1) omega hdefined) T1
  have h21 : ¬ DiagonalRepresents (diagonalUnitCoefficients S2)
      (diagonalUnitCoefficients T1) := by
    rcases sourceChoice1 with hleft | hright
    · exact hleft.2
    · exact fun h ↦ hright.1 h11
  have targetChoice1 := heADCRepresentsExactlyOneTarget_codimensionOne
    S1 T1 T2 (heADC2025Proposition42iOdd (K := K) (k + 1) c)
  have h12 : ¬ DiagonalRepresents (diagonalUnitCoefficients S1)
      (diagonalUnitCoefficients T2) := by
    rcases targetChoice1 with hleft | hright
    · exact hleft.2
    · exact fun h ↦ hright.1 h11
  have targetChoice2 := heADCRepresentsExactlyOneTarget_codimensionOne
    S2 T1 T2 (heADC2025Proposition42iOdd (K := K) (k + 1) c)
  have h22 : DiagonalRepresents (diagonalUnitCoefficients S2)
      (diagonalUnitCoefficients T2) := by
    rcases targetChoice2 with hleft | hright
    · exact (h21 hleft.1).elim
    · exact hright.2
  exact ⟨h11, h21, h12, h22⟩

/-- Negative Hilbert sign selects opposite column numbers. -/
theorem heADC2025Lemma720_representationPattern_of_hilbertNegOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ)
    (hh : hilbertSymbol K omega c = -1) :
    let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
      Or.inl (by omega)
    let S1 := heADCW1Even (k + 1) omega
    let S2 := heADCW2Even (k + 1) omega hdefined
    let T1 := heADCW1Odd (k + 1) c
    let T2 := heADCW2Odd (k + 1) c
    ¬ DiagonalRepresents (diagonalUnitCoefficients S1)
        (diagonalUnitCoefficients T1) ∧
      DiagonalRepresents (diagonalUnitCoefficients S2)
        (diagonalUnitCoefficients T1) ∧
      DiagonalRepresents (diagonalUnitCoefficients S1)
        (diagonalUnitCoefficients T2) ∧
      ¬ DiagonalRepresents (diagonalUnitCoefficients S2)
        (diagonalUnitCoefficients T2) := by
  dsimp only
  let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
    Or.inl (by omega)
  let S1 := heADCW1Even (K := K) (k + 1) omega
  let S2 := heADCW2Even (K := K) (k + 1) omega hdefined
  let T1 := heADCW1Odd (K := K) (k + 1) c
  let T2 := heADCW2Odd (K := K) (k + 1) c
  have h11 : ¬ DiagonalRepresents (diagonalUnitCoefficients S1)
      (diagonalUnitCoefficients T1) := by
    intro hrep
    have hone :=
      (heADC2025Lemma720_firstFirst_represents_iff_hilbertOne
        (K := K) (k + 1) omega c).1 hrep
    rw [hh] at hone
    norm_num at hone
  have sourceChoice1 := heADC2025Lemma45iCodimensionOne S1 S2
    (heADC2025Proposition42iEven (K := K) (k + 1) omega hdefined) T1
  have h21 : DiagonalRepresents (diagonalUnitCoefficients S2)
      (diagonalUnitCoefficients T1) := by
    rcases sourceChoice1 with hleft | hright
    · exact (h11 hleft.1).elim
    · exact hright.2
  have targetChoice1 := heADCRepresentsExactlyOneTarget_codimensionOne
    S1 T1 T2 (heADC2025Proposition42iOdd (K := K) (k + 1) c)
  have h12 : DiagonalRepresents (diagonalUnitCoefficients S1)
      (diagonalUnitCoefficients T2) := by
    rcases targetChoice1 with hleft | hright
    · exact (h11 hleft.1).elim
    · exact hright.2
  have targetChoice2 := heADCRepresentsExactlyOneTarget_codimensionOne
    S2 T1 T2 (heADC2025Proposition42iOdd (K := K) (k + 1) c)
  have h22 : ¬ DiagonalRepresents (diagonalUnitCoefficients S2)
      (diagonalUnitCoefficients T2) := by
    rcases targetChoice2 with hleft | hright
    · exact hleft.2
    · exact fun h ↦ hright.1 h21
  exact ⟨h11, h21, h12, h22⟩

/-- The second even row embeds in the first odd row exactly for negative
Hilbert sign. -/
theorem heADC2025Lemma720_secondFirst_represents_iff_hilbertNegOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) :
    let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
      Or.inl (by omega)
    DiagonalRepresents
        (diagonalUnitCoefficients
          (heADCW2Even (k + 1) omega hdefined))
        (diagonalUnitCoefficients (heADCW1Odd (k + 1) c)) ↔
      hilbertSymbol K omega c = -1 := by
  dsimp only
  let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
    Or.inl (by omega)
  constructor
  · intro hrep
    rcases Int.units_eq_one_or (hilbertSymbol K omega c) with hh | hh
    · have P := heADC2025Lemma720_representationPattern_of_hilbertOne
        (K := K) k omega c hh
      exact (P.2.1 hrep).elim
    · exact hh
  · intro hh
    exact (heADC2025Lemma720_representationPattern_of_hilbertNegOne
      (K := K) k omega c hh).2.1

/-- The first even row embeds in the second odd row exactly for negative
Hilbert sign. -/
theorem heADC2025Lemma720_firstSecond_represents_iff_hilbertNegOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heADCW1Even (k + 1) omega))
        (diagonalUnitCoefficients (heADCW2Odd (k + 1) c)) ↔
      hilbertSymbol K omega c = -1 := by
  constructor
  · intro hrep
    rcases Int.units_eq_one_or (hilbertSymbol K omega c) with hh | hh
    · have P := heADC2025Lemma720_representationPattern_of_hilbertOne
        (K := K) k omega c hh
      exact (P.2.2.1 hrep).elim
    · exact hh
  · intro hh
    exact (heADC2025Lemma720_representationPattern_of_hilbertNegOne
      (K := K) k omega c hh).2.2.1

/-- The second even row embeds in the second odd row exactly for positive
Hilbert sign. -/
theorem heADC2025Lemma720_secondSecond_represents_iff_hilbertOne
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) :
    let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
      Or.inl (by omega)
    DiagonalRepresents
        (diagonalUnitCoefficients
          (heADCW2Even (k + 1) omega hdefined))
        (diagonalUnitCoefficients (heADCW2Odd (k + 1) c)) ↔
      hilbertSymbol K omega c = 1 := by
  dsimp only
  let hdefined : HeHuEvenSecondDefined (k + 1) omega :=
    Or.inl (by omega)
  constructor
  · intro hrep
    rcases Int.units_eq_one_or (hilbertSymbol K omega c) with hh | hh
    · exact hh
    · have P := heADC2025Lemma720_representationPattern_of_hilbertNegOne
        (K := K) k omega c hh
      exact (P.2.2.2 hrep).elim
  · intro hh
    exact (heADC2025Lemma720_representationPattern_of_hilbertOne
      (K := K) k omega c hh).2.2.2

/-- Published form of Lemma 4.4(ii) used in Lemma 7.20(iii).  The
Hilbert-symbol equation selects exactly the represented column. -/
private theorem heADC720Sign_one_one (h : ℤˣ) :
    h = 1 ↔ (-1 : ℤˣ) = -1 * h := by
  rcases Int.units_eq_one_or h with rfl | rfl <;> norm_num

private theorem heADC720Sign_one_two (h : ℤˣ) :
    h = -1 ↔ (-1 : ℤˣ) = 1 * h := by
  rcases Int.units_eq_one_or h with rfl | rfl <;> norm_num

private theorem heADC720Sign_two_one (h : ℤˣ) :
    h = -1 ↔ (1 : ℤˣ) = -1 * h := by
  rcases Int.units_eq_one_or h with rfl | rfl <;> norm_num

private theorem heADC720Sign_two_two (h : ℤˣ) :
    h = 1 ↔ (1 : ℤˣ) = 1 * h := by
  rcases Int.units_eq_one_or h with rfl | rfl <;> norm_num

theorem heADC2025Lemma720_columnRepresentation_iff
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) (nuPrime nu : HeADC716Column) :
    DiagonalRepresents
        (diagonalUnitCoefficients
          (nuPrime.evenCoefficients k omega))
        (diagonalUnitCoefficients
          (nu.coefficients (k + 1) c)) ↔
      nuPrime.paperSign = nu.paperSign * hilbertSymbol K omega c := by
  cases nuPrime <;> cases nu
  · simpa only [HeADC716Column.evenCoefficients,
      HeADC716Column.coefficients, HeADC716Column.paperSign] using
      (heADC2025Lemma720_firstFirst_represents_iff_hilbertOne
        (K := K) (k + 1) omega c).trans
          (heADC720Sign_one_one (hilbertSymbol K omega c))
  · simpa only [HeADC716Column.evenCoefficients,
      HeADC716Column.coefficients, HeADC716Column.paperSign] using
      (heADC2025Lemma720_firstSecond_represents_iff_hilbertNegOne
        (K := K) k omega c).trans
          (heADC720Sign_one_two (hilbertSymbol K omega c))
  · simpa only [HeADC716Column.evenCoefficients,
      HeADC716Column.coefficients, HeADC716Column.paperSign] using
      (heADC2025Lemma720_secondFirst_represents_iff_hilbertNegOne
        (K := K) k omega c).trans
          (heADC720Sign_two_one (hilbertSymbol K omega c))
  · simpa only [HeADC716Column.evenCoefficients,
      HeADC716Column.coefficients, HeADC716Column.paperSign] using
      (heADC2025Lemma720_secondSecond_represents_iff_hilbertOne
        (K := K) k omega c).trans
          (heADC720Sign_two_two (hilbertSymbol K omega c))

/-- Both even columns in Lemma 7.20(iii) have the signed determinant
class printed in Definition 4.1. -/
theorem heADC2025Lemma720_evenDeterminantClass
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega : Kˣ) (nuPrime : HeADC716Column) :
    IsSquare
      (diagonalUnitDeterminant (nuPrime.evenCoefficients k omega) *
        ((-1 : Kˣ) ^ (k + 2) * omega)) := by
  cases nuPrime
  · simpa only [HeADC716Column.evenCoefficients, Nat.add_assoc] using
      (heADCEvenFirst_determinantClass (K := K) (k + 1) omega)
  · simpa only [HeADC716Column.evenCoefficients, Nat.add_assoc] using
      (heADCEvenSecond_determinantClass (K := K) (k + 1) omega
        (Or.inl (by omega)))

/-- Both odd columns in Lemma 7.20(iii) have the same signed determinant
class. -/
theorem heADC2025Lemma720_oddDeterminantClass
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (c : Kˣ) (nu : HeADC716Column) :
    IsSquare
      (diagonalUnitDeterminant (nu.coefficients (k + 1) c) *
        ((-1 : Kˣ) ^ (k + 2) * c)) := by
  cases nu
  · rw [HeADC716Column.coefficients,
      diagonalUnitDeterminant_heHuOddFirst]
    simp only [Nat.add_assoc]
    exact ⟨_, rfl⟩
  · have hpair :=
      (heADC2025Proposition42iOdd (K := K) (k + 1) c).determinantSquare
    simpa only [HeADC716Column.coefficients,
      diagonalUnitDeterminant_heHuOddFirst, Nat.add_assoc,
      mul_comm] using hpair

/-- The missing determinant line in the selected codimension-one
representation has the square class of `omega * c`. -/
theorem heADC2025Lemma720_complementDeterminantSquare
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) (nuPrime nu : HeADC716Column) :
    IsSquare
      ((diagonalUnitDeterminant (nu.coefficients (k + 1) c) *
          diagonalUnitDeterminant (nuPrime.evenCoefficients k omega)) *
        (omega * c)) := by
  let sign : Kˣ := (-1 : Kˣ) ^ (k + 2)
  have htarget : IsSquare
      (diagonalUnitDeterminant (nu.coefficients (k + 1) c) *
        (sign * c)) := by
    simpa only [sign] using
      (heADC2025Lemma720_oddDeterminantClass (K := K) k c nu)
  have hsource : IsSquare
      (diagonalUnitDeterminant (nuPrime.evenCoefficients k omega) *
        (sign * omega)) := by
    simpa only [sign] using
      (heADC2025Lemma720_evenDeterminantClass
        (K := K) k omega nuPrime)
  have hmiddle : IsSquare
      ((diagonalUnitDeterminant (nu.coefficients (k + 1) c) *
          diagonalUnitDeterminant (nuPrime.evenCoefficients k omega)) *
        ((sign * c) * (sign * omega))) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      htarget.mul hsource
  have hline : IsSquare
      (((sign * c) * (sign * omega)) * (omega * c)) := by
    refine ⟨sign * c * omega, ?_⟩
    ac_rfl
  exact isSquare_mul_trans _ _ _ hmiddle hline

/-- Adding the determinant line `omega * c` to the selected even row
gives the required odd row up to equal-rank diagonal representation. -/
theorem heADC2025Lemma720_productDiagonalRepresents
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) (nuPrime nu : HeADC716Column)
    (hselect :
      nuPrime.paperSign = nu.paperSign * hilbertSymbol K omega c) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.snoc (nuPrime.evenCoefficients k omega) (omega * c)))
      (diagonalUnitCoefficients (nu.coefficients (k + 1) c)) := by
  have hhead := (heADC2025Lemma720_columnRepresentation_iff
    (K := K) k omega c nuPrime nu).2 hselect
  let d := diagonalUnitDeterminant (nu.coefficients (k + 1) c) *
    diagonalUnitDeterminant (nuPrime.evenCoefficients k omega)
  have hcomplete := determinantCompletion_represents_base_general
    (nu.coefficients (k + 1) c)
    (nuPrime.evenCoefficients k omega) hhead
  have hsquare : IsSquare ((omega * c) * d) := by
    simpa only [d, mul_comm] using
      (heADC2025Lemma720_complementDeterminantSquare
        (K := K) k omega c nuPrime nu)
  have hback := hcomplete.symm_of_sameRank
  have hbackLine :=
    (diagonalRepresents_snoc_iff_of_isSquare_mul
      (nu.coefficients (k + 1) c)
      (nuPrime.evenCoefficients k omega) (omega * c) d hsquare).2 hback
  exact hbackLine.symm_of_sameRank

/-- Ambient-space isometry asserted in Lemma 7.20(iii): the selected
named even model, with the line `omega * c`, is the chosen odd space. -/
theorem heADC2025Lemma720_productSpaceIsometric
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (omega c : Kˣ) (nuPrime nu : HeADC716Column)
    (hselect :
      nuPrime.paperSign = nu.paperSign * hilbertSymbol K omega c) :
    ((BONG.coefficientDiagonalSpace
        (nuPrime.evenCoefficients k omega)).orthogonalSum
      ((QuadraticSpace.line K).rescaleUnit (omega * c))).IsIsometric
        (BONG.coefficientDiagonalSpace
          (nu.coefficients (k + 1) c)) := by
  have hdiag := heADC2025Lemma720_productDiagonalRepresents
    (K := K) k omega c nuPrime nu hselect
  have hrepresentation :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.snoc (nuPrime.evenCoefficients k omega) (omega * c))
      (nu.coefficients (k + 1) c)).2 hdiag
  obtain ⟨f⟩ := hrepresentation
  let hline :=
    (QuadraticSpace.Isometry.refl
      (BONG.coefficientDiagonalSpace
        (nuPrime.evenCoefficients k omega))).orthogonalSum
      (QuadraticSpace.rescaleLineScaledLineIsometry (omega * c))
  let happend :=
    QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      (nuPrime.evenCoefficients k omega) (omega * c)
  exact ⟨hline.trans (happend.trans
    (f.toIsometryOfFinrankEq (by simp)))⟩

end Bong
