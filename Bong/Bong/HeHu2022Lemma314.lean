/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma313

/-!
# He--Hu (2024), Lemma 3.14

This file proves the two explicit representation comparisons between the
first-column spaces in Table 1.  The only arithmetic input is that the
distinguished discriminant class has every unit in its norm group.  The
nonrepresentation assertion in part (i) is then the codimension-one case of
Lemma 3.13.
-/

namespace Bong

open Dyadic BONG.GoodBONG
open AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A unit is represented by both binary spaces `H=[1,-1]` and
`[1,-Delta]`. -/
theorem heHuBinaryFirst_oneOrDiscriminant_represents_unit
    (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    DiagonalRepresents
      (fun _ : Fin 1 => (epsilon : K))
      (diagonalUnitCoefficients (heHuBinaryFirst mu)) := by
  apply (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
    (K := K) (1 : Kˣ) (-mu) epsilon).2
  rcases hmu with rfl | rfl
  · simp
  · have heven : Even (ordUnit K epsilon) := by
      rw [(isValuationUnit_iff_ordUnit_eq_zero K epsilon).mp hepsilon]
      simp
    have hdelta :=
      (hilbertSymbol_discriminant_eq_one_iff_even_order epsilon).2 heven
    simpa only [inv_one, mul_one, one_mul, neg_neg,
      hilbertSymbol_comm K epsilon] using hdelta

/-- The binary space `[1,-mu]`, for `mu=1` or `Delta`, is represented by
`H perp [epsilon]`.  For the discriminant branch this is the explicit
argument `-Delta -> [-1,epsilon]` in the paper. -/
theorem heHuBinaryFirst_represents_oddFirstTail
    (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuBinaryFirst mu))
      (diagonalUnitCoefficients (heHuOddFirstTail epsilon)) := by
  rcases hmu with rfl | rfl
  · exact diagonalRepresents_append_right_prefix
      (heHuBinaryFirst (K := K) 1) (fun _ : Fin 1 => epsilon)
  · let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have heven : Even (ordUnit K epsilon) := by
      rw [(isValuationUnit_iff_ordUnit_eq_zero K epsilon).mp hepsilon]
      simp
    have hhilbert : hilbertSymbol K delta epsilon = 1 :=
      (hilbertSymbol_discriminant_eq_one_iff_even_order epsilon).2 heven
    have hline : DiagonalRepresents
        (fun _ : Fin 1 => (-delta : K))
        (Fin.cons (-1 : K) (fun _ : Fin 1 => (epsilon : K))) := by
      apply (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
        (K := K) (-1 : Kˣ) epsilon (-delta)).2
      simpa only [inv_neg, inv_one, neg_mul, mul_neg, neg_neg,
        mul_one, one_mul] using hhilbert
    have hone : DiagonalRepresents
        (fun _ : Fin 1 => (1 : K))
        (fun _ : Fin 1 => (1 : K)) :=
      diagonalRepresents_refl _
    have happend := DiagonalRepresents.appendBoth hone hline
    convert happend using 1 <;> funext i <;> fin_cases i <;> rfl

/-- `H perp [epsilon]` is represented by
`H perp [1,-mu]` for `mu=1` or `Delta`. -/
theorem heHuOddFirstTail_represents_evenFirstTail
    (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirstTail epsilon))
      (diagonalUnitCoefficients (heHuEvenFirstTail mu)) := by
  have hline := heHuBinaryFirst_oneOrDiscriminant_represents_unit
    mu epsilon hmu hepsilon
  have hhyperbolic : DiagonalRepresents
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) :=
    diagonalRepresents_refl _
  have happend := DiagonalRepresents.appendBoth hhyperbolic hline
  convert happend using 1 <;> funext i <;> fin_cases i <;> rfl

/-- Lemma 3.14(i), the positive representation assertion, including the
binary exceptional case in which `W_2^2(1)` is undefined. -/
theorem heHu2022Lemma314iRepresents (pairs : Nat)
    (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenFirst pairs mu))
      (diagonalUnitCoefficients (heHuOddFirst pairs epsilon)) := by
  cases pairs with
  | zero =>
      have htail := heHuBinaryFirst_represents_oddFirstTail
        mu epsilon hmu hepsilon
      convert htail using 1 <;> funext i <;> fin_cases i <;>
        rfl
  | succ pairs =>
      have htail := heHuBinaryFirst_represents_oddFirstTail
        mu epsilon hmu hepsilon
      have hhyperbolic : DiagonalRepresents
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) :=
        diagonalRepresents_refl _
      have htailLarge := DiagonalRepresents.appendBoth hhyperbolic htail
      have hfull := DiagonalRepresents.appendBoth
        (diagonalRepresents_refl
          (diagonalUnitCoefficients
            (standardHyperbolicEndpointTower (K := K) pairs)))
        htailLarge
      have hfullUnits : DiagonalRepresents
          (diagonalUnitCoefficients
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (Fin.append (heHuHyperbolicPair (K := K))
                (heHuBinaryFirst mu))))
          (diagonalUnitCoefficients
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (Fin.append (heHuHyperbolicPair (K := K))
                (heHuOddFirstTail epsilon)))) := by
        simpa only [diagonalUnitCoefficients_append] using hfull
      have hcast := diagonalRepresents_heHuFinFamilyCast_both
        (K := K)
        (by omega : 2 * pairs + 4 = 2 * (pairs + 1) + 2)
        (by omega : 2 * pairs + 5 = 2 * (pairs + 1) + 3)
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append (heHuHyperbolicPair (K := K))
            (heHuBinaryFirst mu)))
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (Fin.append (heHuHyperbolicPair (K := K))
            (heHuOddFirstTail epsilon)))
        hfullUnits
      have htargetEq :
          heHuFinFamilyCast (by omega :
              2 * pairs + 5 = 2 * (pairs + 1) + 3)
            (Fin.append
              (standardHyperbolicEndpointTower (K := K) pairs)
              (Fin.append (heHuHyperbolicPair (K := K))
                (heHuOddFirstTail epsilon))) =
            heHuOddFirst (pairs + 1) epsilon := by
        simpa only [heHuOddFirst] using
          heHuFinFamilyCast_tower_hyperbolic_tail
            (K := K) pairs (heHuOddFirstTail epsilon)
      rw [htargetEq] at hcast
      simpa only [heHuEvenFirst, heHuEvenFirstTail] using hcast

/-- Lemma 3.14(i), including the nonrepresentation of the defined second
space. -/
theorem heHu2022Lemma314i (pairs : Nat) (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K))
    (hdefined : HeHuEvenSecondDefined pairs mu) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuEvenFirst pairs mu))
        (diagonalUnitCoefficients (heHuOddFirst pairs epsilon)) ∧
      ¬ DiagonalRepresents
        (diagonalUnitCoefficients
          (heHuEvenSecond pairs mu hdefined))
        (diagonalUnitCoefficients (heHuOddFirst pairs epsilon)) := by
  have hfirst := heHu2022Lemma314iRepresents
    pairs mu epsilon hmu hepsilon
  have hexact := heHu2022Lemma313CodimensionOne
    (heHuEvenFirst pairs mu)
    (heHuEvenSecond pairs mu hdefined)
    (heHu2022Definition34Proposition35Even pairs mu hdefined)
    (heHuOddFirst pairs epsilon)
  refine ⟨hfirst, ?_⟩
  rcases hexact with hleft | hright
  · exact hleft.2
  · exact (hright.1 hfirst).elim

/-- Lemma 3.14(ii): in odd source dimension, `W_1^(n+1)(mu)` represents
`W_1^n(epsilon)` for `mu=1` or `Delta`. -/
theorem heHu2022Lemma314ii (pairs : Nat) (mu epsilon : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst pairs epsilon))
      (diagonalUnitCoefficients (heHuEvenFirst (pairs + 1) mu)) := by
  have htail := heHuOddFirstTail_represents_evenFirstTail
    mu epsilon hmu hepsilon
  have hfull := DiagonalRepresents.appendBoth
    (diagonalRepresents_refl
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) pairs)))
    htail
  have hfullUnits : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuOddFirstTail epsilon)))
      (diagonalUnitCoefficients
        (Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (heHuEvenFirstTail mu))) := by
    simpa only [diagonalUnitCoefficients_append] using hfull
  have hcast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K)
    (rfl : 2 * pairs + 3 = 2 * pairs + 3)
    (by omega : 2 * pairs + 4 = 2 * (pairs + 1) + 2)
    (Fin.append
      (standardHyperbolicEndpointTower (K := K) pairs)
      (heHuOddFirstTail epsilon))
    (Fin.append
      (standardHyperbolicEndpointTower (K := K) pairs)
      (heHuEvenFirstTail mu))
    hfullUnits
  simpa only [heHuOddFirst, heHuEvenFirst,
    heHuFinFamilyCast_self] using hcast

end Bong
