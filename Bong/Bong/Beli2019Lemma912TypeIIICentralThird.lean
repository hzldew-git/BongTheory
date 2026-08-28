/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIICentralLow

/-!
# Beli (2019), Lemma 9.12: condition (iii) at index three

If the source invariant `C_2` is cut down from `C'_2`, Lemma 2.14 already
activates the source central condition.  Otherwise `C_2 = C'_2`, and the
bounds `B'_2 <= C'_2 + 1` and `B_3 <= C_3` convert the target trigger into
the source trigger.  The resulting source prefix representation is then
transported across the common type-III tail.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- Condition 2.1(iii) at the exceptional type-III central index three. -/
theorem beli2019Lemma912_typeIII_thirdCentralRepresentation
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T)) (c : GoodBONG r M (T + 3))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) (hT : 0 < T)
    (hsourceOrder : (a.castLength hlength).RepresentationOrderCondition
      c le_rfl)
    (hsourceDefect : (a.castLength hlength).RepresentationDefectCondition c)
    (hsourceCentral :
      (a.castLength hlength).CentralRepresentationConditions c)
    (htargetTrigger :
      (I.bong.castLength hlength).centralAlphaTrigger c
        (beli2019Lemma912TypeIIIThirdCentralIndex (T := T) hT)) :
    DiagonalRepresents
      (c.prefixValues 2 (by omega))
      ((I.bong.castLength hlength).prefixValues 3 (by omega)) := by
  let source := a.castLength hlength
  let target := I.bong.castLength hlength
  let second : RepresentationIndex (T + 3) (T + 3) := {
    val := 2
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  let third : RepresentationIndex (T + 3) (T + 3) := {
    val := 3
    pos := by omega
    lt_large := by omega
    le_small := by omega }
  let central := beli2019Lemma912TypeIIIThirdCentralIndex (T := T) hT
  have hprefix :=
    beli2019Lemma912_typeIII_sourcePrefix_represents_targetPrefix
      a D I hlength 3 (by omega) (by omega)
  by_cases hprime : source.representationAlpha c central.previous =
      source.representationAlphaPrime c central.previous
  · have hprime' : source.representationAlphaPrime c second =
        source.representationAlpha c second := by
      simpa only [central, beli2019Lemma912TypeIIIThirdCentralIndex,
        CentralRepresentationIndex.previous, second, Nat.reduceSub] using
          hprime.symm
    have htargetAlphaLePrime :
        (target.representationAlphaValue c second : WithTop ℚ) ≤
          target.representationAlphaPrime c second := by
      rw [target.coe_representationAlphaValue]
      exact target.representationAlpha_le_prime c second
    have hprimeBound : target.representationAlphaPrime c second ≤
        source.representationAlphaPrime c second + 1 := by
      simpa only [target, source, second, secondRepresentationIndex] using
        beli2019Lemma912_typeIII_secondAlphaPrime_le_source_add_one
          (sourceAlpha := sourceAlpha) a c D I hlength hT
    have hBTwoTop :
        (target.representationAlphaValue c second : WithTop ℚ) ≤
          (source.representationAlphaValue c second : WithTop ℚ) + 1 := by
      calc
        (target.representationAlphaValue c second : WithTop ℚ) ≤
            target.representationAlphaPrime c second := htargetAlphaLePrime
        _ ≤ source.representationAlphaPrime c second + 1 := hprimeBound
        _ = source.representationAlpha c second + 1 := by rw [hprime']
        _ = (source.representationAlphaValue c second : WithTop ℚ) + 1 := by
          rw [source.coe_representationAlphaValue]
    have hBTwo : target.representationAlphaValue c second ≤
        source.representationAlphaValue c second + 1 := by
      exact_mod_cast hBTwoTop
    have hBThree : target.representationAlphaValue c third ≤
        source.representationAlphaValue c third := by
      exact beli2019Lemma912_typeIII_representationAlphaValue_le_source
        (alpha := sourceAlpha) a c D I hlength third (by
          simp only [third]
          omega)
    have htwo : target.order (⟨2, by omega⟩ : Fin (T + 3)) =
        source.order (⟨2, by omega⟩ : Fin (T + 3)) + 1 := by
      convert beli2019Lemma912TypeIIIIndexPData_order_castLength_two
        a D I hlength using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp [Nat.mod_eq_of_lt (by omega)]
    have hthree : target.order (⟨3, by omega⟩ : Fin (T + 3)) =
        source.order (⟨3, by omega⟩ : Fin (T + 3)) :=
      beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
        a D I hlength ⟨3, by omega⟩ (by simp)
    have htargetCross := htargetTrigger.1
    simp only [beli2019Lemma912TypeIIIThirdCentralIndex,
      Nat.reduceSub] at htargetCross
    rw [hthree] at htargetCross
    have htargetSum := htargetTrigger.2
    unfold centralAdjustedAlpha at htargetSum
    rw [dif_pos (show central.val ≤ T + 3 by
      simp only [central, beli2019Lemma912TypeIIIThirdCentralIndex]
      omega)] at htargetSum
    simp only [beli2019Lemma912TypeIIIThirdCentralIndex,
      CentralRepresentationIndex.previous,
      CentralRepresentationIndex.current,
      Nat.reduceSub] at htargetSum
    norm_cast at htargetSum
    push_cast at htargetSum
    rw [htwo] at htargetSum
    simp only [Int.cast_add, Int.cast_one] at htargetSum
    dsimp only [target, source, second, third] at hBTwo hBThree
    have hsourceSum :
        2 * (ramificationIndex K : ℚ) +
            (source.order (⟨2, by omega⟩ : Fin (T + 3)) : ℚ) <
          source.representationAlphaValue c second +
            (c.order (⟨2, by omega⟩ : Fin (T + 3)) : ℚ) +
              source.representationAlphaValue c third := by
      linarith
    have hsourceTrigger : source.centralAlphaTrigger c central := by
      unfold centralAlphaTrigger
      refine ⟨?_, ?_⟩
      · simpa only [central, beli2019Lemma912TypeIIIThirdCentralIndex,
          source, Nat.reduceSub] using htargetCross
      · unfold centralAdjustedAlpha
        rw [dif_pos (show central.val ≤ T + 3 by
          simp only [central, beli2019Lemma912TypeIIIThirdCentralIndex]
          omega)]
        simp only [central, beli2019Lemma912TypeIIIThirdCentralIndex,
          CentralRepresentationIndex.previous,
          CentralRepresentationIndex.current,
          Nat.reduceSub]
        norm_cast
        push_cast
        simpa only [source, second, third, add_assoc] using hsourceSum
    have hsourceRepresentation := hsourceCentral central hsourceTrigger
    exact hsourceRepresentation.trans hprefix
  · have hsourceTrigger :=
      source.centralAlphaTrigger_of_previous_alpha_ne_prime
        c le_rfl hsourceOrder hsourceDefect central (by
          simp only [central, beli2019Lemma912TypeIIIThirdCentralIndex]
          omega) hprime
    have hsourceRepresentation := hsourceCentral central hsourceTrigger
    exact hsourceRepresentation.trans hprefix

end BONG.GoodBONG

end Bong
