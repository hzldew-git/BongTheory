/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma713
import Bong.Bong.HeHu2022Lemma57

/-!
# He (2025), Lemma 7.11

The published symbol `d(a_1...a_4)=infinity` means that the four-entry
prefix determinant is a square.  The unit and unit-times-uniformizer rows
of `N_2^3(c)` are both formalized.  The latter row also supplies the exact
represented-target contradiction used in the necessity proof of Lemma 7.5.
All condition-(iii') obstructions occur at paper index `4`.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- In the unit-parameter row, the first defect in the central trigger is
at least `2e-1`.  Lemma 7.6(ii) supplies the first two mixed entries, while
Proposition 2.7(iv) supplies the final source pair. -/
theorem heADC2025Lemma711Even_previousDefect_ge
    (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (delta kappa : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hkappa : IsValuationUnit K (kappa : K))
    (hkappaDefect : defectOrder (K := K) kappa =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    letI : GoodBONGClassificationLaws.{u, u, u} K :=
      goodBONGClassificationLawsProved K
    let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
      hkappaDefect
    ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
      a.centralPreviousDefect b
        (heHuLemma57CentralIndex (m := 3) (by omega)) := by
  dsimp only
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
    hkappaDefect
  let sourceLast : Fin 5 := ⟨3, by omega⟩
  let sourceGap : Fin 4 := ⟨2, by omega⟩
  have hsourcePair := a.heHu2022Proposition27iiiiv hAIntegral sourceLast
    (by exact ⟨1, by simp [sourceLast]⟩)
    (by simpa only [sourceLast] using hR4)
  have hsourceForward : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (-1) 2 4 := by
    have h :=
      (hsourcePair.pairOrdersAndDefects sourceLast le_rfl
        (by exact ⟨1, by simp [sourceLast]⟩)).2.2.1
    simpa only [heHuAdjacentCappedDefect, sourceLast, sourceGap] using h
  have hsourceReverse : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.truncatedPrefixDefect a (-1) 4 2 := by
    rw [a.truncatedPrefixDefect_comm a (-1) 4 2]
    exact hsourceForward
  have hbMaximal :=
    heHu2022Proposition37OddSecondUnit delta kappa hdelta hkappa
      hkappaDefect 0
  have hbPenultimate : b.order ⟨1, by omega⟩ =
      2 - 2 * (ramificationIndex K : Int) := by
    simp [b]
  have htarget : a.truncatedPrefixDefect b 1 2 2 =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) :=
    (a.heADC2025Lemma76ii 0 b hI1 hbMaximal).2 hbPenultimate
  have hthreshold :
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    apply WithTop.coe_le_coe.mpr
    linarith
  have hdomination :=
    a.truncatedPrefixDefect_domination a b (-1) 1 4 2 2
  have hcombined :
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
        a.truncatedPrefixDefect b (-1) 4 2 := by
    simpa only [mul_one] using
      (le_min (hthreshold.trans hsourceReverse) htarget.ge).trans
        hdomination
  simpa only [centralPreviousDefect, heHuLemma57CentralIndex, b] using
    hcombined

/-- The unit-parameter test activates condition `(iii')` at paper index
`4`. -/
theorem heADC2025Lemma711Even_defectTrigger
    (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (delta kappa : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hkappa : IsValuationUnit K (kappa : K))
    (hkappaDefect : defectOrder (K := K) kappa =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    letI : GoodBONGClassificationLaws.{u, u, u} K :=
      goodBONGClassificationLawsProved K
    let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
      hkappaDefect
    a.centralDefectTrigger b
      (heHuLemma57CentralIndex (m := 3) (by omega)) := by
  dsimp only
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
    hkappaDefect
  let i := heHuLemma57CentralIndex (m := 3) (by omega)
  let sourceFive : Fin 5 := ⟨4, by omega⟩
  unfold centralDefectTrigger
  constructor
  · change b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩
    have htargetIndex : (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin 3) = 2 := by
      apply Fin.ext
      simp [i, heHuLemma57CentralIndex]
    have hsourceIndex : (⟨i.val, i.lt_large⟩ : Fin 5) =
        sourceFive := by
      apply Fin.ext
      simp [i, sourceFive, heHuLemma57CentralIndex]
    rw [htargetIndex, hsourceIndex]
    have htarget : b.order (2 : Fin 3) = 0 := by
      simp [b]
    rw [htarget]
    have hR5' : 1 < a.order sourceFive := by
      simpa only [sourceFive] using hR5
    omega
  · have hprevious :
        ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
          a.centralPreviousDefect b i := by
      simpa only [b, i] using
        a.heADC2025Lemma711Even_previousDefect_ge hAIntegral hI1 hR4
          delta kappa hdelta hkappa hkappaDefect
    have hcurrent : (0 : WithTop ℚ) ≤ a.centralCurrentDefect b i := by
      unfold centralCurrentDefect
      exact a.truncatedPrefixDefect_nonneg
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws) b (-1)
          (i.val + 1) (i.val - 1)
    have hsum :
        ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) ≤
          a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
      exact hprevious.trans
        (by simpa only [add_zero] using
          add_le_add_right hcurrent (a.centralPreviousDefect b i))
    change
      ((2 * (ramificationIndex K : ℚ) +
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) -
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) : WithTop ℚ) <
          a.centralPreviousDefect b i + a.centralCurrentDefect b i
    have htargetIndex : (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin 3) = 2 := by
      apply Fin.ext
      simp [i, heHuLemma57CentralIndex]
    have hsourceIndex : (⟨i.val, i.lt_large⟩ : Fin 5) =
        sourceFive := by
      apply Fin.ext
      simp [i, sourceFive, heHuLemma57CentralIndex]
    rw [htargetIndex, hsourceIndex]
    have htarget : b.order (2 : Fin 3) = 0 := by
      simp [b]
    rw [htarget]
    have hR5' : 1 < a.order sourceFive := by
      simpa only [sourceFive] using hR5
    have hthreshold :
        ((2 * (ramificationIndex K : ℚ) + (0 : ℚ) -
          (a.order sourceFive : ℚ) : ℚ) : WithTop ℚ) <
            ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
      apply WithTop.coe_lt_coe.mpr
      have hR5Q : (1 : ℚ) < (a.order sourceFive : ℚ) := by
        exact_mod_cast hR5'
      linarith
    exact hthreshold.trans_le hsum

/-- The unit-parameter `N_2^3(delta)` test is not represented by the first
four source coefficients when their product is a square. -/
theorem heADC2025Lemma711Even_not_represents
    (a : GoodBONG q L 5)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta kappa : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hkappa : IsValuationUnit K (kappa : K))
    (hkappaDefect : defectOrder (K := K) kappa =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    letI : GoodBONGClassificationLaws.{u, u, u} K :=
      goodBONGClassificationLawsProved K
    let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
      hkappaDefect
    ¬ DiagonalRepresents (b.prefixValues 3 le_rfl)
      (a.prefixValues 4 (by omega)) := by
  dsimp only
  letI : GoodBONGClassificationLaws.{u, u, u} K :=
    goodBONGClassificationLawsProved K
  let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
    hkappaDefect
  let c := delta
  have hfirst : a.order 0 = 0 := by
    exact hI1.oddOrder (0 : Fin 3) odd_one
  have hdet : IsSquare (a.prefixProduct 4) := by
    apply isSquare_of_two_mul_e_lt_defectOrder (K := K)
    rw [hprefix]
    exact (show
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) < ⊤ from
        WithTop.coe_lt_top (((2 * ramificationIndex K : Nat) : ℚ)))
  have hsplit : DiagonalRepresents
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2))
      (a.prefixValues 4 (by omega)) :=
    heHuLemma57_split_represents_sourcePrefix beliUniversalAlphaLaws a
      (by omega) hfirst hR4 hdet
  have hfirstRep : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) 0 c))
      (a.prefixValues 4 (by omega)) :=
    (heHuLemma57_oddFirst_represents_split (K := K) c).trans hsplit
  let source : Fin 4 → Kˣ := a.prefixValueUnits 4 (by omega)
  have hfirstRepUnits : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddFirst (K := K) 0 c))
      (diagonalUnitCoefficients source) := by
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using
      hfirstRep
  have hexact := heHu2022Lemma313CodimensionOne
    (heHuOddFirst (K := K) 0 c) (heHuOddSecond (K := K) 0 c)
    (heHu2022Definition34Proposition35Odd (K := K) 0 c) source
  have hnotSecond : ¬ DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond (K := K) 0 c))
      (diagonalUnitCoefficients source) := by
    rcases hexact with hleft | hright
    · exact hleft.2
    · exact (hright.1 hfirstRepUnits).elim
  intro hrep
  have hbFull : b.prefixValueUnits 3 le_rfl = b.valueUnit := by
    funext j
    rfl
  have hrepUnits : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients (b.prefixValueUnits 3 le_rfl))
      (diagonalUnitCoefficients source) at hrep
    rwa [hbFull] at hrep
  have hdeltaEven : Even (ordUnit K delta) := by
    rw [(isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdelta]
    exact Even.zero
  have hcandidate : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuOddSecond (K := K) 0 c)) := by
    rw [heHuOddSecond_of_even 0 c (by simpa only [c] using hdeltaEven)]
    have hraw :=
      heHuLemma311OddSecondUnitTail_represents_oddSecondTailEven
        delta kappa hdelta hkappa hkappaDefect
    convert hraw using 1
    · funext j
      fin_cases j <;> rfl
  have hsecondB : DiagonalRepresents
      (diagonalUnitCoefficients (heHuOddSecond (K := K) 0 c))
      (diagonalUnitCoefficients b.valueUnit) :=
    hcandidate.symm_of_sameRank
  exact hnotSecond (hsecondB.trans hrepUnits)

/-- The unit row of He, Lemma 7.11: the trigger holds and its required
prefix representation fails. -/
theorem heADC2025Lemma711Even
    (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta kappa : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hkappa : IsValuationUnit K (kappa : K))
    (hkappaDefect : defectOrder (K := K) kappa =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    letI : GoodBONGClassificationLaws.{u, u, u} K :=
      goodBONGClassificationLawsProved K
    let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
      hkappaDefect
    a.centralDefectTrigger b
        (heHuLemma57CentralIndex (m := 3) (by omega)) ∧
      ¬ DiagonalRepresents (b.prefixValues 3 le_rfl)
        (a.prefixValues 4 (by omega)) := by
  dsimp only
  exact ⟨a.heADC2025Lemma711Even_defectTrigger hAIntegral hI1 hR4 hR5
      delta kappa hdelta hkappa hkappaDefect,
    a.heADC2025Lemma711Even_not_represents hI1 hR4 hprefix
      delta kappa hdelta hkappa hkappaDefect⟩

/-- Direct logical form of the unit-row failure in Lemma 7.11. -/
theorem heADC2025Lemma711Even_not_centralRepresentationConditionsPrime
    (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta kappa : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hkappa : IsValuationUnit K (kappa : K))
    (hkappaDefect : defectOrder (K := K) kappa =
      ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)) :
    letI : GoodBONGClassificationLaws.{u, u, u} K :=
      goodBONGClassificationLawsProved K
    let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
      hkappaDefect
    ¬ a.CentralRepresentationConditionsPrime b := by
  dsimp only
  intro hprime
  have h := a.heADC2025Lemma711Even hAIntegral hI1 hR4 hR5 hprefix
    delta kappa hdelta hkappa hkappaDefect
  exact h.2 (hprime (heHuLemma57CentralIndex (m := 3) (by omega)) h.1)

/-- The odd-valuation half of He, Lemma 7.11.  This is the branch used in
the rank-three necessity argument below. -/
theorem heADC2025Lemma711Odd (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤)
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)) :
    ¬ a.CentralRepresentationConditionsPrime
      (heHuLemma311OddSecondUnitUniformizerTail delta hdelta) := by
  exact a.heHu2022Lemma57_not_centralRepresentationConditionsPrime
    (m := 3) (by omega) hAIntegral hI1 hR4 hR5 hprefix delta hdelta

/-- He, Lemma 7.11 in the two normalized parameter rows.  Every nonzero
square class is represented by a valuation unit `delta` or by
`delta * pi`; the first conjunct is the unit row and the second is the
unit-times-uniformizer row. -/
theorem heADC2025Lemma711
    (a : GoodBONG q L 5)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤) :
    (∀ (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)),
      ∃ (kappa : Kˣ) (hkappa : IsValuationUnit K (kappa : K))
        (hkappaDefect : defectOrder (K := K) kappa =
          ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ)),
        letI : GoodBONGClassificationLaws.{u, u, u} K :=
          goodBONGClassificationLawsProved K
        let b := heHuLemma311OddSecondUnitTail delta kappa hdelta hkappa
          hkappaDefect
        a.centralDefectTrigger b
            (heHuLemma57CentralIndex (m := 3) (by omega)) ∧
          ¬ DiagonalRepresents (b.prefixValues 3 le_rfl)
            (a.prefixValues 4 (by omega))) ∧
      ∀ (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)),
        a.centralDefectTrigger
            (heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
            (heHuLemma57CentralIndex (m := 3) (by omega)) ∧
          ¬ DiagonalRepresents
            ((heHuLemma311OddSecondUnitUniformizerTail delta hdelta)
              |>.prefixValues 3 le_rfl)
            (a.prefixValues 4 (by omega)) := by
  constructor
  · intro delta hdelta
    obtain ⟨kappa, hkappa, hkappaDefect⟩ :=
      exists_unit_defectOrder_eq_twoE_sub_one (K := K)
    refine ⟨kappa, hkappa, hkappaDefect, ?_⟩
    exact a.heADC2025Lemma711Even hAIntegral hI1 hR4 hR5 hprefix
      delta kappa hdelta hkappa hkappaDefect
  · intro delta hdelta
    exact a.heHu2022Lemma57 (m := 3) (by omega) hAIntegral hI1 hR4
      hR5 hprefix delta hdelta

/-- A rank-five source space represents at least one of two odd-valuation
second-column tests whose unit parameters differ by `Delta`. -/
theorem heADC2025Lemma711_exists_represented_oddTarget
    (a : GoodBONG q L 5) :
    ∃ (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K)),
      DiagonalRepresents
        (diagonalUnitCoefficients
          (heHuLemma311OddSecondUnitUniformizerTail delta hdelta).valueUnit)
        (diagonalUnitCoefficients a.valueUnit) := by
  let laws := heHuDiscriminantClassLaws (K := K)
  let Delta : Kˣ := laws.discriminantUnit
  let c : Kˣ := uniformizerPowerUnit K 1
  let targetOne := heADCW2Odd (K := K) 0 c
  let targetDelta := heADCW2Odd (K := K) 0 (c * Delta)
  have hDelta : ¬ IsSquare Delta := by
    exact AlternatingEndpointNormalization.discriminantUnit_not_isSquare
      (K := K) (laws := laws)
  have htwist : ¬ DiagonalRepresents
      (diagonalUnitCoefficients targetDelta)
      (diagonalUnitCoefficients targetOne) := by
    apply heADC2025Lemma713_twisted_not_represents 0 c Delta hDelta
      targetOne targetDelta
    · exact (heADC2025Proposition42iOdd (K := K) 0 c).determinantSquare
    · exact (heADC2025Proposition42iOdd
        (K := K) 0 (c * Delta)).determinantSquare
  have select {excluded : Fin 3 → Kˣ} {large : Fin 5 → Kˣ}
      (hexact : HeHuMissesExactly excluded large) :
      DiagonalRepresents (diagonalUnitCoefficients targetOne)
          (diagonalUnitCoefficients large) ∨
        DiagonalRepresents (diagonalUnitCoefficients targetDelta)
          (diagonalUnitCoefficients large) := by
    by_cases hone : DiagonalRepresents
        (diagonalUnitCoefficients targetOne)
        (diagonalUnitCoefficients excluded)
    · right
      apply hexact.represents_other targetDelta
      intro hdelta
      exact htwist (hdelta.trans hone.symm_of_sameRank)
    · left
      exact hexact.represents_other targetOne hone
  have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (1 : Kˣ)).2
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [one_mul] at h
    omega
  have hDeltaUnit : IsValuationUnit K (Delta : K) := by
    exact laws.discriminant_isValuationUnit
  have hliteralOne : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitUniformizerTail 1 honeUnit).valueUnit)
      (diagonalUnitCoefficients targetOne) := by
    simpa only [targetOne, c, heADCW2Odd, heHuLemma57Parameter, one_mul] using
      heHuLemma57Target_represents_oddSecond (K := K) 1 honeUnit
  have hliteralDelta : DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma311OddSecondUnitUniformizerTail Delta hDeltaUnit).valueUnit)
      (diagonalUnitCoefficients targetDelta) := by
    simpa only [targetDelta, c, heADCW2Odd, heHuLemma57Parameter,
      mul_comm] using
        heHuLemma57Target_represents_oddSecond (K := K) Delta hDeltaUnit
  rcases a.heADC2025Lemma713_sourceDiagonal (k := 0) with hsource | hsource
  · rcases select
        (heADC2025Proposition42iiiOddSecond
          (K := K) 0 (heHuLemma59C a 0)).exactness with hone | hdelta
    · exact ⟨1, honeUnit, hliteralOne.trans (hone.trans hsource)⟩
    · exact ⟨Delta, hDeltaUnit,
        hliteralDelta.trans (hdelta.trans hsource)⟩
  · rcases select
        (heADC2025Proposition42iiiOddFirst
          (K := K) 0 (heHuLemma59C a 0)).exactness with hone | hdelta
    · exact ⟨1, honeUnit, hliteralOne.trans (hone.trans hsource)⟩
    · exact ⟨Delta, hDeltaUnit,
        hliteralDelta.trans (hdelta.trans hsource)⟩

/-- Under `3`-ADC, the exceptional rank-three branch in the necessity proof
of Lemma 7.5 cannot occur. -/
theorem heADC2025Lemma711_badBranch_impossible
    (a : GoodBONG q L 5)
    (hADC : Lattice.IsNADC.{u, u, u} q L 3)
    (hI1 : a.HeHuI1E 2 (by omega))
    (hR4 : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hR5 : 1 < a.order ⟨4, by omega⟩)
    (hprefix : defectOrder (K := K) (a.prefixProduct 4) = ⊤) : False := by
  rcases a.heADC2025Lemma711_exists_represented_oddTarget with
    ⟨delta, hdelta, hdiag⟩
  let r :=
    (BONG.binaryDiagonalModelSpace
      (heHuDiscriminantEndpointValues (K := K) 0 0)
      (heHuDiscriminantEndpointValues (K := K) 0 1)
      (heHuDiscriminantEndpoint_admissible (K := K) 0)).orthogonalSum
        (QuadraticSpace.rescaleUnit
          (heHuLemma311OddSecondUnitUniformizerValue delta)
          (QuadraticSpace.line K))
  let M := Lattice.product
    (BONG.binaryDiagonalModelLattice (K := K))
    (BONG.unaryModelLattice (K := K))
  let b : GoodBONG r M 3 :=
    heHuLemma311OddSecondUnitUniformizerTail delta hdelta
  have hM : Lattice.IsIntegral r M :=
    heHuIntegral_of_firstOrder_nonneg b (by
      rw [show b.order 0 = 0 by simp [b]])
  have hrep : Lattice.Represents q r L M := by
    apply hADC.represents r M b.toBONG.length_eq_finrank.symm hM
    have hSource : q.Represents
        (BONG.coefficientDiagonalSpace a.valueUnit) :=
      ⟨a.toBONG.exactDiagonalizationIsometry.symm.toRepresentation⟩
    have hdiag' : DiagonalRepresents
        (diagonalUnitCoefficients b.valueUnit)
        (diagonalUnitCoefficients a.valueUnit) := by
      convert hdiag using 1
    have hDiagonal :
        (BONG.coefficientDiagonalSpace a.valueUnit).Represents
          (BONG.coefficientDiagonalSpace b.valueUnit) :=
      (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        b.valueUnit a.valueUnit).2 hdiag'
    exact (hSource.trans hDiagonal).trans
      ⟨b.toBONG.exactDiagonalizationIsometry.toRepresentation⟩
  have hcentral :=
    ((heADC2025Theorem36Published (by omega) hrep.ambient a b).mp hrep)
      |>.centralRepresentations
  exact (a.heADC2025Lemma711Odd hADC.isIntegral hI1 hR4 hR5 hprefix
    delta hdelta) hcentral

end BONG.GoodBONG

end Bong
