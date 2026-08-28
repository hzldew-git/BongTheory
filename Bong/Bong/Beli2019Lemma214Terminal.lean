/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019TerminalNormalForm

/-!
# Beli (2019), Lemma 2.14 at the exceptional terminal index

When the current ordinary invariant no longer exists, Definition 4 supplies
the combined terminal value.  A mismatch at the preceding invariant still
forces condition (iii): both possible terminal candidates exceed the central
threshold after adding the preceding half-gap.
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
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Lemma 2.14 for the exceptional central index `n + 2`. -/
theorem centralAlphaTrigger_of_previous_alpha_ne_prime_terminal
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2)
    (hne : a.representationAlpha b i.previous ≠
      a.representationAlphaPrime b i.previous) :
    a.centralAlphaTrigger b i := by
  obtain ⟨hPreviousAlpha, hhalf⟩ :=
    a.representationAlpha_eq_halfGap_and_lt_prime_of_ne b i.previous hne
  have hnotOrdinary : ¬i.val ≤ n + 1 := by omega
  have hgap : n + 2 < m + 1 := by
    rw [← hterminal]
    exact i.lt_large
  have hprevRight : i.previous.val + 1 < m + 1 := by
    change i.val - 1 + 1 < m + 1
    have := i.one_lt
    have := i.lt_large
    omega
  have hcrossRaw :=
    a.sourceNext_gt_targetCurrent_of_halfGap_lt_alphaPrime
      b i.previous hprevRight hhalf
  have hbIndex : (⟨i.previous.val - 1, by
      have := i.previous.le_small
      omega⟩ : Fin (n + 1)) = ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  have haIndex : (⟨i.previous.val + 1, hprevRight⟩ : Fin (m + 1)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    have := i.one_lt
    omega
  rw [hbIndex, haIndex] at hcrossRaw
  have hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, i.lt_large⟩ := hcrossRaw
  have hpreviousDefect :=
    a.centralPreviousDefect_gt_halfGapComplement b i hhalf
  have hcurrentDefect :=
    a.centralCurrentDefect_gt_previousMismatchCut b hdefect i hne
  let T : ℚ := 2 * (ramificationIndex K : ℚ) +
    (a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : ℚ)
  let Hprevious : ℚ :=
    ((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ) / 2 + (ramificationIndex K : ℚ)
  have hPreviousHalfGap : a.representationHalfGap b i.previous =
      (Hprevious : WithTop ℚ) := by
    simp only [representationHalfGap, CentralRepresentationIndex.previous,
      Nat.sub_sub, one_add_one_eq_two, Hprevious]
  let currentShift : ℚ := (a.order ⟨i.val, i.lt_large⟩ : ℚ)
  let primaryTotal : ℚ := Hprevious + currentShift
  have hPrimaryInput : ((T - primaryTotal : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect b i := by
    convert hcurrentDefect using 1
    norm_cast
    dsimp only [T, primaryTotal, Hprevious, currentShift]
    push_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    ring
  have hPrimaryCanonical : (T : WithTop ℚ) <
      (primaryTotal : WithTop ℚ) + a.centralCurrentDefect b i :=
    withTop_lt_add_of_sub_lt T primaryTotal
      (a.centralCurrentDefect b i) hPrimaryInput
  have haTerminal : (⟨n + 2, hgap⟩ : Fin (m + 1)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    exact hterminal.symm
  have hplus : n + 3 = i.val + 1 := by omega
  have hminus : n + 1 = i.val - 1 := by omega
  have hPrimaryEq : a.terminalAdjustedPrimary b hgap =
      (currentShift : WithTop ℚ) + a.centralCurrentDefect b i := by
    unfold terminalAdjustedPrimary centralCurrentDefect
    rw [haTerminal, hplus]
    dsimp only [currentShift]
    congr 1
    exact congrArg
      (fun j => a.truncatedPrefixDefect b (-1) (i.val + 1) j) hminus
  have hPrimary : (T : WithTop ℚ) <
      (Hprevious : WithTop ℚ) + a.terminalAdjustedPrimary b hgap := by
    rw [hPrimaryEq]
    have htotal : (primaryTotal : WithTop ℚ) =
        (Hprevious : WithTop ℚ) + (currentShift : WithTop ℚ) := by
      norm_cast
    rw [htotal] at hPrimaryCanonical
    simpa only [add_assoc] using hPrimaryCanonical
  unfold centralAlphaTrigger
  refine ⟨hcross, ?_⟩
  unfold centralAdjustedAlpha
  rw [dif_neg hnotOrdinary]
  rw [a.coe_representationAlphaValue b i.previous, hPreviousAlpha,
    hPreviousHalfGap]
  by_cases hinner : n + 3 < m + 1
  · have hbTerminal : (⟨n, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ := by
      apply Fin.ext
      change n = i.val - 2
      omega
    have hcrossTerminal : b.order ⟨n, by omega⟩ <
        a.order ⟨n + 2, hgap⟩ := by
      rw [hbTerminal, haTerminal]
      exact hcross
    rw [a.terminalAdjustedAlpha_eq_min_primary_previous
      b hgap hinner hcrossTerminal.le]
    let previousCut : ℚ := (ramificationIndex K : ℚ) -
      ((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ) / 2
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, by
          rw [← hplus]
          exact hinner⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ)
    let secondaryTotal : ℚ := Hprevious + secondaryShift
    have hiNext : i.val + 1 < m + 1 := by
      rw [← hplus]
      exact hinner
    have hsourceTwoStep : a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ ≤ a.order ⟨i.val + 1, hiNext⟩ := by
      have hstart : i.val - 1 < m + 1 := by
        have := i.lt_large
        omega
      have hstep :
          (⟨i.val - 1, hstart⟩ : Fin (m + 1)).val + 2 < m + 1 := by
        change i.val - 1 + 2 < m + 1
        have := i.one_lt
        have := hiNext
        omega
      have hgood := a.good ⟨i.val - 1, hstart⟩ hstep
      have hend :
          (⟨(⟨i.val - 1, hstart⟩ : Fin (m + 1)).val + 2, hstep⟩ :
              Fin (m + 1)) = ⟨i.val + 1, hiNext⟩ := by
        apply Fin.ext
        change i.val - 1 + 2 = i.val + 1
        have := i.one_lt
        omega
      rw [hend] at hgood
      exact hgood
    have hSecondaryCut : ((T - secondaryTotal : ℚ) : WithTop ℚ) <
        (previousCut : WithTop ℚ) := by
      norm_cast
      dsimp only [T, secondaryTotal, secondaryShift, Hprevious, previousCut]
      push_cast
      have hcrossQ :
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) < (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
        exact_mod_cast hcross
      have htwoStepQ :
          (a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : ℚ) ≤ (a.order ⟨i.val + 1, hiNext⟩ : ℚ) := by
        exact_mod_cast hsourceTwoStep
      linarith
    have hPreviousCut : (previousCut : WithTop ℚ) <
        a.centralPreviousDefect b i := by
      simpa only [previousCut] using hpreviousDefect
    have hSecondaryInput := hSecondaryCut.trans hPreviousCut
    have hSecondaryCanonical : (T : WithTop ℚ) <
        (secondaryTotal : WithTop ℚ) + a.centralPreviousDefect b i :=
      withTop_lt_add_of_sub_lt T secondaryTotal
        (a.centralPreviousDefect b i) hSecondaryInput
    have haNext : (⟨n + 3, hinner⟩ : Fin (m + 1)) =
        ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      exact hplus
    have hSecondaryEq : a.terminalAdjustedSecondaryPrevious b hinner =
        (secondaryShift : WithTop ℚ) + a.centralPreviousDefect b i := by
      unfold terminalAdjustedSecondaryPrevious centralPreviousDefect
      rw [haTerminal, haNext, hbTerminal]
      dsimp only [secondaryShift]
      congr 1
      exact congrArg₂
        (fun x y => a.truncatedPrefixDefect b (-1) x y)
        hterminal.symm (by omega)
    have hSecondary : (T : WithTop ℚ) <
        (Hprevious : WithTop ℚ) +
          a.terminalAdjustedSecondaryPrevious b hinner := by
      rw [hSecondaryEq]
      have htotal : (secondaryTotal : WithTop ℚ) =
          (Hprevious : WithTop ℚ) + (secondaryShift : WithTop ℚ) := by
        norm_cast
      rw [htotal] at hSecondaryCanonical
      simpa only [add_assoc] using hSecondaryCanonical
    by_cases hfirst : a.terminalAdjustedPrimary b hgap ≤
        a.terminalAdjustedSecondaryPrevious b hinner
    · rw [min_eq_left hfirst]
      simpa only [T] using hPrimary
    · rw [min_eq_right (le_of_not_ge hfirst)]
      simpa only [T] using hSecondary
  · rw [a.terminalAdjustedAlpha_eq_primary_of_not_inner b hgap hinner]
    simpa only [T] using hPrimary

end BONG.GoodBONG

end Bong
