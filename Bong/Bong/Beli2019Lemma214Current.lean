/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214CurrentDefect

/-!
# Beli (2019), Lemma 2.14: the current-index implication

This is the half of Lemma 2.14 needed when `A_i ≠ A'_i`.  Every candidate
of `A_(i-1)` is checked against the central threshold; the lower endpoint has
only two candidates and is treated separately.
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

/-- Lemma 2.14 at the central index `i`, obtained from `A_i ≠ A'_i`. -/
theorem centralAlphaTrigger_of_current_alpha_ne_prime
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hne :
      a.representationAlpha b (i.current hi) ≠
        a.representationAlphaPrime b (i.current hi)) :
    a.centralAlphaTrigger b i := by
  obtain ⟨hCurrentAlpha, hhalf⟩ :=
    a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      b (i.current hi) hne
  have hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, i.lt_large⟩ :=
    a.sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
      b (i.current hi) i.one_lt hhalf
  have horderCurrent := a.centralPreviousOrder_le_targetCurrent
    b hRank horder i hi hcross.le
  have hpreviousDefect :=
    a.centralPreviousDefect_gt_currentMismatchCut b hdefect i hi hne
  have hcurrentDefect :=
    a.centralCurrentDefect_gt_halfGapComplement b i hi hhalf
  let T : ℚ := 2 * (ramificationIndex K : ℚ) +
    (a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : ℚ)
  let S : ℚ := (b.order ⟨i.val - 1, by
    have := i.one_lt
    have := hi
    omega⟩ : ℚ)
  let Hcurrent : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ - b.order ⟨i.val - 1, by
      have := i.one_lt
      have := hi
      omega⟩ : Int) : ℚ) / 2 + (ramificationIndex K : ℚ)
  let Hprevious : ℚ :=
    ((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ) / 2 + (ramificationIndex K : ℚ)
  let previousShift : ℚ :=
    ((a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ - b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ)
  have hCurrentHalfGap : a.representationHalfGap b (i.current hi) =
      (Hcurrent : WithTop ℚ) := by
    simp only [representationHalfGap, CentralRepresentationIndex.current,
      Hcurrent]
  have hPreviousHalfGap : a.representationHalfGap b i.previous =
      (Hprevious : WithTop ℚ) := by
    simp only [representationHalfGap, CentralRepresentationIndex.previous,
      Nat.sub_sub, one_add_one_eq_two, Hprevious]
  have hHalf : (T : WithTop ℚ) <
      (Hprevious : WithTop ℚ) +
        ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
    norm_cast
    dsimp only [T, S, Hprevious, Hcurrent]
    push_cast
    have hcrossQ :
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    have horderQ :
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) ≤
          (b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : ℚ) := by
      exact_mod_cast horderCurrent
    linarith
  let primaryTotal : ℚ := previousShift + S + Hcurrent
  have hPrimaryInput : ((T - primaryTotal : ℚ) : WithTop ℚ) <
      a.centralPreviousDefect b i := by
    convert hpreviousDefect using 1
    norm_cast
    dsimp only [T, primaryTotal, previousShift, S, Hcurrent]
    push_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    ring
  have hPrimaryCanonical : (T : WithTop ℚ) <
      (primaryTotal : WithTop ℚ) + a.centralPreviousDefect b i :=
    withTop_lt_add_of_sub_lt T primaryTotal
      (a.centralPreviousDefect b i) hPrimaryInput
  have hPrimary : (T : WithTop ℚ) <
      a.representationPrimaryDefect b i.previous +
        ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
    rw [a.representationPrimaryDefect_previous_eq b i]
    have htotal : (primaryTotal : WithTop ℚ) =
        (previousShift : WithTop ℚ) +
          ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
      norm_cast
      dsimp only [primaryTotal]
      ring
    rw [htotal] at hPrimaryCanonical
    calc
      (T : WithTop ℚ) <
          (previousShift : WithTop ℚ) +
            ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) +
              a.centralPreviousDefect b i := hPrimaryCanonical
      _ = ((previousShift : WithTop ℚ) +
            a.centralPreviousDefect b i) +
          ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
        ac_rfl
  unfold centralAlphaTrigger
  refine ⟨hcross, ?_⟩
  unfold centralAdjustedAlpha
  rw [dif_pos hi]
  rw [a.coe_representationAlphaValue b i.previous,
    a.coe_representationAlphaValue b (i.current hi), hCurrentAlpha,
    hCurrentHalfGap]
  rw [a.representationAlpha_eq_min_halfGap_prime b i.previous,
    hPreviousHalfGap]
  by_cases hinterior : 2 < i.val
  · have hprev : 1 < i.previous.val ∧ i.previous.val + 1 < m + 1 := by
      constructor
      · change 1 < i.val - 1
        omega
      · change i.val - 1 + 1 < m + 1
        have := i.lt_large
        omega
    have hcrossPrev :
        b.order ⟨i.previous.val - 1, by
          have := i.previous.le_small
          omega⟩ ≤
          a.order ⟨i.previous.val + 1, hprev.2⟩ := by
      have hbIndex : (⟨i.previous.val - 1, by
          have := i.previous.le_small
          omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ := by
        apply Fin.ext
        change (i.val - 1) - 1 = i.val - 2
        omega
      have haIndex : (⟨i.previous.val + 1, hprev.2⟩ : Fin (m + 1)) =
          ⟨i.val, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
      rw [hbIndex, haIndex]
      exact hcross.le
    rw [a.representationAlphaPrime_eq_min_primary_current
      b i.previous hprev hcrossPrev]
    let currentCut : ℚ := (ramificationIndex K : ℚ) -
      ((a.order ⟨i.val, i.lt_large⟩ - b.order ⟨i.val - 1, by
        have := i.one_lt
        have := hi
        omega⟩ : Int) : ℚ) / 2
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ + a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 3, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ)
    let secondaryTotal : ℚ := secondaryShift + S + Hcurrent
    have htargetTwoStep : b.order ⟨i.val - 3, by
        have := i.le_small_succ
        omega⟩ ≤ b.order ⟨i.val - 1, by
        have := hi
        omega⟩ := by
      have hstart : i.val - 3 < n + 1 := by
        have := i.le_small_succ
        omega
      have hstep :
          (⟨i.val - 3, hstart⟩ : Fin (n + 1)).val + 2 < n + 1 := by
        change i.val - 3 + 2 < n + 1
        omega
      have hgood := b.good ⟨i.val - 3, hstart⟩ hstep
      have hend :
          (⟨(⟨i.val - 3, hstart⟩ : Fin (n + 1)).val + 2, hstep⟩ :
              Fin (n + 1)) =
            ⟨i.val - 1, by have := hi; omega⟩ := by
        apply Fin.ext
        change i.val - 3 + 2 = i.val - 1
        omega
      rw [hend] at hgood
      exact hgood
    have hSecondaryCut : ((T - secondaryTotal : ℚ) : WithTop ℚ) <
        (currentCut : WithTop ℚ) := by
      norm_cast
      dsimp only [T, secondaryTotal, secondaryShift, S, Hcurrent, currentCut]
      push_cast
      have hcrossQ :
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) <
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
        exact_mod_cast hcross
      have htwoStepQ :
          (b.order ⟨i.val - 3, by
            have := i.le_small_succ
            omega⟩ : ℚ) ≤
            (b.order ⟨i.val - 1, by
              have := hi
              omega⟩ : ℚ) := by
        exact_mod_cast htargetTwoStep
      linarith
    have hCurrentCut : (currentCut : WithTop ℚ) <
        a.centralCurrentDefect b i := by
      simpa only [currentCut] using hcurrentDefect
    have hSecondaryInput := hSecondaryCut.trans hCurrentCut
    have hSecondaryCanonical : (T : WithTop ℚ) <
        (secondaryTotal : WithTop ℚ) + a.centralCurrentDefect b i :=
      withTop_lt_add_of_sub_lt T secondaryTotal
        (a.centralCurrentDefect b i) hSecondaryInput
    have hSecondaryEq :
        a.representationSecondaryCurrentDefect b i.previous hprev =
          (secondaryShift : WithTop ℚ) + a.centralCurrentDefect b i := by
      unfold representationSecondaryCurrentDefect centralCurrentDefect
      simp only [CentralRepresentationIndex.previous,
        Nat.sub_add_cancel i.one_lt.le, Nat.sub_sub, one_add_one_eq_two,
        show i.val - 1 + 2 = i.val + 1 by omega, secondaryShift]
    have hSecondary : (T : WithTop ℚ) <
        a.representationSecondaryCurrentDefect b i.previous hprev +
          ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
      rw [hSecondaryEq]
      have htotal : (secondaryTotal : WithTop ℚ) =
          (secondaryShift : WithTop ℚ) +
            ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
        norm_cast
        dsimp only [secondaryTotal]
        ring
      rw [htotal] at hSecondaryCanonical
      calc
        (T : WithTop ℚ) <
            (secondaryShift : WithTop ℚ) +
              ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) +
                a.centralCurrentDefect b i := hSecondaryCanonical
        _ = ((secondaryShift : WithTop ℚ) +
              a.centralCurrentDefect b i) +
            ((S : WithTop ℚ) + (Hcurrent : WithTop ℚ)) := by
          ac_rfl
    by_cases hfirst :
        (Hprevious : WithTop ℚ) ≤
        min (a.representationPrimaryDefect b i.previous)
          (a.representationSecondaryCurrentDefect b i.previous hprev)
    · rw [min_eq_left hfirst]
      simpa only [T, S] using hHalf
    · rw [min_eq_right (le_of_not_ge hfirst)]
      by_cases hsecond :
          a.representationPrimaryDefect b i.previous ≤
          a.representationSecondaryCurrentDefect b i.previous hprev
      · rw [min_eq_left hsecond]
        simpa only [T, S] using hPrimary
      · rw [min_eq_right (le_of_not_ge hsecond)]
        simpa only [T, S] using hSecondary
  · have hendpoint := a.representationAlphaPrime_eq_primary_of_not_interior
        b i.previous (by
          simp only [CentralRepresentationIndex.previous]
          omega)
    rw [hendpoint]
    by_cases hfirst : (Hprevious : WithTop ℚ) ≤
        a.representationPrimaryDefect b i.previous
    · rw [min_eq_left hfirst]
      simpa only [T, S] using hHalf
    · rw [min_eq_right (le_of_not_ge hfirst)]
      simpa only [T, S] using hPrimary

end BONG.GoodBONG

end Bong
