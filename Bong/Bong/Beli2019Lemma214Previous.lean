/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214PreviousDefect

/-!
# Beli (2019), Lemma 2.14: the previous-index implication

This is the half of Lemma 2.14 needed when `A_(i-1) ≠ A'_(i-1)`.
For an interior current index, all three candidates of `A_i` are checked.
At the upper endpoint, only its two existing candidates remain.
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

/-- Lemma 2.14 at the central index `i`, obtained from
`A_(i-1) ≠ A'_(i-1)`. -/
theorem centralAlphaTrigger_of_previous_alpha_ne_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hne : a.representationAlpha b i.previous ≠
      a.representationAlphaPrime b i.previous) :
    a.centralAlphaTrigger b i := by
  obtain ⟨hPreviousAlpha, hhalf⟩ :=
    a.representationAlpha_eq_halfGap_and_lt_prime_of_ne b i.previous hne
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
  have horderCurrent := a.centralPreviousOrder_le_targetCurrent
    b hRank horder i hi hcross.le
  have hpreviousDefect :=
    a.centralPreviousDefect_gt_halfGapComplement b i hhalf
  have hcurrentDefect :=
    a.centralCurrentDefect_gt_previousMismatchCut b hdefect i hne
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
          omega⟩ : ℚ) < (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    have horderQ :
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) ≤ (b.order ⟨i.val - 1, by
          have := i.one_lt
          have := hi
          omega⟩ : ℚ) := by
      exact_mod_cast horderCurrent
    linarith
  let currentShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    b.order ⟨i.val - 1, by
      have := i.one_lt
      have := hi
      omega⟩ : Int) : ℚ)
  let primaryTotal : ℚ := Hprevious + S + currentShift
  have hPrimaryInput : ((T - primaryTotal : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect b i := by
    convert hcurrentDefect using 1
    norm_cast
    dsimp only [T, primaryTotal, Hprevious, S, currentShift]
    push_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    ring
  have hPrimaryCanonical : (T : WithTop ℚ) <
      (primaryTotal : WithTop ℚ) + a.centralCurrentDefect b i :=
    withTop_lt_add_of_sub_lt T primaryTotal
      (a.centralCurrentDefect b i) hPrimaryInput
  have hPrimary : (T : WithTop ℚ) <
      (Hprevious : WithTop ℚ) +
        ((S : WithTop ℚ) +
          a.representationPrimaryDefect b (i.current hi)) := by
    rw [a.representationPrimaryDefect_current_eq b i hi]
    have htotal : (primaryTotal : WithTop ℚ) =
        (Hprevious : WithTop ℚ) +
          ((S : WithTop ℚ) + (currentShift : WithTop ℚ)) := by
      norm_cast
      dsimp only [primaryTotal]
      ring
    rw [htotal] at hPrimaryCanonical
    calc
      (T : WithTop ℚ) <
          (Hprevious : WithTop ℚ) +
            ((S : WithTop ℚ) + (currentShift : WithTop ℚ)) +
              a.centralCurrentDefect b i := hPrimaryCanonical
      _ = (Hprevious : WithTop ℚ) +
          ((S : WithTop ℚ) +
            ((currentShift : WithTop ℚ) +
              a.centralCurrentDefect b i)) := by
        ac_rfl
  unfold centralAlphaTrigger
  refine ⟨hcross, ?_⟩
  unfold centralAdjustedAlpha
  rw [dif_pos hi]
  rw [a.coe_representationAlphaValue b i.previous,
    a.coe_representationAlphaValue b (i.current hi), hPreviousAlpha,
    hPreviousHalfGap]
  rw [a.representationAlpha_eq_min_halfGap_prime b (i.current hi),
    hCurrentHalfGap]
  by_cases hinterior : i.val + 1 < m + 1
  · have hcur : 1 < (i.current hi).val ∧
        (i.current hi).val + 1 < m + 1 := by
      constructor
      · change 1 < i.val
        exact i.one_lt
      · change i.val + 1 < m + 1
        exact hinterior
    rw [a.representationAlphaPrime_eq_min_primary_previous
      b (i.current hi) hcur hcross.le]
    let previousCut : ℚ := (ramificationIndex K : ℚ) -
      ((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ) / 2
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hinterior⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ - b.order ⟨i.val - 1, by
          have := i.one_lt
          have := hi
          omega⟩ : Int) : ℚ)
    let secondaryTotal : ℚ := Hprevious + S + secondaryShift
    have hsourceTwoStep : a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ ≤ a.order ⟨i.val + 1, hinterior⟩ := by
      have hstart : i.val - 1 < m + 1 := by
        have := i.lt_large
        omega
      have hstep :
          (⟨i.val - 1, hstart⟩ : Fin (m + 1)).val + 2 < m + 1 := by
        change i.val - 1 + 2 < m + 1
        have := i.one_lt
        have := hinterior
        omega
      have hgood := a.good ⟨i.val - 1, hstart⟩ hstep
      have hend :
          (⟨(⟨i.val - 1, hstart⟩ : Fin (m + 1)).val + 2, hstep⟩ :
              Fin (m + 1)) = ⟨i.val + 1, hinterior⟩ := by
        apply Fin.ext
        change i.val - 1 + 2 = i.val + 1
        have := i.one_lt
        omega
      rw [hend] at hgood
      exact hgood
    have hSecondaryCut : ((T - secondaryTotal : ℚ) : WithTop ℚ) <
        (previousCut : WithTop ℚ) := by
      norm_cast
      dsimp only [T, secondaryTotal, secondaryShift, Hprevious, S,
        previousCut]
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
            omega⟩ : ℚ) ≤ (a.order ⟨i.val + 1, hinterior⟩ : ℚ) := by
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
    have hSecondaryEq :
        a.representationSecondaryPreviousDefect b (i.current hi) hcur =
          (secondaryShift : WithTop ℚ) + a.centralPreviousDefect b i := by
      unfold representationSecondaryPreviousDefect centralPreviousDefect
      simp only [CentralRepresentationIndex.current, secondaryShift]
    have hSecondary : (T : WithTop ℚ) <
        (Hprevious : WithTop ℚ) +
          ((S : WithTop ℚ) +
            a.representationSecondaryPreviousDefect b (i.current hi) hcur) := by
      rw [hSecondaryEq]
      have htotal : (secondaryTotal : WithTop ℚ) =
          (Hprevious : WithTop ℚ) +
            ((S : WithTop ℚ) + (secondaryShift : WithTop ℚ)) := by
        norm_cast
        dsimp only [secondaryTotal]
        ring
      rw [htotal] at hSecondaryCanonical
      calc
        (T : WithTop ℚ) <
            (Hprevious : WithTop ℚ) +
              ((S : WithTop ℚ) + (secondaryShift : WithTop ℚ)) +
                a.centralPreviousDefect b i := hSecondaryCanonical
        _ = (Hprevious : WithTop ℚ) +
            ((S : WithTop ℚ) +
              ((secondaryShift : WithTop ℚ) +
                a.centralPreviousDefect b i)) := by
          ac_rfl
    by_cases hfirst : (Hcurrent : WithTop ℚ) ≤
        min (a.representationPrimaryDefect b (i.current hi))
          (a.representationSecondaryPreviousDefect b (i.current hi) hcur)
    · rw [min_eq_left hfirst]
      simpa only [T, S] using hHalf
    · rw [min_eq_right (le_of_not_ge hfirst)]
      by_cases hsecond : a.representationPrimaryDefect b (i.current hi) ≤
          a.representationSecondaryPreviousDefect b (i.current hi) hcur
      · rw [min_eq_left hsecond]
        simpa only [T, S] using hPrimary
      · rw [min_eq_right (le_of_not_ge hsecond)]
        simpa only [T, S] using hSecondary
  · have hendpoint := a.representationAlphaPrime_eq_primary_of_not_interior
        b (i.current hi) (by
          simp only [CentralRepresentationIndex.current]
          omega)
    rw [hendpoint]
    by_cases hfirst : (Hcurrent : WithTop ℚ) ≤
        a.representationPrimaryDefect b (i.current hi)
    · rw [min_eq_left hfirst]
      simpa only [T, S] using hHalf
    · rw [min_eq_right (le_of_not_ge hfirst)]
      simpa only [T, S] using hPrimary

end BONG.GoodBONG

end Bong
