/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Terminal

/-!
# Beli (2019), Lemma 2.16 at the exceptional terminal index

The combined terminal value has no half-gap candidate of its own.  Under the
revised defect inequality its primary candidate realizes the terminal minimum,
and the same affine cancellation as in the ordinary case applies.
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

/-- The terminal primary candidate written with the second central defect. -/
theorem terminalAdjustedPrimary_eq_centralCurrent
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2) (hgap : n + 2 < m + 1) :
    a.terminalAdjustedPrimary b hgap =
      ((a.order ⟨i.val, i.lt_large⟩ : ℚ) : WithTop ℚ) +
        a.centralCurrentDefect b i := by
  have haTerminal : (⟨n + 2, hgap⟩ : Fin (m + 1)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    exact hterminal.symm
  have hplus : n + 3 = i.val + 1 := by omega
  have hminus : n + 1 = i.val - 1 := by omega
  unfold terminalAdjustedPrimary centralCurrentDefect
  rw [haTerminal, hplus]
  congr 1
  exact congrArg
    (fun j => a.truncatedPrefixDefect b (-1) (i.val + 1) j) hminus

/-- The replacement terminal candidate written with the first central defect. -/
theorem terminalAdjustedSecondaryPrevious_eq_centralPrevious
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2) (hinner : n + 3 < m + 1) :
    a.terminalAdjustedSecondaryPrevious b hinner =
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, by
          omega⟩ - b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.centralPreviousDefect b i := by
  have hgap : n + 2 < m + 1 := by
    rw [← hterminal]
    exact i.lt_large
  have haTerminal : (⟨n + 2, hgap⟩ : Fin (m + 1)) =
      ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    exact hterminal.symm
  have haNext : (⟨n + 3, hinner⟩ : Fin (m + 1)) =
      ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    change n + 3 = i.val + 1
    omega
  have hbTerminal : (⟨n, by omega⟩ : Fin (n + 1)) =
      ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ := by
    apply Fin.ext
    change n = i.val - 2
    omega
  unfold terminalAdjustedSecondaryPrevious centralPreviousDefect
  rw [haTerminal, haNext, hbTerminal]
  congr 1
  exact congrArg₂
    (fun x y => a.truncatedPrefixDefect b (-1) x y)
    hterminal.symm (by omega)

/-- The revised defect sum forces the primary candidate to realize the
exceptional terminal minimum. -/
theorem terminalAdjustedAlpha_eq_primary_of_defectSum
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2)
    (hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, i.lt_large⟩)
    (hsum :
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) - (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i) :
    a.terminalAdjustedAlpha b (by rw [← hterminal]; exact i.lt_large) =
      a.terminalAdjustedPrimary b (by rw [← hterminal]; exact i.lt_large) := by
  let hgap : n + 2 < m + 1 := by
    rw [← hterminal]
    exact i.lt_large
  change a.terminalAdjustedAlpha b hgap = a.terminalAdjustedPrimary b hgap
  by_cases hinner : n + 3 < m + 1
  · have hbTerminal : (⟨n, by omega⟩ : Fin (n + 1)) =
        ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ := by
      apply Fin.ext
      change n = i.val - 2
      omega
    have haTerminal : (⟨n + 2, hgap⟩ : Fin (m + 1)) =
        ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      exact hterminal.symm
    have hcrossTerminal : b.order ⟨n, by omega⟩ <
        a.order ⟨n + 2, hgap⟩ := by
      rw [hbTerminal, haTerminal]
      exact hcross
    rw [a.terminalAdjustedAlpha_eq_min_primary_previous
      b hgap hinner hcrossTerminal.le]
    apply min_eq_left
    have hiNext : i.val + 1 < m + 1 := by
      omega
    let p : Fin m := ⟨i.val, by omega⟩
    let c : ℚ := ((a.order ⟨i.val + 1, hiNext⟩ -
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Int) : ℚ)
    let d : ℚ := 2 * (ramificationIndex K : ℚ) +
      (b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : ℚ) - (a.order ⟨i.val, i.lt_large⟩ : ℚ)
    have hpSucc : p.succ = ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      rfl
    have hpCast : p.castSucc = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      rfl
    have hcore : a.centralCurrentDefect b i <
        (c : WithTop ℚ) + a.centralPreviousDefect b i := by
      apply withTop_lt_shift_add_of_affine_sum (d := d)
        (p := a.halfGapValue p)
      · simpa only [p] using a.centralCurrentDefect_le_halfGap b i hiNext
      · rw [halfGapValue, orderGap, hpSucc, hpCast]
        dsimp only [c, d]
        push_cast
        ring_nf
        exact le_rfl
      · simpa only [d, add_comm] using hsum
    rw [a.terminalAdjustedPrimary_eq_centralCurrent b i hterminal hgap,
      a.terminalAdjustedSecondaryPrevious_eq_centralPrevious
        b i hterminal hinner]
    let x : WithTop ℚ := ((a.order ⟨i.val, i.lt_large⟩ : ℚ) : WithTop ℚ)
    let y : WithTop ℚ :=
      (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Int) : ℚ) : WithTop ℚ)
    have hshift : x + (c : WithTop ℚ) = y := by
      dsimp only [x, c, y]
      norm_cast
      ring
    have hadd := WithTop.add_lt_add_left (x := x) (by simp [x]) hcore
    rw [← add_assoc, hshift] at hadd
    exact hadd.le
  · exact a.terminalAdjustedAlpha_eq_primary_of_not_inner b hgap hinner

/-- Affine cancellation for the two primary candidates at the terminal
central index. -/
theorem centralTerminalPrimaryTrigger_iff_defectTrigger
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2) :
    ((2 * (ramificationIndex K : ℚ) +
        (a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        a.representationPrimaryDefect b i.previous +
          a.terminalAdjustedPrimary b (by
            rw [← hterminal]
            exact i.lt_large) ↔
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) - (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ) :
            WithTop ℚ) <
        a.centralPreviousDefect b i + a.centralCurrentDefect b i := by
  let hgap : n + 2 < m + 1 := by
    rw [← hterminal]
    exact i.lt_large
  change ((2 * (ramificationIndex K : ℚ) +
      (a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
      a.representationPrimaryDefect b i.previous +
        a.terminalAdjustedPrimary b hgap ↔ _
  rw [a.representationPrimaryDefect_previous_eq b i,
    a.terminalAdjustedPrimary_eq_centralCurrent b i hterminal hgap]
  simpa only [Int.cast_sub, Int.cast_zero, WithTop.coe_zero, sub_zero,
    zero_add, add_assoc] using
    withTop_centralShift_lt_iff
      (ramificationIndex K : ℚ)
      (a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩)
      0
      (b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩)
      (a.order ⟨i.val, i.lt_large⟩)
      (a.centralPreviousDefect b i) (a.centralCurrentDefect b i)

/-- Lemma 2.16 at the unique exceptional terminal central index. -/
theorem centralAlphaTrigger_iff_defectTrigger_of_terminal
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hterminal : i.val = n + 2) :
    a.centralAlphaTrigger b i ↔ a.centralDefectTrigger b i := by
  have hnotOrdinary : ¬i.val ≤ n + 1 := by omega
  let hgap : n + 2 < m + 1 := by
    rw [← hterminal]
    exact i.lt_large
  constructor
  · intro h
    unfold centralAlphaTrigger at h
    rcases h with ⟨hcross, hsum⟩
    unfold centralAdjustedAlpha at hsum
    rw [dif_neg hnotOrdinary,
      a.coe_representationAlphaValue b i.previous] at hsum
    have hprimarySum :
        ((2 * (ramificationIndex K : ℚ) +
          (a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
          a.representationPrimaryDefect b i.previous +
            a.terminalAdjustedPrimary b hgap :=
      hsum.trans_le (add_le_add
        ((a.representationAlpha_le_prime b i.previous).trans
          (a.representationAlphaPrime_le_primaryDefect b i.previous))
        (a.terminalAdjustedAlpha_le_primary b hgap))
    unfold centralDefectTrigger
    refine ⟨hcross, ?_⟩
    exact (a.centralTerminalPrimaryTrigger_iff_defectTrigger
      b i hterminal).mp hprimarySum
  · intro h
    unfold centralDefectTrigger at h
    rcases h with ⟨hcross, hsum⟩
    by_cases hprevious : a.representationAlpha b i.previous =
        a.representationAlphaPrime b i.previous
    · have hterminalPrimary :=
        a.terminalAdjustedAlpha_eq_primary_of_defectSum
          (sourceLaws := sourceLaws) b i hterminal hcross hsum
      have hpreviousPrimary := by
        letI : Beli2006AlphaLaws.{u, w} K := targetLaws
        exact a.representationAlphaPrime_previous_eq_primary b i hcross hsum
      have hprimary :=
        (a.centralTerminalPrimaryTrigger_iff_defectTrigger
          b i hterminal).mpr hsum
      unfold centralAlphaTrigger
      refine ⟨hcross, ?_⟩
      unfold centralAdjustedAlpha
      rw [dif_neg hnotOrdinary,
        a.coe_representationAlphaValue b i.previous, hprevious,
        hpreviousPrimary, hterminalPrimary]
      exact hprimary
    · letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.centralAlphaTrigger_of_previous_alpha_ne_prime_terminal
        b hdefect i hterminal hprevious

end BONG.GoodBONG

end Bong
