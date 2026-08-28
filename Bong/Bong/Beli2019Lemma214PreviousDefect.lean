/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Current

/-!
# Beli (2019), Lemma 2.14: a preceding mismatch

This is the source-side counterpart of the current-mismatch defect argument.
The source alpha cap and Remark 1.1 transfer the strict lower bound from the
preceding central defect to the current central defect.
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

/-- The previous primary candidate converts `H_(i-1) < A'_(i-1)` into
the complementary strict defect bound. -/
theorem centralPreviousDefect_gt_halfGapComplement
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hhalf : a.representationHalfGap b i.previous <
      a.representationAlphaPrime b i.previous) :
    ((ramificationIndex K : ℚ) -
          ((a.order ⟨i.val - 1, by
              have := i.one_lt
              have := i.lt_large
              omega⟩ -
            b.order ⟨i.val - 2, by
              have := i.one_lt
              have := i.le_small_succ
              omega⟩ : Int) : ℚ) / 2 : ℚ) <
      a.centralPreviousDefect b i := by
  let g : ℚ := ((a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ -
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : Int) : ℚ)
  let H : ℚ := g / 2 + (ramificationIndex K : ℚ)
  have hHalfEq : a.representationHalfGap b i.previous =
      (H : WithTop ℚ) := by
    simp only [representationHalfGap, CentralRepresentationIndex.previous,
      Nat.sub_sub, one_add_one_eq_two, H, g]
  have hprimary : (H : WithTop ℚ) <
      (g : WithTop ℚ) + a.centralPreviousDefect b i := by
    have h := hhalf.trans_le
      (a.representationAlphaPrime_le_primaryDefect b i.previous)
    rw [hHalfEq, a.representationPrimaryDefect_previous_eq b i] at h
    simpa only [g] using h
  have hsub := withTop_sub_lt_of_lt_add H g
    (a.centralPreviousDefect b i) hprimary
  convert hsub using 1
  norm_cast
  dsimp only [H, g]
  push_cast
  simp only [Rat.divInt_eq_div]
  push_cast
  ring

/-- If `A_(i-1) ≠ A'_(i-1)`, condition 2.1(ii) and domination force the
current central defect above the source-shifted complementary half-gap. -/
theorem centralCurrentDefect_gt_previousMismatchCut
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hne : a.representationAlpha b i.previous ≠
      a.representationAlphaPrime b i.previous) :
    ((((a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.lt_large
          omega⟩ - a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) +
        (ramificationIndex K : ℚ) -
        ((a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ -
          b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Int) : ℚ) / 2 : ℚ) : WithTop ℚ) <
      a.centralCurrentDefect b i := by
  obtain ⟨hAlpha, hhalf⟩ :=
    a.representationAlpha_eq_halfGap_and_lt_prime_of_ne b i.previous hne
  let g : ℚ := ((a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ -
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ : Int) : ℚ)
  let cut : ℚ := (ramificationIndex K : ℚ) - g / 2
  let sourceShift : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    a.order ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : Int) : ℚ)
  let sourceCut : ℚ := cut - sourceShift
  have hprevious : (cut : WithTop ℚ) < a.centralPreviousDefect b i := by
    have h := a.centralPreviousDefect_gt_halfGapComplement b i hhalf
    simpa only [cut, g] using h
  let p : Fin m := ⟨i.val - 1, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  have hpreviousCap : a.centralPreviousDefect b i ≤
      (a.alphaValue p : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      i.val (i.val - 2)
    rw [a.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large] at hcap
    have hindex : (⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin m) = p := by
      apply Fin.ext
      rfl
    rw [hindex] at hcap
    simpa only [centralPreviousDefect] using hcap
  have halpha : (cut : WithTop ℚ) < (a.alphaValue p : WithTop ℚ) :=
    hprevious.trans_le hpreviousCap
  have hremark := a.alpha_le_orderGap_add_cappedAdjacent p
  have hshifted : (cut : WithTop ℚ) <
      (sourceShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (i.val - 1) (i.val + 1) := by
    have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      have := i.one_lt
      omega
    have hpCast : p.castSucc = ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ := by
      apply Fin.ext
      rfl
    have htwo : i.val - 1 + 2 = i.val + 1 := by
      have := i.one_lt
      omega
    rw [hpSucc, hpCast] at hremark
    exact halpha.trans_le (by
      simpa only [sourceShift, p, Fin.val_mk, htwo] using hremark)
  have hsourceForward : (sourceCut : WithTop ℚ) <
      a.truncatedPrefixDefect a (-1) (i.val - 1) (i.val + 1) := by
    have h := withTop_sub_lt_of_lt_add cut sourceShift
      (a.truncatedPrefixDefect a (-1) (i.val - 1) (i.val + 1)) hshifted
    simpa only [sourceCut] using h
  have hsource : (sourceCut : WithTop ℚ) <
      a.truncatedPrefixDefect a (-1) (i.val + 1) (i.val - 1) := by
    rw [← a.truncatedPrefixDefect_comm a (-1) (i.val - 1) (i.val + 1)]
    exact hsourceForward
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
  have hhalfAbove : (sourceCut : WithTop ℚ) <
      a.representationHalfGap b i.previous := by
    unfold representationHalfGap
    simp only [CentralRepresentationIndex.previous, Nat.sub_sub,
      one_add_one_eq_two]
    norm_cast
    dsimp only [sourceCut, sourceShift, cut, g]
    push_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hcrossQ :
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) < (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  have hdiagonal : (sourceCut : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 (i.val - 1) (i.val - 1) := by
    have hd := hdefect i.previous
    rw [a.coe_representationAlphaValue b i.previous, hAlpha] at hd
    exact hhalfAbove.trans_le hd
  have hdomination := a.truncatedPrefixDefect_domination a b (-1) 1
    (i.val + 1) (i.val - 1) (i.val - 1)
  simp only [mul_one] at hdomination
  have hresult := (lt_min hsource hdiagonal).trans_le hdomination
  unfold centralCurrentDefect
  convert hresult using 1
  norm_cast
  dsimp only [sourceCut, sourceShift, cut, g]
  push_cast
  simp only [Rat.divInt_eq_div]
  push_cast
  ring

end BONG.GoodBONG

end Bong
