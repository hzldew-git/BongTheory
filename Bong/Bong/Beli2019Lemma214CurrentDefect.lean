/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Lemma 2.14: a current mismatch

If `A_i` is cut down from `A'_i` by its half-gap candidate, the primary
defect gives one strict lower bound.  Condition 2.1(ii), Remark 1.1, and
defect domination then transfer this lower bound to the preceding defect.
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

/-- The primary candidate converts `H_i < A'_i` into the strict defect
bound used in Lemma 2.14. -/
theorem centralCurrentDefect_gt_halfGapComplement
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hhalf : a.representationHalfGap b (i.current hi) <
      a.representationAlphaPrime b (i.current hi)) :
    ((ramificationIndex K : ℚ) -
          ((a.order ⟨i.val, i.lt_large⟩ -
            b.order ⟨i.val - 1, by
              have := i.one_lt
              have := hi
              omega⟩ : Int) : ℚ) / 2 : ℚ) <
      a.centralCurrentDefect b i := by
  let g : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    b.order ⟨i.val - 1, by
      have := i.one_lt
      have := hi
      omega⟩ : Int) : ℚ)
  let H : ℚ := g / 2 + (ramificationIndex K : ℚ)
  have hprimary : (H : WithTop ℚ) <
      (g : WithTop ℚ) + a.centralCurrentDefect b i := by
    have h := hhalf.trans_le
      (a.representationAlphaPrime_le_primaryDefect b (i.current hi))
    simpa only [representationHalfGap, representationPrimaryDefect,
      centralCurrentDefect, CentralRepresentationIndex.current, g, H] using h
  have hsub := withTop_sub_lt_of_lt_add H g
    (a.centralCurrentDefect b i) hprimary
  convert hsub using 1
  norm_cast
  dsimp only [H, g]
  push_cast
  simp only [Rat.divInt_eq_div]
  push_cast
  ring

/-- If `A_i ≠ A'_i`, condition 2.1(ii) and domination force the preceding
central defect above the shifted complementary half-gap. -/
theorem centralPreviousDefect_gt_currentMismatchCut
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hi : i.val ≤ n + 1)
    (hne : a.representationAlpha b (i.current hi) ≠
      a.representationAlphaPrime b (i.current hi)) :
    ((((b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ - b.order ⟨i.val - 1, by
          have := i.one_lt
          have := hi
          omega⟩ : Int) : ℚ) +
        (ramificationIndex K : ℚ) -
        ((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by
            have := i.one_lt
            have := hi
            omega⟩ : Int) : ℚ) / 2 : ℚ) : WithTop ℚ) <
      a.centralPreviousDefect b i := by
  obtain ⟨hAlpha, hhalf⟩ :=
    a.representationAlpha_eq_halfGap_and_lt_prime_of_ne
      b (i.current hi) hne
  have hone := i.one_lt
  have hsmall := i.le_small_succ
  let g : ℚ := ((a.order ⟨i.val, i.lt_large⟩ -
    b.order ⟨i.val - 1, by
      have := i.one_lt
      have := hi
      omega⟩ : Int) : ℚ)
  let cut : ℚ := (ramificationIndex K : ℚ) - g / 2
  let targetShift : ℚ := ((b.order ⟨i.val - 1, by
    have := i.one_lt
    have := hi
    omega⟩ - b.order ⟨i.val - 2, by
    have := i.one_lt
    have := i.le_small_succ
    omega⟩ : Int) : ℚ)
  let targetCut : ℚ := cut - targetShift
  have hcurrent : (cut : WithTop ℚ) < a.centralCurrentDefect b i := by
    have h := a.centralCurrentDefect_gt_halfGapComplement b i hi hhalf
    simpa only [cut, g] using h
  let p : Fin n := ⟨i.val - 2, by
    have := i.le_small_succ
    omega⟩
  have hcurrentCap : a.centralCurrentDefect b i ≤
      (b.alphaValue p : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
      (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hindex : (⟨i.val - 1 - 1, by omega⟩ : Fin n) = p := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    rw [hindex] at hcap
    simpa only [centralCurrentDefect] using hcap
  have hbeta : (cut : WithTop ℚ) < (b.alphaValue p : WithTop ℚ) :=
    hcurrent.trans_le hcurrentCap
  have hremark := b.alpha_le_orderGap_add_cappedAdjacent p
  have hshifted : (cut : WithTop ℚ) <
      (targetShift : WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have hpSucc : p.succ = ⟨i.val - 1, by
        have := hi
        omega⟩ := by
      apply Fin.ext
      change i.val - 2 + 1 = i.val - 1
      omega
    have hpCast : p.castSucc = ⟨i.val - 2, by
        have := i.le_small_succ
        omega⟩ := by
      apply Fin.ext
      rfl
    have htwo : i.val - 2 + 2 = i.val := by omega
    rw [hpSucc, hpCast] at hremark
    exact hbeta.trans_le (by
      simpa only [targetShift, p, Fin.val_mk, htwo] using hremark)
  have htargetForward : (targetCut : WithTop ℚ) <
      b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have h := withTop_sub_lt_of_lt_add cut targetShift
      (b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) hshifted
    simpa only [targetCut] using h
  have htarget : (targetCut : WithTop ℚ) <
      b.truncatedPrefixDefect b (-1) i.val (i.val - 2) := by
    rw [← b.truncatedPrefixDefect_comm b (-1) (i.val - 2) i.val]
    exact htargetForward
  have hcross : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ < a.order ⟨i.val, i.lt_large⟩ :=
    a.sourceCurrent_gt_targetPrevious_of_halfGap_lt_alphaPrime
      b (i.current hi) i.one_lt hhalf
  have hhalfAbove : (targetCut : WithTop ℚ) <
      a.representationHalfGap b (i.current hi) := by
    unfold representationHalfGap
    simp only [CentralRepresentationIndex.current]
    norm_cast
    dsimp only [targetCut, targetShift, cut, g]
    push_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have hcrossQ :
        (b.order ⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : ℚ) <
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  have hdiagonal : (targetCut : WithTop ℚ) <
      a.truncatedPrefixDefect b 1 i.val i.val := by
    have hd := hdefect (i.current hi)
    rw [a.coe_representationAlphaValue b (i.current hi), hAlpha] at hd
    exact hhalfAbove.trans_le hd
  have hdomination := a.truncatedPrefixDefect_domination b b 1 (-1)
    i.val i.val (i.val - 2)
  simp only [one_mul] at hdomination
  have hresult := (lt_min hdiagonal htarget).trans_le hdomination
  unfold centralPreviousDefect
  convert hresult using 1
  norm_cast
  dsimp only [targetCut, targetShift, cut, g]
  push_cast
  simp only [Rat.divInt_eq_div]
  push_cast
  ring

end BONG.GoodBONG

end Bong
