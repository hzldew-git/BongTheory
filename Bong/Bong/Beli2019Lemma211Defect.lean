/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AdjacentCappedDefect
import Bong.Bong.Beli2019AlphaLocalFormula
import Bong.Bong.Beli2019AuxiliaryAlphaBounds
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 2.11: the two defect implications

Under the nonpositive secondary order shift, the capped-defect domination
triangle reduces condition 2.1(ii) to either adjacent alpha bound.  These are
the two directions of Lemma 2.11 needed in the proof of Lemma 2.13.
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

/-- Lemma 2.11(i), in the implication used by Lemma 2.13. -/
theorem representationDefectAt_of_le_nextFallbackAlphaBound
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < m + 1)
    (hpair :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hleft : a.order ⟨i.val, i.lt_large⟩ ≤
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩)
    (hbound : a.representationAlpha b i ≤
      a.nextFallbackAlphaBound i hiNext) :
    a.RepresentationDefectAt b i := by
  have hiSmall := i.le_small
  let sourcePair : Fin m := ⟨i.val, by omega⟩
  let targetPair : Fin n := ⟨i.val - 2, by omega⟩
  have hsourceCast : sourcePair.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsourceSucc : sourcePair.succ =
      (⟨i.val + 1, hiNext⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have htargetCast : targetPair.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have htargetAlpha :
      (⟨i.val - 1 - 1, by omega⟩ : Fin n) = targetPair := by
    apply Fin.ext
    simp only [targetPair]
    omega
  have hsourceAdjacent : a.representationAlpha b i ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.order_sub_add_alpha_le_cappedAdjacent sourcePair
    rw [hsourceCast, hsourceSucc] at hadjacent
    unfold nextFallbackAlphaBound at hbound
    apply hbound.trans
    simpa only [sourcePair, WithTop.coe_add] using hadjacent
  have hprimaryRight :=
    (a.representationAlpha_le_prime b i).trans
      (a.representationAlphaPrime_le_primaryRightCap b i)
  rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hprimaryRight
  rw [htargetAlpha] at hprimaryRight
  have hrightShift :
      ((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
        ((b.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) := by
    exact_mod_cast sub_le_sub_right hleft _
  have htargetFallback : a.representationAlpha b i ≤
      ((((b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (b.alphaValue targetPair : WithTop ℚ)) := by
    apply hprimaryRight.trans
    have hrightShiftTop :
        ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
          ((((b.order ⟨i.val - 2, by omega⟩ -
            b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) := by
      exact_mod_cast hrightShift
    simpa only [add_comm] using
      add_le_add_right hrightShiftTop (b.alphaValue targetPair : WithTop ℚ)
  have htargetAdjacent : a.representationAlpha b i ≤
      b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, w} K := targetLaws
      exact b.order_sub_add_alpha_le_cappedAdjacent targetPair
    rw [htargetCast, htargetSucc] at hadjacent
    apply htargetFallback.trans
    simpa only [targetPair, Nat.sub_add_cancel (show 2 ≤ i.val by omega),
      WithTop.coe_add] using hadjacent
  have hsecondary : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
    have hshift : secondaryShift ≤ 0 := by
      dsimp only [secondaryShift]
      exact_mod_cast (show
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
          b.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val - 1, by omega⟩ ≤ 0 by omega)
    have hcand := a.representationAlpha_le_secondary b i ⟨hiTwo, hiNext⟩
    unfold representationSecondaryDefect at hcand
    change a.representationAlpha b i ≤
      (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) at hcand
    calc
      a.representationAlpha b i ≤
          (secondaryShift : WithTop ℚ) +
            a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := hcand
      _ ≤ (0 : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
        have hshiftTop : (secondaryShift : WithTop ℚ) ≤ 0 := by
          exact_mod_cast hshift
        simpa only [add_comm] using
          add_le_add_right hshiftTop
            (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
      _ = a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) :=
        zero_add _
  have hmiddleDomination :
      min (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
          (b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) ≤
        a.truncatedPrefixDefect b (-1) (i.val + 2) i.val := by
    simpa only [one_mul] using
      (a.truncatedPrefixDefect_domination b b 1 (-1)
        (i.val + 2) (i.val - 2) i.val)
  have hmiddle : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b (-1) (i.val + 2) i.val :=
    (le_min hsecondary htargetAdjacent).trans hmiddleDomination
  have hfinalDomination :
      min (a.truncatedPrefixDefect a (-1) i.val (i.val + 2))
          (a.truncatedPrefixDefect b (-1) (i.val + 2) i.val) ≤
        a.truncatedPrefixDefect b 1 i.val i.val := by
    simpa only [neg_mul_neg, one_mul] using
      (a.truncatedPrefixDefect_domination a b (-1) (-1)
        i.val (i.val + 2) i.val)
  unfold RepresentationDefectAt
  exact (le_min hsourceAdjacent hmiddle).trans hfinalDomination

/-- Lemma 2.11(i), reverse implication.  The diagonal defect and the
secondary mixed defect recover the adjacent source defect; Remark 1.1 then
identifies its threshold with the shifted source alpha. -/
theorem le_nextFallbackAlphaBound_of_representationDefectAt
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < m + 1)
    (hpair :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hleft : a.order ⟨i.val, i.lt_large⟩ ≤
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩)
    (hdefect : a.RepresentationDefectAt b i) :
    a.representationAlpha b i ≤ a.nextFallbackAlphaBound i hiNext := by
  have hiSmall := i.le_small
  let sourcePair : Fin m := ⟨i.val, by omega⟩
  let targetPair : Fin n := ⟨i.val - 2, by omega⟩
  have hsourceCast : sourcePair.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsourceSucc : sourcePair.succ =
      (⟨i.val + 1, hiNext⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have htargetCast : targetPair.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have htargetAlpha :
      (⟨i.val - 1 - 1, by omega⟩ : Fin n) = targetPair := by
    apply Fin.ext
    simp only [targetPair]
    omega
  have hsecondary : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
    have hshift : secondaryShift ≤ 0 := by
      dsimp only [secondaryShift]
      exact_mod_cast (show
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
          b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ ≤ 0 by omega)
    have hcand := a.representationAlpha_le_secondary b i ⟨hiTwo, hiNext⟩
    unfold representationSecondaryDefect at hcand
    change a.representationAlpha b i ≤
      (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) at hcand
    calc
      a.representationAlpha b i ≤
          (secondaryShift : WithTop ℚ) +
            a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := hcand
      _ ≤ (0 : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
        have hshiftTop : (secondaryShift : WithTop ℚ) ≤ 0 := by
          exact_mod_cast hshift
        simpa only [add_comm] using
          add_le_add_right hshiftTop
            (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
      _ = a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := zero_add _
  have hprimaryRight :=
    (a.representationAlpha_le_prime b i).trans
      (a.representationAlphaPrime_le_primaryRightCap b i)
  rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hprimaryRight
  rw [htargetAlpha] at hprimaryRight
  have hrightShift :
      ((a.order ⟨i.val, i.lt_large⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
        ((b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) := by
    exact_mod_cast sub_le_sub_right hleft _
  have htargetFallback : a.representationAlpha b i ≤
      ((((b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (b.alphaValue targetPair : WithTop ℚ)) := by
    apply hprimaryRight.trans
    have hrightShiftTop :
        ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
          ((((b.order ⟨i.val - 2, by omega⟩ -
            b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) := by
      exact_mod_cast hrightShift
    simpa only [add_comm] using
      add_le_add_right hrightShiftTop (b.alphaValue targetPair : WithTop ℚ)
  have htargetAdjacent : a.representationAlpha b i ≤
      b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, w} K := targetLaws
      exact b.order_sub_add_alpha_le_cappedAdjacent targetPair
    rw [htargetCast, htargetSucc] at hadjacent
    apply htargetFallback.trans
    simpa only [targetPair, Nat.sub_add_cancel (show 2 ≤ i.val by omega),
      WithTop.coe_add] using hadjacent
  have hmiddleDomination :
      min (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
          (b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) ≤
        a.truncatedPrefixDefect b (-1) (i.val + 2) i.val := by
    simpa only [one_mul] using
      (a.truncatedPrefixDefect_domination b b 1 (-1)
        (i.val + 2) (i.val - 2) i.val)
  have hmiddle : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b (-1) (i.val + 2) i.val :=
    (le_min hsecondary htargetAdjacent).trans hmiddleDomination
  have hdiagonal : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    exact hdefect
  have hreverseDomination :
      min (a.truncatedPrefixDefect b 1 i.val i.val)
          (a.truncatedPrefixDefect b (-1) (i.val + 2) i.val) ≤
        a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    have h := a.truncatedPrefixDefect_domination b a 1 (-1)
      i.val i.val (i.val + 2)
    rw [b.truncatedPrefixDefect_comm a (-1) i.val (i.val + 2)] at h
    simpa only [one_mul] using h
  have hsourceAdjacent : a.representationAlpha b i ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) :=
    (le_min hdiagonal hmiddle).trans hreverseDomination
  have htargetAlphaHalf : (b.alphaValue targetPair : WithTop ℚ) ≤
      b.halfGapCandidate targetPair := by
    rw [← b.coe_halfGapValue targetPair]
    exact_mod_cast b.alphaValue_le_halfGapValue targetPair
  have hprimaryHalf : a.representationAlpha b i ≤
      ((((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        b.halfGapCandidate targetPair) :=
    hprimaryRight.trans (add_le_add_right htargetAlphaHalf _)
  have hhalfCompare :
      ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (b.halfGapValue targetPair : WithTop ℚ)) ≤
        ((((a.order ⟨i.val, i.lt_large⟩ -
          a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ) +
          a.halfGapCandidate sourcePair) := by
    rw [← a.coe_halfGapValue sourcePair]
    norm_cast
    unfold halfGapValue orderGap
    rw [htargetCast, htargetSucc, hsourceCast, hsourceSucc]
    have hpairQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) + (a.order ⟨i.val + 1, hiNext⟩ : ℚ) ≤
          (b.order ⟨i.val - 2, by omega⟩ : ℚ) +
            (b.order ⟨i.val - 1, by omega⟩ : ℚ) := by
      exact_mod_cast hpair
    push_cast
    linarith
  have hsourceHalf : a.representationAlpha b i ≤
      ((((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ) +
        a.halfGapCandidate sourcePair) :=
    hprimaryHalf.trans hhalfCompare
  have halpha := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact a.alpha_eq_min_halfGap_add_cappedAdjacent sourcePair
  rw [hsourceCast, hsourceSucc] at halpha
  unfold nextFallbackAlphaBound
  rw [halpha, add_min]
  apply le_min
  · exact hsourceHalf
  · let sourceShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ - a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ)
    let sourceGap : ℚ :=
      ((a.order ⟨i.val + 1, hiNext⟩ - a.order ⟨i.val, i.lt_large⟩ : Int) : ℚ)
    have hcancel : (sourceShift : WithTop ℚ) + (sourceGap : WithTop ℚ) = 0 := by
      norm_cast
      dsimp only [sourceShift, sourceGap]
      push_cast
      ring
    simpa only [sourcePair, sourceShift, sourceGap, ← add_assoc, hcancel,
      zero_add] using hsourceAdjacent

/-- Lemma 2.11(ii), in the implication used by Lemma 2.13. -/
theorem representationDefectAt_of_le_currentFallbackAlphaBound
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < m + 1)
    (hpair :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hright : a.order ⟨i.val + 1, hiNext⟩ ≤
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩)
    (hbound : a.representationAlpha b i ≤
      a.currentFallbackAlphaBound b i hiTwo) :
    a.RepresentationDefectAt b i := by
  have hiSmall := i.le_small
  let sourcePair : Fin m := ⟨i.val, by omega⟩
  let targetPair : Fin n := ⟨i.val - 2, by omega⟩
  have hsourceCast : sourcePair.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsourceSucc : sourcePair.succ =
      (⟨i.val + 1, hiNext⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have htargetCast : targetPair.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have hsourceAlpha :
      (⟨i.val + 1 - 1, by omega⟩ : Fin m) = sourcePair := by
    apply Fin.ext
    simp only [sourcePair]
    omega
  have htargetAdjacent : a.representationAlpha b i ≤
      b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, w} K := targetLaws
      exact b.order_sub_add_alpha_le_cappedAdjacent targetPair
    rw [htargetCast, htargetSucc] at hadjacent
    unfold currentFallbackAlphaBound at hbound
    apply hbound.trans
    simpa only [targetPair, Nat.sub_add_cancel (show 2 ≤ i.val by omega),
      WithTop.coe_add] using hadjacent
  have hprimaryLeft :=
    (a.representationAlpha_le_prime b i).trans
      (a.representationAlphaPrime_le_primaryLeftCap b i)
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hprimaryLeft
  rw [hsourceAlpha] at hprimaryLeft
  have hleftShift :
      ((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
        ((a.order ⟨i.val, i.lt_large⟩ -
          a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) := by
    exact_mod_cast sub_le_sub_left hright _
  have hsourceFallback : a.representationAlpha b i ≤
      ((((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue sourcePair : WithTop ℚ)) := by
    apply hprimaryLeft.trans
    have hleftShiftTop :
        ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
          ((((a.order ⟨i.val, i.lt_large⟩ -
            a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ)) := by
      exact_mod_cast hleftShift
    simpa only [add_comm] using
      add_le_add_right hleftShiftTop (a.alphaValue sourcePair : WithTop ℚ)
  have hsourceAdjacent : a.representationAlpha b i ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.order_sub_add_alpha_le_cappedAdjacent sourcePair
    rw [hsourceCast, hsourceSucc] at hadjacent
    apply hsourceFallback.trans
    simpa only [sourcePair, WithTop.coe_add] using hadjacent
  have hsecondary : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
    have hshift : secondaryShift ≤ 0 := by
      dsimp only [secondaryShift]
      exact_mod_cast (show
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
          b.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val - 1, by omega⟩ ≤ 0 by omega)
    have hcand := a.representationAlpha_le_secondary b i ⟨hiTwo, hiNext⟩
    unfold representationSecondaryDefect at hcand
    change a.representationAlpha b i ≤
      (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) at hcand
    calc
      a.representationAlpha b i ≤
          (secondaryShift : WithTop ℚ) +
            a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := hcand
      _ ≤ (0 : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
        have hshiftTop : (secondaryShift : WithTop ℚ) ≤ 0 := by
          exact_mod_cast hshift
        simpa only [add_comm] using
          add_le_add_right hshiftTop
            (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
      _ = a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) :=
        zero_add _
  have hmiddleDomination :
      min (a.truncatedPrefixDefect a (-1) i.val (i.val + 2))
          (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)) ≤
        a.truncatedPrefixDefect b (-1) i.val (i.val - 2) := by
    simpa only [mul_one] using
      (a.truncatedPrefixDefect_domination a b (-1) 1
        i.val (i.val + 2) (i.val - 2))
  have hmiddle : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b (-1) i.val (i.val - 2) :=
    (le_min hsourceAdjacent hsecondary).trans hmiddleDomination
  have hfinalDomination :
      min (a.truncatedPrefixDefect b (-1) i.val (i.val - 2))
          (b.truncatedPrefixDefect b (-1) (i.val - 2) i.val) ≤
        a.truncatedPrefixDefect b 1 i.val i.val := by
    simpa only [neg_mul_neg, one_mul] using
      (a.truncatedPrefixDefect_domination b b (-1) (-1)
        i.val (i.val - 2) i.val)
  unfold RepresentationDefectAt
  exact (le_min hmiddle htargetAdjacent).trans hfinalDomination

/-- Lemma 2.11(ii), reverse implication.  This is the target-side mirror of
`le_nextFallbackAlphaBound_of_representationDefectAt`. -/
theorem le_currentFallbackAlphaBound_of_representationDefectAt
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < n + 1)
    (hpair :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 2, by omega⟩ + b.order ⟨i.val - 1, by omega⟩)
    (hright : a.order ⟨i.val + 1, hiNext⟩ ≤
      b.order ⟨i.val - 1, by omega⟩)
    (hdefect : a.RepresentationDefectAt b i) :
    a.representationAlpha b i ≤ a.currentFallbackAlphaBound b i hiTwo := by
  let sourcePair : Fin n := ⟨i.val, by omega⟩
  let targetPair : Fin n := ⟨i.val - 2, by omega⟩
  have hsourceCast : sourcePair.castSucc =
      (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hsourceSucc : sourcePair.succ =
      (⟨i.val + 1, hiNext⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetCast : targetPair.castSucc =
      (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have hsourceAlpha :
      (⟨i.val + 1 - 1, by omega⟩ : Fin n) = sourcePair := by
    apply Fin.ext
    simp only [sourcePair]
    omega
  have hsecondary : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
    let secondaryShift : ℚ :=
      ((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
        b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
    have hshift : secondaryShift ≤ 0 := by
      dsimp only [secondaryShift]
      exact_mod_cast (show
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ -
          b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ ≤ 0 by omega)
    have hcand := a.representationAlpha_le_secondary b i ⟨hiTwo, hiNext⟩
    unfold representationSecondaryDefect at hcand
    change a.representationAlpha b i ≤
      (secondaryShift : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) at hcand
    calc
      a.representationAlpha b i ≤
          (secondaryShift : WithTop ℚ) +
            a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := hcand
      _ ≤ (0 : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := by
        have hshiftTop : (secondaryShift : WithTop ℚ) ≤ 0 := by
          exact_mod_cast hshift
        simpa only [add_comm] using
          add_le_add_right hshiftTop
            (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2))
      _ = a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2) := zero_add _
  have hprimaryLeft :=
    (a.representationAlpha_le_prime b i).trans
      (a.representationAlphaPrime_le_primaryLeftCap b i)
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hprimaryLeft
  rw [hsourceAlpha] at hprimaryLeft
  have hleftShift :
      ((a.order ⟨i.val, i.lt_large⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
        ((a.order ⟨i.val, i.lt_large⟩ - a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) := by
    exact_mod_cast sub_le_sub_left hright _
  have hsourceFallback : a.representationAlpha b i ≤
      ((((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ) +
          (a.alphaValue sourcePair : WithTop ℚ)) := by
    apply hprimaryLeft.trans
    have hleftShiftTop :
        ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
          ((((a.order ⟨i.val, i.lt_large⟩ -
            a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ)) := by
      exact_mod_cast hleftShift
    simpa only [add_comm] using
      add_le_add_right hleftShiftTop (a.alphaValue sourcePair : WithTop ℚ)
  have hsourceAdjacent : a.representationAlpha b i ≤
      a.truncatedPrefixDefect a (-1) i.val (i.val + 2) := by
    have hadjacent := by
      letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
      exact a.order_sub_add_alpha_le_cappedAdjacent sourcePair
    rw [hsourceCast, hsourceSucc] at hadjacent
    apply hsourceFallback.trans
    simpa only [sourcePair, WithTop.coe_add] using hadjacent
  have hmiddleDomination :
      min (a.truncatedPrefixDefect a (-1) i.val (i.val + 2))
          (a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)) ≤
        a.truncatedPrefixDefect b (-1) i.val (i.val - 2) := by
    simpa only [mul_one] using
      (a.truncatedPrefixDefect_domination a b (-1) 1
        i.val (i.val + 2) (i.val - 2))
  have hmiddle : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b (-1) i.val (i.val - 2) :=
    (le_min hsourceAdjacent hsecondary).trans hmiddleDomination
  have hdiagonal : a.representationAlpha b i ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
    exact hdefect
  have hreverseDomination :
      min (a.truncatedPrefixDefect b (-1) i.val (i.val - 2))
          (a.truncatedPrefixDefect b 1 i.val i.val) ≤
        b.truncatedPrefixDefect b (-1) (i.val - 2) i.val := by
    have h := b.truncatedPrefixDefect_domination a b (-1) 1
      (i.val - 2) i.val i.val
    rw [← a.truncatedPrefixDefect_comm b (-1) i.val (i.val - 2)] at h
    simpa only [mul_one] using h
  have htargetAdjacent : a.representationAlpha b i ≤
      b.truncatedPrefixDefect b (-1) (i.val - 2) i.val :=
    (le_min hmiddle hdiagonal).trans hreverseDomination
  have hsourceAlphaHalf : (a.alphaValue sourcePair : WithTop ℚ) ≤
      a.halfGapCandidate sourcePair := by
    rw [← a.coe_halfGapValue sourcePair]
    exact_mod_cast a.alphaValue_le_halfGapValue sourcePair
  have hprimaryHalf : a.representationAlpha b i ≤
      ((((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.halfGapCandidate sourcePair) :=
    hprimaryLeft.trans (add_le_add_right hsourceAlphaHalf _)
  have hhalfCompare :
      ((((a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.halfGapCandidate sourcePair) ≤
        ((((b.order ⟨i.val - 2, by omega⟩ -
          b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          b.halfGapCandidate targetPair) := by
    rw [← a.coe_halfGapValue sourcePair,
      ← b.coe_halfGapValue targetPair]
    norm_cast
    unfold halfGapValue orderGap
    rw [hsourceCast, hsourceSucc, htargetCast, htargetSucc]
    have hpairQ :
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) + (a.order ⟨i.val + 1, hiNext⟩ : ℚ) ≤
          (b.order ⟨i.val - 2, by omega⟩ : ℚ) +
            (b.order ⟨i.val - 1, by omega⟩ : ℚ) := by
      exact_mod_cast hpair
    push_cast
    linarith
  have htargetHalf : a.representationAlpha b i ≤
      ((((b.order ⟨i.val - 2, by omega⟩ -
        b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        b.halfGapCandidate targetPair) :=
    hprimaryHalf.trans hhalfCompare
  have halpha := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    exact b.alpha_eq_min_halfGap_add_cappedAdjacent targetPair
  rw [htargetCast, htargetSucc] at halpha
  unfold currentFallbackAlphaBound
  rw [halpha, add_min]
  apply le_min
  · exact htargetHalf
  · let targetShift : ℚ :=
      ((b.order ⟨i.val - 2, by omega⟩ - b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
    let targetGap : ℚ :=
      ((b.order ⟨i.val - 1, by omega⟩ - b.order ⟨i.val - 2, by omega⟩ : Int) : ℚ)
    have hcancel : (targetShift : WithTop ℚ) + (targetGap : WithTop ℚ) = 0 := by
      norm_cast
      dsimp only [targetShift, targetGap]
      push_cast
      ring
    simpa only [targetPair, Nat.sub_add_cancel (show 2 ≤ i.val by omega),
      targetShift, targetGap, ← add_assoc, hcancel, zero_add] using htargetAdjacent

end BONG.GoodBONG

end Bong
