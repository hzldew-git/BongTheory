/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma63
import Bong.Bong.Beli2019KeyLemma
import Bong.Bong.Beli2019Lemma69TypeIBetaSecondary
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Lemma 6.9(v): a type-I first boundary

This file formalizes the `s = t` argument in the proof of Lemma 6.9(v).
At the first unequal order, the target order is two above the source order.
The primary and secondary candidates for `A_s` are both at least
`alpha_s - 2`; Lemma 2.14 removes the half-gap candidate.  Consequently the
first even coordinate of the type-I `W`-interval satisfies the direct
comparison.  The statement is translation invariant and is therefore suited
to the shifted type-I interval obtained by reverse duality.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 3000000 in
-- Dependent prefix-index transport and extended-defect arithmetic need extra heartbeats.
/-- At a first gap-two boundary, the primary mixed-defect candidate is at
least the source alpha minus two. -/
theorem lemma69_v_firstGapTwo_primary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val)
    (hprefix : ∀ k, k < i.val - 1 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htarget : b.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ + 2) :
    ((a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ - 2 : ℚ) : WithTop ℚ) ≤
      a.representationPrimaryDefect b i := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hiPreviousAlpha : i.val - 2 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, hiPreviousAlpha⟩
  let previousIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, by omega, hiPrevious, by
      have hi := i.lt_large
      omega⟩
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPrevious⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetP : b.order p.castSucc = a.order p.castSucc + 2 := by
    rw [hpCast]
    simpa only [p] using htarget
  have hprevious : a.representationAlpha b previousIdx =
      (a.alphaValue previous : WithTop ℚ) := by
    have hsame := a.beli2019Lemma63_sameRank b hdefect previousIdx (by
      intro k hk
      exact hprefix k (by
        simpa only [previousIdx] using hk))
    have hindex : (⟨i.val - 1 - 1, by
        have hi := i.lt_large
        omega⟩ : Fin (n + 1)) = previous := by
      apply Fin.ext
      simp only [previous]
      omega
    rw [hindex] at hsame
    simpa only [previousIdx] using hsame
  let shift : ℚ :=
    ((a.order p.succ - a.order p.castSucc : Int) : ℚ)
  let selfDefect := a.truncatedPrefixDefect a (-1)
    (i.val + 1) (i.val - 1)
  let diagonalDefect := a.truncatedPrefixDefect b 1
    (i.val - 1) (i.val - 1)
  let crossDefect := a.truncatedPrefixDefect b (-1)
    (i.val + 1) (i.val - 1)
  have hlocalRaw := a.alpha_le_orderGap_add_cappedAdjacent p
  have hlocal : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + selfDefect := by
    dsimp only [selfDefect]
    rw [a.truncatedPrefixDefect_comm a (-1)
      (i.val + 1) (i.val - 1)]
    simpa only [shift, p, Fin.val_succ, Fin.val_castSucc,
      show i.val - 1 + 2 = i.val + 1 by omega] using hlocalRaw
  have hdiagonal : (a.alphaValue previous : WithTop ℚ) ≤
      diagonalDefect := by
    calc
      (a.alphaValue previous : WithTop ℚ) =
          a.representationAlpha b previousIdx := hprevious.symm
      _ = (a.representationAlphaValue b previousIdx : WithTop ℚ) :=
        (a.coe_representationAlphaValue b previousIdx).symm
      _ ≤ a.truncatedPrefixDefect b 1 previousIdx.val previousIdx.val :=
        hdefect previousIdx
      _ = diagonalDefect := rfl
  have hendpoint := a.alphaRightEndpoint_antitone
    (show previous ≤ p by
      change previous.val ≤ p.val
      simp only [previous, p]
      omega)
  have hpreviousSucc : previous.succ = p.castSucc := by
    apply Fin.ext
    simp only [previous, p, Fin.val_succ, Fin.val_castSucc]
    omega
  have hpreviousShift : a.alphaValue p ≤
      shift + a.alphaValue previous := by
    unfold alphaRightEndpoint at hendpoint
    rw [hpreviousSucc] at hendpoint
    dsimp only [shift]
    push_cast at hendpoint ⊢
    linarith
  have hpreviousBound : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + diagonalDefect := by
    calc
      (a.alphaValue p : WithTop ℚ) ≤
          (shift : WithTop ℚ) +
            (a.alphaValue previous : WithTop ℚ) := by
        exact_mod_cast hpreviousShift
      _ ≤ (shift : WithTop ℚ) + diagonalDefect := by
        simpa only [add_comm] using
          add_le_add_right hdiagonal (shift : WithTop ℚ)
  have hdomRaw := a.truncatedPrefixDefect_domination a b
    (-1) 1 (i.val + 1) (i.val - 1) (i.val - 1)
  have hdom : min selfDefect diagonalDefect ≤ crossDefect := by
    dsimp only [selfDefect, diagonalDefect, crossDefect]
    simpa only [mul_one] using hdomRaw
  have hminimum : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + min selfDefect diagonalDefect :=
    withTop_le_shift_add_min _ shift _ _ hlocal hpreviousBound
  have hcross : (a.alphaValue p : WithTop ℚ) ≤
      (shift : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hdom (shift : WithTop ℚ))
  have htranslated := add_le_add_right hcross ((-2 : ℚ) : WithTop ℚ)
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) = shift - 2 := by
    rw [← hpSucc, ← hpCast, htargetP]
    dsimp only [shift]
    push_cast
    ring
  unfold representationPrimaryDefect
  rw [hcoefficient]
  have hleftTranslate :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) =
        ((a.alphaValue p - 2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue p + (-2 : ℚ) =
      a.alphaValue p - 2 by ring)
  have hrightTranslate :
      ((shift : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) =
        ((shift - 2 : ℚ) : WithTop ℚ) + crossDefect := by
    rw [sub_eq_add_neg, WithTop.coe_add]
    ac_rfl
  have htranslated' :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) ≤
        ((shift : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) := by
    simpa only [add_comm] using htranslated
  rw [hleftTranslate, hrightTranslate] at htranslated'
  simpa only [crossDefect, p] using htranslated'

set_option maxHeartbeats 5000000 in
-- This branch combines two defect dominations and several dependent index normalizations.
/-- At a first gap-two boundary, the secondary mixed-defect candidate is at
least the source alpha minus two. -/
theorem lemma69_v_firstGapTwo_secondary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hprefix : ∀ k, k < i.val - 1 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htarget : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ + 2) :
    ((a.alphaValue ⟨i.val - 1, by omega⟩ - 2 : ℚ) : WithTop ℚ) ≤
      a.representationSecondaryDefect b i hi := by
  have hiNext : i.val + 1 < n + 2 := hi.2
  have hiAlpha : i.val - 1 < n + 1 := by
    have hiLarge := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  let coefficient : ℚ :=
    ((a.order ⟨i.val, i.lt_large⟩ +
      a.order ⟨i.val + 1, hiNext⟩ -
      a.order ⟨i.val - 2, by omega⟩ -
      a.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
  let leftDefect := a.truncatedPrefixDefect a (-1)
    (i.val - 2) i.val
  let rightDefect := a.truncatedPrefixDefect a (-1)
    i.val (i.val + 2)
  let diagonalDefect := a.truncatedPrefixDefect b 1
    (i.val - 2) (i.val - 2)
  let middleDefect := a.truncatedPrefixDefect b (-1)
    i.val (i.val - 2)
  let crossDefect := a.truncatedPrefixDefect b 1
    (i.val + 2) (i.val - 2)
  have hleftGoodRaw := a.good
    (⟨i.val - 1, by omega⟩ : Fin (n + 2)) (by
      change (i.val - 1) + 2 < n + 2
      omega)
  have hleftGood : a.order ⟨i.val - 1, by omega⟩ ≤
      a.order ⟨i.val + 1, hiNext⟩ := by
    have hindex :
        (⟨(⟨i.val - 1, by omega⟩ : Fin (n + 2)).val + 2,
          by
            change (i.val - 1) + 2 < n + 2
            omega⟩ : Fin (n + 2)) = ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      change (i.val - 1) + 2 = i.val + 1
      omega
    rw [hindex] at hleftGoodRaw
    exact hleftGoodRaw
  have hrightGoodRaw := a.good
    (⟨i.val - 2, by omega⟩ : Fin (n + 2)) (by
      change (i.val - 2) + 2 < n + 2
      omega)
  have hrightGood : a.order ⟨i.val - 2, by omega⟩ ≤
      a.order ⟨i.val, i.lt_large⟩ := by
    have hindex :
        (⟨(⟨i.val - 2, by omega⟩ : Fin (n + 2)).val + 2,
          by
            change (i.val - 2) + 2 < n + 2
            omega⟩ : Fin (n + 2)) = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change (i.val - 2) + 2 = i.val
      omega
    rw [hindex] at hrightGoodRaw
    exact hrightGoodRaw
  let previous : Fin (n + 1) := ⟨i.val - 2, by omega⟩
  let next : Fin (n + 1) := ⟨i.val, by omega⟩
  have hleftRaw := a.alpha_le_order_sub_add_cappedAdjacent
    (i := p) (j := previous) (by
      change previous.val ≤ p.val
      simp only [previous, p]
      omega)
  have hleftShift :
      ((a.order p.succ - a.order previous.castSucc : Int) : ℚ) ≤
        coefficient := by
    have hpreviousCast : previous.castSucc =
        (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hpSucc, hpreviousCast]
    dsimp only [coefficient]
    push_cast
    have hgoodQ : (a.order ⟨i.val - 1, by omega⟩ : ℚ) ≤
        a.order ⟨i.val + 1, hiNext⟩ := by
      exact_mod_cast hleftGood
    linarith
  have hleftAlpha : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + leftDefect := by
    have hshiftTop :
        ((((a.order p.succ - a.order previous.castSucc : Int) : ℚ)) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hleftShift
    have hraw : (a.alphaValue p : WithTop ℚ) ≤
        ((((a.order p.succ - a.order previous.castSucc : Int) : ℚ)) :
          WithTop ℚ) + leftDefect := by
      simpa only [previous, leftDefect,
        show i.val - 2 + 2 = i.val by omega] using hleftRaw
    exact hraw.trans (by
      simpa only [add_comm] using add_le_add_right hshiftTop leftDefect)
  have hrightRaw := a.alpha_le_laterOrder_sub_add_cappedAdjacent
    (i := p) (j := next) (by
      change p.val ≤ next.val
      simp only [p, next]
      omega)
  have hrightShift :
      ((a.order next.succ - a.order p.castSucc : Int) : ℚ) ≤
        coefficient := by
    have hnextSucc : next.succ =
        (⟨i.val + 1, hiNext⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hnextSucc, hpCast]
    dsimp only [coefficient]
    push_cast
    have hgoodQ : (a.order ⟨i.val - 2, by omega⟩ : ℚ) ≤
        a.order ⟨i.val, i.lt_large⟩ := by
      exact_mod_cast hrightGood
    linarith
  have hrightAlpha : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + rightDefect := by
    have hshiftTop :
        ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hrightShift
    have hraw : (a.alphaValue p : WithTop ℚ) ≤
        ((((a.order next.succ - a.order p.castSucc : Int) : ℚ)) :
          WithTop ℚ) + rightDefect := by
      simpa only [next, rightDefect] using hrightRaw
    exact hraw.trans (by
      simpa only [add_comm] using add_le_add_right hshiftTop rightDefect)
  have hdiagonalBound : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + diagonalDefect := by
    by_cases hiThree : 2 < i.val
    · have hiEarlier : i.val - 2 < n + 2 := by
        have hiLarge := i.lt_large
        omega
      have hiPreviousTwoAlpha : i.val - 3 < n + 1 := by
        have hiLarge := i.lt_large
        omega
      let previousTwo : Fin (n + 1) :=
        ⟨i.val - 3, hiPreviousTwoAlpha⟩
      let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val - 2, by omega, hiEarlier, by
          have hiLarge := i.lt_large
          omega⟩
      have hearlier : a.representationAlpha b earlierIdx =
          (a.alphaValue previousTwo : WithTop ℚ) := by
        have hsame := a.beli2019Lemma63_sameRank b hdefect earlierIdx (by
          intro k hk
          apply hprefix k
          change k < i.val - 2 at hk
          omega)
        have hindex : (⟨i.val - 2 - 1, by
            have hiLarge := i.lt_large
            omega⟩ : Fin (n + 1)) = previousTwo := by
          apply Fin.ext
          simp only [previousTwo]
          omega
        rw [hindex] at hsame
        simpa only [earlierIdx] using hsame
      have hdiagonal : (a.alphaValue previousTwo : WithTop ℚ) ≤
          diagonalDefect := by
        calc
          (a.alphaValue previousTwo : WithTop ℚ) =
              a.representationAlpha b earlierIdx := hearlier.symm
          _ = (a.representationAlphaValue b earlierIdx : WithTop ℚ) :=
            (a.coe_representationAlphaValue b earlierIdx).symm
          _ ≤ a.truncatedPrefixDefect b 1
              earlierIdx.val earlierIdx.val := hdefect earlierIdx
          _ = diagonalDefect := rfl
      have hendpoint := a.alphaRightEndpoint_antitone
        (show previousTwo ≤ p by
          change previousTwo.val ≤ p.val
          simp only [previousTwo, p]
          omega)
      have hpreviousTwoSucc : previousTwo.succ =
          (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [previousTwo, Fin.val_succ]
        omega
      have hrecurrence : a.alphaValue p ≤
          coefficient + a.alphaValue previousTwo := by
        unfold alphaRightEndpoint at hendpoint
        rw [hpSucc, hpreviousTwoSucc] at hendpoint
        dsimp only [coefficient]
        push_cast at hendpoint ⊢
        have hgoodQ : (a.order ⟨i.val - 1, by omega⟩ : ℚ) ≤
            a.order ⟨i.val + 1, hiNext⟩ := by
          exact_mod_cast hleftGood
        linarith
      calc
        (a.alphaValue p : WithTop ℚ) ≤
            (coefficient : WithTop ℚ) +
              (a.alphaValue previousTwo : WithTop ℚ) := by
          exact_mod_cast hrecurrence
        _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
          simpa only [add_comm] using
            add_le_add_right hdiagonal (coefficient : WithTop ℚ)
    · have hiEq : i.val = 2 := by omega
      have htop : diagonalDefect = ⊤ := by
        dsimp only [diagonalDefect]
        rw [hiEq]
        norm_num
        rw [a.truncatedPrefixDefect_zero_right_eq_self b 1 0]
        unfold truncatedPrefixDefect
        rw [a.prefixAlphaCap_zero]
        simp only [inf_top_eq]
        rw [show (1 : Kˣ) * a.prefixProduct 0 * a.prefixProduct 0 = 1 by
          simp [GoodBONG.prefixProduct]]
        rw [defectOrder_eq_top_of_isSquare]
        exact IsSquare.one
      rw [htop]
      simp
  have hfirstDom := a.truncatedPrefixDefect_domination a b
    (-1) 1 i.val (i.val - 2) (i.val - 2)
  have hfirstMin : min leftDefect diagonalDefect ≤ middleDefect := by
    dsimp only [leftDefect, diagonalDefect, middleDefect]
    rw [← a.truncatedPrefixDefect_comm a (-1) i.val (i.val - 2)]
    simpa only [mul_one] using hfirstDom
  have hsecondDom := a.truncatedPrefixDefect_domination a b
    (-1) (-1) (i.val + 2) i.val (i.val - 2)
  have hsecondMin : min rightDefect middleDefect ≤ crossDefect := by
    dsimp only [rightDefect, middleDefect, crossDefect]
    rw [← a.truncatedPrefixDefect_comm a (-1) (i.val + 2) i.val]
    simpa only [neg_mul, one_mul, neg_neg] using hsecondDom
  have hnested : min rightDefect
      (min leftDefect diagonalDefect) ≤ crossDefect :=
    (min_le_min_left rightDefect hfirstMin).trans hsecondMin
  have hminimum : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + min rightDefect
        (min leftDefect diagonalDefect) :=
    withTop_le_shift_add_min _ coefficient _ _ hrightAlpha
      (withTop_le_shift_add_min _ coefficient _ _
        hleftAlpha hdiagonalBound)
  have hcrossBound : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hnested (coefficient : WithTop ℚ))
  have hearlierOrder : b.order ⟨i.val - 2, by omega⟩ =
      a.order ⟨i.val - 2, by omega⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact (hprefix (i.val - 2) (by omega)).symm
  have htranslated := add_le_add_right hcrossBound
    ((-2 : ℚ) : WithTop ℚ)
  unfold representationSecondaryDefect
  rw [hearlierOrder, htarget]
  have hcoefficient :
      ((a.order ⟨i.val, i.lt_large⟩ +
        a.order ⟨i.val + 1, hiNext⟩ -
        a.order ⟨i.val - 2, by omega⟩ -
        (a.order ⟨i.val - 1, by omega⟩ + 2) : Int) : ℚ) =
        coefficient - 2 := by
    dsimp only [coefficient]
    push_cast
    ring
  rw [hcoefficient]
  have hleftTranslate :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) =
        ((a.alphaValue p - 2 : ℚ) : WithTop ℚ) := by
    exact_mod_cast (show a.alphaValue p + (-2 : ℚ) =
      a.alphaValue p - 2 by ring)
  have hrightTranslate :
      ((coefficient : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) =
        ((coefficient - 2 : ℚ) : WithTop ℚ) + crossDefect := by
    rw [sub_eq_add_neg, WithTop.coe_add]
    ac_rfl
  have htranslated' :
      (a.alphaValue p : WithTop ℚ) + ((-2 : ℚ) : WithTop ℚ) ≤
        ((coefficient : WithTop ℚ) + crossDefect) +
          ((-2 : ℚ) : WithTop ℚ) := by
    simpa only [add_comm] using htranslated
  rw [hleftTranslate, hrightTranslate] at htranslated'
  simpa only [crossDefect, p] using htranslated'

/-- If the next source order is still below the first raised target order, the
half-gap candidate cannot define the representation alpha. -/
theorem lemma69_v_firstGapTwo_eq_prime
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hfar : a.order ⟨i.val + 1, hiNext⟩ <
      b.order ⟨i.val - 1, by omega⟩) :
    a.representationAlpha b i = a.representationAlphaPrime b i := by
  by_contra hne
  have hsplit := a.representationAlpha_eq_halfGap_and_lt_prime_of_ne b i hne
  have hreverse := a.sourceNext_gt_targetCurrent_of_halfGap_lt_alphaPrime
    b i hiNext hsplit.2
  exact (lt_asymm hfar hreverse)

/-- The local `s = t` argument of Lemma 6.9(v): at a first gap-two boundary,
`A_s` is at least `alpha_s - 2`. -/
theorem lemma69_v_firstGapTwo_alpha_lower
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hprefix : ∀ k, k < i.val - 1 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htarget : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ + 2)
    (hfar : a.order ⟨i.val + 1, hi.2⟩ <
      b.order ⟨i.val - 1, by omega⟩) :
    ((a.alphaValue ⟨i.val - 1, by omega⟩ - 2 : ℚ) : WithTop ℚ) ≤
      a.representationAlpha b i := by
  rw [a.lemma69_v_firstGapTwo_eq_prime b i hi.2 hfar,
    a.representationAlphaPrime_eq_min_primary_secondary b i hi]
  exact le_min
    (a.lemma69_v_firstGapTwo_primary b hdefect i hi.1 hprefix htarget)
    (a.lemma69_v_firstGapTwo_secondary b hdefect i hi hprefix htarget)

/-- The first gap-two boundary satisfies the direct comparison of the two
left-endpoint weight sequences. -/
theorem lemma69_v_firstGapTwo_weight
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hprefix : ∀ k, k < i.val - 1 →
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k)
    (htarget : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ + 2)
    (hfar : a.order ⟨i.val + 1, hi.2⟩ <
      b.order ⟨i.val - 1, by omega⟩) :
    a.alphaLeftEndpoint ⟨i.val - 1, by omega⟩ ≤
      b.alphaLeftEndpoint ⟨i.val - 1, by omega⟩ := by
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hlower := a.lemma69_v_firstGapTwo_alpha_lower
    b hdefect i hi hprefix htarget hfar
  have hupper := a.representationAlpha_le_rightAlpha b hdefect i
  have halphaTop : ((a.alphaValue p - 2 : ℚ) : WithTop ℚ) ≤
      (b.alphaValue p : WithTop ℚ) := by
    simpa only [p] using hlower.trans hupper
  have halpha : a.alphaValue p - 2 ≤ b.alphaValue p := by
    exact_mod_cast halphaTop
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htargetP : b.order p.castSucc = a.order p.castSucc + 2 := by
    rw [hpCast]
    simpa only [p] using htarget
  unfold alphaLeftEndpoint
  have htargetQ : (b.order p.castSucc : ℚ) =
      (a.order p.castSucc : ℚ) + 2 := by
    exact_mod_cast htargetP
  simpa only [p] using (show
    (a.order p.castSucc : ℚ) + a.alphaValue p ≤
      (b.order p.castSucc : ℚ) + b.alphaValue p by linarith)

end BONG.GoodBONG

end Bong
