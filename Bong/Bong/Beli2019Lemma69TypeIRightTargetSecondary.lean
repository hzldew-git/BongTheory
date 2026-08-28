/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightTargetPrimary

/-!
# Beli (2019), Lemma 6.9(ii): the type-I right secondary candidate

The secondary candidate on the target-right branch is propagated backwards
by two positions.  The diagonal input is the target-alpha equality two
boundaries later; the remaining four defects are combined by two applications
of capped-defect domination.
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
-- Two domination cuts carry several proof-dependent prefix indices.
/-- If the source and target adjacent sums agree, a target value two
positions later bounds the current secondary representation candidate. -/
theorem lemma69_typeI_right_beta_le_secondary_of_later
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hpairsum :
      a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hi.2⟩ =
        b.order ⟨i.val, i.lt_large⟩ +
          b.order ⟨i.val + 1, hi.2⟩)
    (hlater : ∀ hbound : i.val + 2 < n + 2,
      a.representationAlpha b
          (⟨i.val + 2, by omega, hbound, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (b.alphaValue ⟨i.val + 1, by omega⟩ : WithTop ℚ)) :
    (b.alphaValue ⟨i.val - 1, by
      have hb := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationSecondaryDefect b i hi := by
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hb := i.lt_large
    omega⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, by omega⟩
  let next : Fin (n + 1) := ⟨i.val, by omega⟩
  let coefficient : ℚ :=
    ((b.order ⟨i.val, i.lt_large⟩ +
      b.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by omega⟩ -
      b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ)
  let leftDefect := b.truncatedPrefixDefect b (-1)
    (i.val - 2) i.val
  let rightDefect := b.truncatedPrefixDefect b (-1)
    i.val (i.val + 2)
  let diagonalDefect := a.truncatedPrefixDefect b 1
    (i.val + 2) (i.val + 2)
  let middleDefect := a.truncatedPrefixDefect b (-1)
    (i.val + 2) i.val
  let crossDefect := a.truncatedPrefixDefect b 1
    (i.val + 2) (i.val - 2)
  have hiPreviousBound : i.val - 1 < n + 2 := by
    have hb := i.lt_large
    omega
  have hiPreviousGood : (i.val - 1) + 2 < n + 2 := by
    omega
  have hleftGoodRaw := b.good
    (⟨i.val - 1, hiPreviousBound⟩ : Fin (n + 2)) hiPreviousGood
  have hleftGood : b.order ⟨i.val - 1, by omega⟩ ≤
      b.order ⟨i.val + 1, hi.2⟩ := by
    have hindex :
        (⟨(⟨i.val - 1, by omega⟩ : Fin (n + 2)).val + 2,
          by omega⟩ : Fin (n + 2)) = ⟨i.val + 1, hi.2⟩ := by
      apply Fin.ext
      change (i.val - 1) + 2 = i.val + 1
      omega
    rw [hindex] at hleftGoodRaw
    exact hleftGoodRaw
  have hiTwoPreviousBound : i.val - 2 < n + 2 := by
    have hb := i.lt_large
    omega
  have hiTwoPreviousGood : (i.val - 2) + 2 < n + 2 := by
    omega
  have hrightGoodRaw := b.good
    (⟨i.val - 2, hiTwoPreviousBound⟩ : Fin (n + 2))
      hiTwoPreviousGood
  have hrightGood : b.order ⟨i.val - 2, by omega⟩ ≤
      b.order ⟨i.val, i.lt_large⟩ := by
    have hindex :
        (⟨(⟨i.val - 2, by omega⟩ : Fin (n + 2)).val + 2,
          by omega⟩ : Fin (n + 2)) = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change (i.val - 2) + 2 = i.val
      omega
    rw [hindex] at hrightGoodRaw
    exact hrightGoodRaw
  have hleftShift :
      ((b.order p.succ - b.order previous.castSucc : Int) : ℚ) ≤
        coefficient := by
    have hpSucc : p.succ =
        (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
      omega
    have hpreviousCast : previous.castSucc =
        (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hpSucc, hpreviousCast]
    dsimp only [coefficient]
    push_cast
    have hgoodQ : (b.order ⟨i.val - 1, by omega⟩ : ℚ) ≤
        b.order ⟨i.val + 1, hi.2⟩ := by
      exact_mod_cast hleftGood
    linarith
  have hrightShift :
      ((b.order next.succ - b.order p.castSucc : Int) : ℚ) ≤
        coefficient := by
    have hnextSucc : next.succ =
        (⟨i.val + 1, hi.2⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hpCast : p.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hnextSucc, hpCast]
    dsimp only [coefficient]
    push_cast
    have hgoodQ : (b.order ⟨i.val - 2, by omega⟩ : ℚ) ≤
        b.order ⟨i.val, i.lt_large⟩ := by
      exact_mod_cast hrightGood
    linarith
  have hleftRaw := b.alpha_le_order_sub_add_cappedAdjacent
    (i := p) (j := previous) (by
      change previous.val ≤ p.val
      simp only [previous, p]
      omega)
  have hleftBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + leftDefect := by
    have hshiftTop :
        ((((b.order p.succ - b.order previous.castSucc : Int) : ℚ)) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hleftShift
    have hraw : (b.alphaValue p : WithTop ℚ) ≤
        ((((b.order p.succ - b.order previous.castSucc : Int) : ℚ)) :
          WithTop ℚ) + leftDefect := by
      simpa only [previous, leftDefect,
        show i.val - 2 + 2 = i.val by omega] using hleftRaw
    exact hraw.trans (by
      simpa only [add_comm] using add_le_add_right hshiftTop leftDefect)
  have hrightRaw := b.alpha_le_laterOrder_sub_add_cappedAdjacent
    (i := p) (j := next) (by
      change p.val ≤ next.val
      simp only [p, next]
      omega)
  have hrightBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + rightDefect := by
    have hshiftTop :
        ((((b.order next.succ - b.order p.castSucc : Int) : ℚ)) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hrightShift
    have hraw : (b.alphaValue p : WithTop ℚ) ≤
        ((((b.order next.succ - b.order p.castSucc : Int) : ℚ)) :
          WithTop ℚ) + rightDefect := by
      simpa only [next, rightDefect] using hrightRaw
    exact hraw.trans (by
      simpa only [add_comm] using add_le_add_right hshiftTop rightDefect)
  have hdiagonalBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + diagonalDefect := by
    by_cases hfullIndex : i.val + 2 = n + 2
    · have htop : diagonalDefect = ⊤ := by
        dsimp only [diagonalDefect]
        simpa only [hfullIndex] using
          a.truncatedPrefixDefect_full_eq_top b
      rw [htop]
      simp
    · have hbound : i.val + 2 < n + 2 := by omega
      let laterIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val + 2, by omega, hbound, by omega⟩
      let laterAlpha : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      have hlaterEq : a.representationAlpha b laterIdx =
          (b.alphaValue laterAlpha : WithTop ℚ) := by
        simpa only [laterIdx, laterAlpha] using hlater hbound
      have hdiag : (b.alphaValue laterAlpha : WithTop ℚ) ≤
          diagonalDefect := by
        calc
          (b.alphaValue laterAlpha : WithTop ℚ) =
              a.representationAlpha b laterIdx := hlaterEq.symm
          _ = (a.representationAlphaValue b laterIdx : WithTop ℚ) :=
            (a.coe_representationAlphaValue b laterIdx).symm
          _ ≤ a.truncatedPrefixDefect b 1
              laterIdx.val laterIdx.val := hdefect laterIdx
          _ = diagonalDefect := rfl
      have hendpoint := b.alphaLeftEndpoint_monotone
        (show p ≤ laterAlpha by
          change p.val ≤ laterAlpha.val
          simp only [p, laterAlpha]
          omega)
      have hshift : b.alphaValue p ≤
          coefficient + b.alphaValue laterAlpha := by
        unfold alphaLeftEndpoint at hendpoint
        have hpCast : p.castSucc =
            (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        have hlaterCast : laterAlpha.castSucc =
            (⟨i.val + 1, hi.2⟩ : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        rw [hpCast, hlaterCast] at hendpoint
        dsimp only [coefficient]
        push_cast at hendpoint ⊢
        have hgoodQ : (b.order ⟨i.val - 2, by omega⟩ : ℚ) ≤
            b.order ⟨i.val, i.lt_large⟩ := by
          exact_mod_cast hrightGood
        linarith
      calc
        (b.alphaValue p : WithTop ℚ) ≤
            (coefficient : WithTop ℚ) +
              (b.alphaValue laterAlpha : WithTop ℚ) := by
          exact_mod_cast hshift
        _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
          simpa only [add_comm] using
            add_le_add_right hdiag (coefficient : WithTop ℚ)
  have hfirstDom := a.truncatedPrefixDefect_domination b b
    1 (-1) (i.val + 2) (i.val + 2) i.val
  have hfirst : min diagonalDefect rightDefect ≤ middleDefect := by
    dsimp only [diagonalDefect, rightDefect, middleDefect]
    rw [← b.truncatedPrefixDefect_comm b (-1) (i.val + 2) i.val]
    simpa only [one_mul] using hfirstDom
  have hsecondDom := a.truncatedPrefixDefect_domination b b
    (-1) (-1) (i.val + 2) i.val (i.val - 2)
  have hsecond : min middleDefect leftDefect ≤ crossDefect := by
    dsimp only [middleDefect, leftDefect, crossDefect]
    rw [← b.truncatedPrefixDefect_comm b (-1) i.val (i.val - 2)]
    simpa only [neg_mul, one_mul, neg_neg] using hsecondDom
  have hnested : min (min diagonalDefect rightDefect)
      leftDefect ≤ crossDefect :=
    (min_le_min_right leftDefect hfirst).trans hsecond
  have hminimum : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) +
        min (min diagonalDefect rightDefect) leftDefect :=
    withTop_le_shift_add_min _ coefficient _ _
      (withTop_le_shift_add_min _ coefficient _ _
        hdiagonalBound hrightBound) hleftBound
  have hcrossBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hnested (coefficient : WithTop ℚ))
  unfold representationSecondaryDefect
  rw [hpairsum]
  simpa only [coefficient, crossDefect, p] using hcrossBound

end BONG.GoodBONG

end Bong
