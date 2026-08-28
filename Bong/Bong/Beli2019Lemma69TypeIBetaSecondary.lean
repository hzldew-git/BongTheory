/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaPrimary

/-!
# Beli (2019), Lemma 6.9(ii): type-I beta secondary candidate

For a noninitial odd boundary in the central type-I interval, four capped
defects form the two domination cuts leading to the secondary mixed defect.
The diagonal input is the preceding odd-boundary beta equality.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

set_option maxHeartbeats 4000000 in
-- Two nested domination cuts carry six dependent prefix indices.
/-- The target alpha is below the secondary candidate at every noninitial
odd central type-I boundary. -/
theorem lemma69_typeI_beta_le_secondary_of_earlier
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiThree : 2 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 2)
    (hright : i.val - 1 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩)
    (hearlier : a.representationAlpha b
        (⟨i.val - 2, by omega, by
          have hi := i.lt_large
          omega, by
          have hi := i.lt_large
          omega⟩ : RepresentationIndex (n + 2) (n + 2)) =
      (b.alphaValue ⟨i.val - 3, by
        have hi := i.lt_large
        omega⟩ : WithTop ℚ)) :
    (b.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationSecondaryDefect b i (by
        constructor
        · omega
        · rcases hodd with ⟨d, hd⟩
          rcases C.right_even with ⟨e, he⟩
          have hr := C.right_le_last
          have hb := D.profile.lastDifference.bound
          omega) := by
  have hiNext : i.val + 1 < n + 2 := by
    rcases hodd with ⟨d, hd⟩
    rcases C.right_even with ⟨e, he⟩
    have hr := C.right_le_last
    have hb := D.profile.lastDifference.bound
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  have hiEarlier : i.val - 2 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiEarlierAlpha : i.val - 3 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  let previousTwo : Fin (n + 1) := ⟨i.val - 3, hiEarlierAlpha⟩
  let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 2, by omega, hiEarlier, by
      have hi := i.lt_large
      omega⟩
  rcases hodd with ⟨d, hd⟩
  have hpEven : Even p.val := ⟨d, by simp only [p]; omega⟩
  have hcurrentOdd : Odd i.val := ⟨d, hd⟩
  have hearlierOdd : Odd (i.val - 2) := ⟨d - 1, by omega⟩
  have hfarEven : Even (i.val + 1) := ⟨d + 1, by omega⟩
  have hfarRight : i.val + 1 ≤ C.rightSwitch := by
    rcases C.right_even with ⟨e, he⟩
    omega
  have hcurrentGap := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst i.val hcurrentOdd (by omega) (by omega)
  have hearlierGap := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val - 2) hearlierOdd hleft (by omega)
  have hpreviousGap := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst p.val hpEven (by
      simp only [p]
      omega) (by
        simp only [p]
        omega)
  have hfarGap := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst (i.val + 1) hfarEven (by omega) hfarRight
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hbetaSource : b.alphaValue p = a.alphaValue p - 2 := by
    unfold alphaLeftEndpoint at hweight
    change (a.order p.castSucc : ℚ) + a.alphaValue p =
      (b.order p.castSucc : ℚ) + b.alphaValue p at hweight
    have htargetP : b.order p.castSucc = a.order p.castSucc + 2 := by
      rw [hpCast]
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← a.orderSequence_entryOrZero_eq_order]
      simpa only [p] using hpreviousGap
    rw [htargetP] at hweight
    push_cast at hweight ⊢
    linarith
  have hbetaLeSource : (b.alphaValue p : WithTop ℚ) ≤
      (a.alphaValue p : WithTop ℚ) := by
    exact_mod_cast (show b.alphaValue p ≤ a.alphaValue p by
      linarith [hbetaSource])
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
  have hleftBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + leftDefect :=
    hbetaLeSource.trans hleftAlpha
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
  have hrightBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + rightDefect :=
    hbetaLeSource.trans hrightAlpha
  have hearlier' : a.representationAlpha b earlierIdx =
      (b.alphaValue previousTwo : WithTop ℚ) := by
    simpa only [earlierIdx, previousTwo] using hearlier
  have hdiagonal : (b.alphaValue previousTwo : WithTop ℚ) ≤
      diagonalDefect := by
    calc
      (b.alphaValue previousTwo : WithTop ℚ) =
          a.representationAlpha b earlierIdx := hearlier'.symm
      _ = (a.representationAlphaValue b earlierIdx : WithTop ℚ) :=
        (a.coe_representationAlphaValue b earlierIdx).symm
      _ ≤ a.truncatedPrefixDefect b 1 earlierIdx.val earlierIdx.val :=
        hdefect earlierIdx
      _ = diagonalDefect := rfl
  have htargetEndpoint := b.alphaRightEndpoint_antitone
    (show previousTwo ≤ p by
      change previousTwo.val ≤ p.val
      simp only [previousTwo, p]
      omega)
  have hpreviousTwoSucc : previousTwo.succ =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previousTwo, Fin.val_succ]
    omega
  have htargetShift :
      ((b.order p.succ - b.order previousTwo.succ : Int) : ℚ) ≤
        coefficient := by
    rw [hpSucc, hpreviousTwoSucc]
    have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
        a.order ⟨i.val, i.lt_large⟩ - 2 := by
      rw [← b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩,
        ← a.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩]
      have hgap : b.orderSequence.entryOrZero i.val =
          a.orderSequence.entryOrZero i.val - 2 := by
        omega
      simpa only using hgap
    have hearlierOrder : b.order ⟨i.val - 2, hiEarlier⟩ =
        a.order ⟨i.val - 2, hiEarlier⟩ - 2 := by
      rw [← b.orderSequence_entryOrZero_eq_order
          ⟨i.val - 2, hiEarlier⟩,
        ← a.orderSequence_entryOrZero_eq_order
          ⟨i.val - 2, hiEarlier⟩]
      have hgap : b.orderSequence.entryOrZero (i.val - 2) =
          a.orderSequence.entryOrZero (i.val - 2) - 2 := by
        omega
      simpa only using hgap
    rw [hcurrentOrder, hearlierOrder]
    dsimp only [coefficient]
    push_cast
    have hgoodQ : (a.order ⟨i.val - 1, by omega⟩ : ℚ) ≤
        a.order ⟨i.val + 1, hiNext⟩ := by
      exact_mod_cast hleftGood
    linarith
  have htargetRecurrence : b.alphaValue p ≤
      coefficient + b.alphaValue previousTwo := by
    unfold alphaRightEndpoint at htargetEndpoint
    have hshiftQ := htargetShift
    push_cast at hshiftQ
    linarith
  have hdiagonalBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + diagonalDefect := by
    calc
      (b.alphaValue p : WithTop ℚ) ≤
          (coefficient : WithTop ℚ) +
            (b.alphaValue previousTwo : WithTop ℚ) := by
        exact_mod_cast htargetRecurrence
      _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
        simpa only [add_comm] using
          add_le_add_right hdiagonal (coefficient : WithTop ℚ)
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
  have hminimum : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + min rightDefect
        (min leftDefect diagonalDefect) :=
    withTop_le_shift_add_min _ coefficient _ _ hrightBound
      (withTop_le_shift_add_min _ coefficient _ _
        hleftBound hdiagonalBound)
  have hcrossBound : (b.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hnested (coefficient : WithTop ℚ))
  have htargetEarlier : b.order ⟨i.val - 2, by omega⟩ =
      a.order ⟨i.val - 2, by omega⟩ - 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order
        ⟨i.val - 2, hiEarlier⟩,
      ← a.orderSequence_entryOrZero_eq_order
        ⟨i.val - 2, hiEarlier⟩]
    have hgap : b.orderSequence.entryOrZero (i.val - 2) =
        a.orderSequence.entryOrZero (i.val - 2) - 2 := by
      omega
    simpa only using hgap
  have htargetPrevious : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order
        ⟨i.val - 1, by omega⟩,
      ← a.orderSequence_entryOrZero_eq_order
        ⟨i.val - 1, by omega⟩]
    simpa only [p] using hpreviousGap
  unfold representationSecondaryDefect
  rw [htargetEarlier, htargetPrevious]
  have hcoefficientEq :
      a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ -
            (a.order ⟨i.val - 2, by omega⟩ - 2) -
            (a.order ⟨i.val - 1, by omega⟩ + 2) =
        a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ -
            a.order ⟨i.val - 2, by omega⟩ -
            a.order ⟨i.val - 1, by omega⟩ := by
    ring
  rw [hcoefficientEq]
  simpa only [coefficient, crossDefect, p] using hcrossBound

end BONG.GoodBONG

end Bong
