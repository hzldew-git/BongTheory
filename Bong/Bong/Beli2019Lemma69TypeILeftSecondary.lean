/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeILeftPrimary
import Bong.Bong.Beli2019Lemma69CappedPropagationRight

/-!
# Beli (2019), Lemma 6.9(ii): type-I left secondary candidate

Two adjacent source defects and the preceding same-parity diagonal defect
dominate Definition 4's secondary mixed defect.  At the first even boundary
the diagonal prefix is empty and hence has defect `top`.
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
-- Two domination cuts transport six prefix indices; the base case also
-- normalizes an empty capped prefix.
/-- The source alpha is below the secondary candidate at every interior even
boundary of the type-I left branch. -/
theorem lemma69_typeI_left_alpha_le_secondary
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 1 < i.val) (hiLeft : i.val ≤ C.leftSwitch)
    (hiEven : Even i.val)
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hearlier : ∀ hthree : 2 < i.val,
      a.representationAlpha b
          (⟨i.val - 2, by omega, by omega, by omega⟩ :
            RepresentationIndex (n + 2) (n + 2)) =
        (a.alphaValue ⟨i.val - 3, by omega⟩ : WithTop ℚ)) :
    (a.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) ≤
      a.representationSecondaryDefect b i hi := by
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hiNext : i.val + 1 < n + 2 := hi.2
  let p : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let previousTwo : Fin (n + 1) := ⟨i.val - 3, by omega⟩
  let previous : Fin (n + 1) := ⟨i.val - 2, by omega⟩
  let next : Fin (n + 1) := ⟨i.val, by omega⟩
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
  have hpCast : p.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have hleftGoodRaw := a.good
    (⟨i.val - 1, by omega⟩ : Fin (n + 2)) (by
      change (i.val - 1) + 2 < n + 2
      omega)
  have hleftGood : a.order ⟨i.val - 1, by omega⟩ ≤
      a.order ⟨i.val + 1, hiNext⟩ := by
    have hindex :
        (⟨(⟨i.val - 1, by omega⟩ : Fin (n + 2)).val + 2, by
          change (i.val - 1) + 2 < n + 2
          omega⟩ : Fin (n + 2)) = ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      simp only
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
        (⟨(⟨i.val - 2, by omega⟩ : Fin (n + 2)).val + 2, by
          change (i.val - 2) + 2 < n + 2
          omega⟩ : Fin (n + 2)) = ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [hindex] at hrightGoodRaw
    exact hrightGoodRaw
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
        a.order ⟨i.val + 1, hiNext⟩ := by exact_mod_cast hleftGood
    linarith
  have hleftBoundCandidate : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + leftDefect := by
    have hshiftTop :
        (((a.order p.succ - a.order previous.castSucc : Int) : ℚ) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hleftShift
    have hraw : (a.alphaValue p : WithTop ℚ) ≤
        (((a.order p.succ - a.order previous.castSucc : Int) : ℚ) :
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
        a.order ⟨i.val, i.lt_large⟩ := by exact_mod_cast hrightGood
    linarith
  have hrightBoundCandidate : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + rightDefect := by
    have hshiftTop :
        (((a.order next.succ - a.order p.castSucc : Int) : ℚ) :
          WithTop ℚ) ≤ coefficient := by
      exact_mod_cast hrightShift
    have hraw : (a.alphaValue p : WithTop ℚ) ≤
        (((a.order next.succ - a.order p.castSucc : Int) : ℚ) :
          WithTop ℚ) + rightDefect := by
      simpa only [next, rightDefect] using hrightRaw
    exact hraw.trans (by
      simpa only [add_comm] using add_le_add_right hshiftTop rightDefect)
  have hdiagonalBound : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + diagonalDefect := by
    by_cases hbase : i.val = 2
    · have htop : diagonalDefect = ⊤ := by
        have hsub : i.val - 2 = 0 := by omega
        dsimp only [diagonalDefect]
        unfold truncatedPrefixDefect
        rw [hsub, a.prefixAlphaCap_zero, b.prefixAlphaCap_zero]
        simp [BONG.GoodBONG.prefixProduct, defectOrder_one]
      rw [htop]
      simp
    · have hthree : 2 < i.val := by
        rcases hiEven with ⟨m, hm⟩
        omega
      let earlierIdx : RepresentationIndex (n + 2) (n + 2) :=
        ⟨i.val - 2, by omega, by omega, by omega⟩
      have hearlierEq : a.representationAlpha b earlierIdx =
          (a.alphaValue previousTwo : WithTop ℚ) := by
        simpa only [earlierIdx, previousTwo] using hearlier hthree
      have hdiag : (a.alphaValue previousTwo : WithTop ℚ) ≤
          diagonalDefect := by
        calc
          (a.alphaValue previousTwo : WithTop ℚ) =
              a.representationAlpha b earlierIdx := hearlierEq.symm
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
            a.order ⟨i.val + 1, hiNext⟩ := by exact_mod_cast hleftGood
        linarith
      calc
        (a.alphaValue p : WithTop ℚ) ≤
            (coefficient : WithTop ℚ) +
              (a.alphaValue previousTwo : WithTop ℚ) := by
          exact_mod_cast hrecurrence
        _ ≤ (coefficient : WithTop ℚ) + diagonalDefect := by
          simpa only [add_comm] using
            add_le_add_right hdiag (coefficient : WithTop ℚ)
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
    withTop_le_shift_add_min _ coefficient _ _ hrightBoundCandidate
      (withTop_le_shift_add_min _ coefficient _ _
        hleftBoundCandidate hdiagonalBound)
  have hcrossBound : (a.alphaValue p : WithTop ℚ) ≤
      (coefficient : WithTop ℚ) + crossDefect :=
    hminimum.trans (by
      simpa only [add_comm] using
        add_le_add_right hnested (coefficient : WithTop ℚ))
  have horders := lemma69_typeI_left_boundary_orders
    a b D C hfirst i.val (by omega) hiLeft hiEven
  have htargetEarlier : b.order ⟨i.val - 2, by omega⟩ =
      a.order ⟨i.val - 2, by omega⟩ + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.1
  have htargetPrevious : b.order ⟨i.val - 1, by omega⟩ =
      a.order ⟨i.val - 1, by omega⟩ - 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact horders.2.2
  unfold representationSecondaryDefect
  rw [htargetEarlier, htargetPrevious]
  have hcoefficientEq :
      a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ -
            (a.order ⟨i.val - 2, by omega⟩ + 1) -
            (a.order ⟨i.val - 1, by omega⟩ - 1) =
        a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ -
            a.order ⟨i.val - 2, by omega⟩ -
            a.order ⟨i.val - 1, by omega⟩ := by
    ring
  rw [hcoefficientEq]
  simpa only [coefficient, crossDefect, p] using hcrossBound

end BONG.GoodBONG

end Bong
