/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma37

/-!
# He (2024), Lemma 3.8

This file targets condition (iii) exactly as printed in the publisher
version, hence uses `HeClassicPublishedCentralConditionAt` and its two-defect
trigger.  The paper's even rank `n >= 2` is written as `2 * t + 2`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- He, Lemma 3.8, with an arbitrary source tail beyond `n + 2`. -/
theorem he2022ClassicLemma38LongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 2))
    (hm : 2 * t + 4 <= m + 4)
    (_hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRn : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRnOne : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : CentralRepresentationIndex (m + 4) (2 * t + 2) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  dsimp only
  let i : CentralRepresentationIndex (m + 4) (2 * t + 2) :=
    { val := 2 * t + 3
      one_lt := by omega
      lt_large := by omega
      le_small_succ := by omega }
  unfold HeClassicPublishedCentralConditionAt
  intro htrigger
  exfalso
  let targetLast : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
  let sourceNext : Fin (m + 4) := ⟨2 * t + 3, by omega⟩
  let firstDefect :=
    a.truncatedPrefixDefect b (-1) (2 * t + 3) (2 * t + 1)
  let secondDefect :=
    a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2)
  have hTargetIndex :
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ : Fin (2 * t + 2)) = targetLast := by
    apply Fin.ext
    change 2 * t + 3 - 2 = 2 * t + 1
    omega
  have hSourceIndex :
      (⟨i.val, by exact i.lt_large⟩ : Fin (m + 4)) = sourceNext := by
    apply Fin.ext
    rfl
  have hPreviousDefect :
      a.centralPreviousDefect b i = firstDefect := by
    unfold centralPreviousDefect firstDefect
    congr 2
  have hCurrentDefect :
      a.centralCurrentDefect b i = secondDefect := by
    unfold centralCurrentDefect secondDefect
    congr 2
  have hOrderTrigger : b.order targetLast < a.order sourceNext := by
    have hraw := htrigger.1
    rw [hTargetIndex, hSourceIndex] at hraw
    exact hraw
  have hDefectTrigger :
      ((((2 * (ramificationIndex K : Int) + b.order targetLast -
        a.order sourceNext : Int) : ℚ) : WithTop ℚ)) <
        firstDefect + secondDefect := by
    have hraw := htrigger.2
    rw [hTargetIndex, hSourceIndex, hPreviousDefect,
      hCurrentDefect] at hraw
    norm_cast at hraw ⊢
  let idx : LongRepresentationIndex (m + 4) (2 * t + 1) :=
    { val := 2 * t + 2
      one_lt := by omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  have hiEven : Even idx.val := by
    refine ⟨t + 1, ?_⟩
    simp only [idx]
    omega
  have hLemma35 := a.he2022ClassicLemma35 (m := m + 2) (n := 2 * t)
    b hBClassic idx hiEven
      (by
        have hindex :
            (⟨idx.val - 1, by have := idx.succ_lt_large; omega⟩ :
              Fin (m + 4)) = ⟨2 * t + 1, by omega⟩ := by
          apply Fin.ext
          simp only [idx]
          omega
        rw [hindex]
        exact hRn)
      (by simpa only [idx] using hRnOne)
      (by
        have hdiv : (idx.val + 2) / 2 = t + 2 := by
          simp only [idx]
          omega
        rw [hdiv]
        convert hSourceEquality using 1)
  have hSecondEquality :
      secondDefect =
        ((((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ)) := by
    rcases hLemma35 with hEquality | hWitness
    · simpa only [idx, secondDefect, sourceNext] using hEquality
    · rcases hWitness with
        ⟨j, hjEven, hjBefore, hSourceLeJ, _hBetaBounds⟩
      have hjSuccOdd : Odd j.succ.val := by
        rcases hjEven with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        simp only [Fin.val_succ]
        omega
      have hLastOdd : Odd targetLast.val := by
        refine ⟨t, ?_⟩
        simp only [targetLast]
      have hjLeLast : j.succ <= targetLast := by
        apply Fin.mk_le_mk.mpr
        have hjBefore' : j.val + 1 < 2 * t + 2 := by
          simpa only [idx] using hjBefore
        omega
      have hTargetUpper :=
        (b.he2022ClassicProposition24 hBClassic).evenIndexed
          j.succ targetLast hjLeLast hjSuccOdd hLastOdd
      have hSourceLe : a.order sourceNext <= b.order j.succ := by
        simpa only [idx, sourceNext] using hSourceLeJ
      exact False.elim ((not_le_of_gt hOrderTrigger)
        (hSourceLe.trans hTargetUpper.2))
  have hFirstUpper : firstDefect <= (1 : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b (-1)
      (2 * t + 3) (2 * t + 1)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hindex :
        (⟨2 * t + 3 - 1, by omega⟩ : Fin (m + 3)) =
          ⟨2 * t + 2, by omega⟩ := by
      apply Fin.ext
      change 2 * t + 3 - 1 = 2 * t + 2
      omega
    rw [hindex, hAlpha] at hcap
    simpa [firstDefect] using hcap
  have hSumUpper :
      firstDefect + secondDefect <=
        ((((2 - a.order sourceNext : Int) : ℚ) : WithTop ℚ)) := by
    calc
      firstDefect + secondDefect <= 1 + secondDefect :=
        by simpa [add_comm] using add_le_add_right hFirstUpper secondDefect
      _ = ((((2 - a.order sourceNext : Int) : ℚ) : WithTop ℚ)) := by
        rw [hSecondEquality]
        norm_cast
        ring
  have hTargetTooSmall :
      b.order targetLast < 2 - 2 * (ramificationIndex K : Int) := by
    have hfinite := hDefectTrigger.trans_le hSumUpper
    norm_cast at hfinite
    push_cast at hfinite
    exact_mod_cast (show
      b.order targetLast < 2 - 2 * (ramificationIndex K : Int) by
        linarith)
  have hePositive := ramificationIndex_pos (K := K)
  have hTargetNegative : b.order targetLast < 0 := by omega
  let previous : Fin (2 * t + 2) := ⟨2 * t, by omega⟩
  let lastGap : Fin (2 * t + 1) := ⟨2 * t, by omega⟩
  have hPreviousPositive : 0 < b.order previous := by
    have hsum :=
      (b.he2022ClassicProposition24 hBClassic).adjacentOrderSum lastGap
    have hcast : lastGap.castSucc = previous := by
      apply Fin.ext
      rfl
    have hsucc : lastGap.succ = targetLast := by
      apply Fin.ext
      rfl
    unfold adjacentOrderSum at hsum
    rw [hcast, hsucc] at hsum
    omega
  have hGapLower := b.orderGap_ge_neg_two_mul_e lastGap
  have hGapValue : b.order targetLast - b.order previous =
      -(2 * (ramificationIndex K : Int)) := by
    have hcast : lastGap.castSucc = previous := by
      apply Fin.ext
      rfl
    have hsucc : lastGap.succ = targetLast := by
      apply Fin.ext
      rfl
    unfold orderGap at hGapLower
    rw [hcast, hsucc] at hGapLower
    omega
  have hTargetValue : b.order targetLast =
      1 - 2 * (ramificationIndex K : Int) := by
    omega
  have hBetaZero : b.alphaValue lastGap = 0 := by
    apply (b.he2022ClassicProposition23 lastGap).alphaZero.mpr
    unfold orderGap
    have hcast : lastGap.castSucc = previous := by
      apply Fin.ext
      rfl
    have hsucc : lastGap.succ = targetLast := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc, hGapValue]
  have hFirstZero : firstDefect = 0 := by
    apply le_antisymm
    · have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
        (2 * t + 3) (2 * t + 1)
      rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      have hindex :
          (⟨2 * t + 1 - 1, by omega⟩ : Fin (2 * t + 1)) =
            lastGap := by
        apply Fin.ext
        simp only [lastGap]
        omega
      rw [hindex, hBetaZero] at hcap
      simpa [firstDefect] using hcap
    · exact a.truncatedPrefixDefect_nonneg
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws) b (-1) (2 * t + 3)
          (2 * t + 1)
  rw [hFirstZero, zero_add, hSecondEquality] at hDefectTrigger
  have hFinalStrict : b.order targetLast <
      1 - 2 * (ramificationIndex K : Int) := by
    norm_cast at hDefectTrigger
    push_cast at hDefectTrigger
    exact_mod_cast (show
      b.order targetLast < 1 - 2 * (ramificationIndex K : Int) by
        linarith)
  exact (not_lt_of_ge (le_of_eq hTargetValue.symm)) hFinalStrict

/-- Exact-rank specialization of He, Lemma 3.8. -/
theorem he2022ClassicLemma38 (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRn : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRnOne : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : CentralRepresentationIndex (2 * t + 4) (2 * t + 2) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    a.HeClassicPublishedCentralConditionAt b i := by
  exact a.he2022ClassicLemma38LongSource (m := 2 * t) t b (by omega)
    hAClassic hBClassic hRn hRnOne hAlpha hSourceEquality

end BONG.GoodBONG

end Bong
