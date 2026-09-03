/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionTwo
import Bong.Bong.HeHu2022Lemma211Parity
import Bong.Bong.HeHu2022Lemma211Claim
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint

/-!
# He--Hu (2024), Lemma 2.11

This file formalizes the terminal odd-rank defect inequality used immediately
before the maximal-lattice classification.  Writing the paper's odd integer
as `n = 2 * t + 3` removes a parity side condition while retaining every
order, alpha, and capped-defect hypothesis of the published statement.
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

/-- He--Hu, Lemma 2.11.  The source has rank `n + 1` and the target rank
`n`, where the paper's odd `n ≥ 3` is represented by `2 * t + 3`. -/
theorem heHu2022Lemma211LongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 ≤ m + 3)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hLocal :
      a.truncatedPrefixDefect a (-1) (2 * t + 2) (2 * t + 4) =
        (((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) ≤
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  let alphaV : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  let alphaW : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
  let idx : LongRepresentationIndex (m + 3) (2 * t + 2) :=
    { val := 2 * t + 2
      one_lt := by omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  let sourceGap : Fin (m + 2) := ⟨2 * t + 2, by omega⟩
  let sourceNext : Fin (m + 3) := ⟨2 * t + 3, by omega⟩
  have hSourceGap : a.orderGap sourceGap = a.order sourceNext := by
    unfold orderGap
    have hleft : sourceGap.castSucc = ⟨2 * t + 2, by omega⟩ := by
      apply Fin.ext
      rfl
    have hright : sourceGap.succ = sourceNext := by
      apply Fin.ext
      rfl
    rw [hleft, hright, hRAt]
    simp
  have hNextGreater :
      -(2 * (ramificationIndex K : Int)) < a.order sourceNext := by
    have hcases := (a.heHu2022Proposition26 sourceGap).alphaOne (by
      simpa only [sourceGap] using hAlpha)
    rw [hSourceGap] at hcases
    have hePositive := ramificationIndex_pos (K := K)
    rcases hcases.1 with hone | heven
    · rw [hone]
      omega
    · omega
  have hLemma210 := a.heHu2022Lemma210iii b hAIntegral hBIntegral idx
    (by refine ⟨t + 1, ?_⟩; simp only [idx]; omega)
    (by
      convert hRBefore using 1
      congr 2)
    (by simpa only [idx] using hRAt)
    (by simpa only [idx, sourceNext] using hNextGreater)
    (by simpa only [idx] using hLocal)
  let sourceLast : Fin (m + 3) := ⟨2 * t + 1, by omega⟩
  have hSourceLastOdd : Odd sourceLast.val := by
    refine ⟨t, ?_⟩
    simp only [sourceLast]
  let sourcePattern := a.heHu2022Proposition27iiiiv hAIntegral sourceLast
    hSourceLastOdd (by simpa only [sourceLast] using hRBefore)
  have hSourceOrdersEven (k : Nat) (hk : k < 2 * t + 3) :
      Even (a.orderSequence.entryOrZero k) := by
    let kFin : Fin (m + 3) := ⟨k, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order kFin]
    by_cases hkFinal : k = 2 * t + 2
    · have hkFinEq : kFin = ⟨2 * t + 2, by omega⟩ := by
        apply Fin.ext
        exact hkFinal
      rw [hkFinEq, hRAt]
      exact Even.zero
    · rcases Nat.even_or_odd k with hkEven | hkOdd
      · let oddIndex : Fin (m + 3) := ⟨k + 1, by omega⟩
        have hoddIndex : Odd oddIndex.val := by
          rcases hkEven with ⟨d, hd⟩
          refine ⟨d, ?_⟩
          simp only [oddIndex]
          omega
        have hoddLe : oddIndex ≤ sourceLast := by
          apply Fin.mk_le_mk.mpr
          rcases hkEven with ⟨d, hd⟩
          omega
        have hpair := sourcePattern.pairOrdersAndDefects oddIndex hoddLe
          hoddIndex
        have hprevious :
            (⟨oddIndex.val - 1, by omega⟩ : Fin (m + 3)) = kFin := by
          apply Fin.ext
          simp only [oddIndex, kFin]
          omega
        rw [← hprevious, hpair.1]
        exact Even.zero
      · have hkLe : kFin ≤ sourceLast := by
          apply Fin.mk_le_mk.mpr
          rcases hkOdd with ⟨d, hd⟩
          omega
        have hpair := sourcePattern.pairOrdersAndDefects kFin hkLe hkOdd
        rw [hpair.2.1]
        refine ⟨-(ramificationIndex K : Int), ?_⟩
        ring
  have hSourcePrefixSumEven :
      Even (a.orderSequence.prefixSum (2 * t + 3)) :=
    a.orderSequence.prefixSum_even_of_entries_even (2 * t + 3)
      hSourceOrdersEven
  have hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))) := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * t + 3) (by omega)]
    exact hSourcePrefixSumEven
  have hCommonNonnegative :
      (0 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
    a.truncatedPrefixDefect_nonneg (alphaV := alphaV)
      (alphaW := alphaW) b 1 (2 * t + 3) (2 * t + 3)
  have hCommonOneOfEven
      (heven : Even (ordUnit K
        (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3)))) :
      (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
    unfold truncatedPrefixDefect
    apply le_min
    · simpa only [one_mul] using
        (defectOrder_one_le_of_even
          (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))
          heven)
    · apply le_min
      · rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
        have hCapAlpha :
            a.alphaValue ⟨2 * t + 3 - 1, by omega⟩ = 1 := by
          convert hAlpha using 1
          congr 2
        rw [hCapAlpha]
        norm_num
      · simp [prefixAlphaCap]
  rcases hLemma210 with hMixedEquality | hWitness
  · let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    have hTargetLastEven : Even targetLast.val := by
      refine ⟨t + 1, ?_⟩
      simp only [targetLast]
      omega
    let targetOrders := b.heHu2022Proposition27i hBIntegral
    have hTargetLastNonnegative : 0 ≤ b.order targetLast := by
      have h := targetOrders.oddIndexed 0 targetLast
        (Fin.zero_le targetLast) Even.zero hTargetLastEven
      exact h.1.trans h.2
    have hMixed :
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) =
          (((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ) := by
      simpa only [idx, sourceNext] using hMixedEquality
    by_cases hTargetZero : b.order targetLast = 0
    · let targetParity := b.heHu2022Proposition27ii hBIntegral targetLast
        hTargetLastEven hTargetZero
      have hTargetOrdersEven (k : Nat) (hk : k < 2 * t + 3) :
          Even (b.orderSequence.entryOrZero k) := by
        let kFin : Fin (2 * t + 3) := ⟨k, hk⟩
        rw [b.orderSequence_entryOrZero_eq_order kFin]
        exact targetParity.precedingOrdersEven kFin
          (Fin.mk_le_mk.mpr (by
            omega))
      have hTargetPrefixOrderEven :
          Even (ordUnit K (b.prefixProduct (2 * t + 3))) := by
        rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (2 * t + 3) (by omega)]
        exact b.orderSequence.prefixSum_even_of_entries_even (2 * t + 3)
          hTargetOrdersEven
      have hProductEven : Even (ordUnit K
          (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))) := by
        rw [ordUnit_mul]
        exact hSourcePrefixOrderEven.add hTargetPrefixOrderEven
      have hCommonOne := hCommonOneOfEven hProductEven
      calc
        (((a.order ⟨2 * t + 3, by omega⟩ -
              b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) =
            1 := by
              rw [hMixed]
              norm_cast
              have hSourceNextEq :
                  (⟨2 * t + 3, by omega⟩ : Fin (m + 3)) =
                    sourceNext := by rfl
              have hTargetLastEq :
                  (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 3)) =
                    targetLast := by rfl
              rw [hSourceNextEq, hTargetLastEq, hTargetZero]
              ring
        _ ≤ a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
          hCommonOne
    · have hTargetOne : 1 ≤ b.order targetLast := by omega
      calc
        (((a.order ⟨2 * t + 3, by omega⟩ -
              b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) =
            (((1 - b.order targetLast : Int) : ℚ) : WithTop ℚ) := by
              rw [hMixed]
              norm_cast
              have hSourceNextEq :
                  (⟨2 * t + 3, by omega⟩ : Fin (m + 3)) =
                    sourceNext := by rfl
              have hTargetLastEq :
                  (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 3)) =
                    targetLast := by rfl
              rw [hSourceNextEq, hTargetLastEq]
              ring
        _ ≤ 0 := by
          exact_mod_cast (show 1 - b.order targetLast ≤ 0 by omega)
        _ ≤ a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
          hCommonNonnegative
  · rcases hWitness with
      ⟨j, hjEven, hjBefore, hSourceLeJ, hBetaBounds⟩
    let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    let lastGap : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
    have hjLeLast : j ≤ lastGap := by
      apply Fin.mk_le_mk.mpr
      have hjBefore' : j.val + 1 < 2 * t + 2 := by
        simpa only [idx] using hjBefore
      omega
    have hBetaRaw := (hBetaBounds lastGap hjLeLast).1
    have hBetaBound :
        b.alphaValue lastGap ≤
          ((b.order targetLast - b.order j.castSucc : Int) : ℚ) +
            ((1 - a.order sourceNext : Int) : ℚ) := by
      have hLastGapSucc : lastGap.succ = targetLast := by
        apply Fin.ext
        rfl
      have hIdxNext :
          (⟨idx.val + 1, by have := idx.succ_lt_large; omega⟩ :
            Fin (m + 3)) = sourceNext := by
        apply Fin.ext
        rfl
      rw [hLastGapSucc, hIdxNext] at hBetaRaw
      exact hBetaRaw
    let targetOrders := b.heHu2022Proposition27i hBIntegral
    have hJEvenAsTarget : Even (j.castSucc.val) := by
      simpa only [Fin.val_castSucc] using hjEven
    have hJOrderNonnegative : 0 ≤ b.order j.castSucc := by
      have h := targetOrders.oddIndexed 0 j.castSucc
        (Fin.zero_le j.castSucc) Even.zero hJEvenAsTarget
      exact h.1.trans h.2
    have hMixedLeBeta :
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) ≤
          (b.alphaValue lastGap : WithTop ℚ) := by
      have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
        (2 * t + 4) (2 * t + 2)
      rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      convert hcap using 1
      congr 2
    have hClaim :
        (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
            WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) ≤
          a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
      have hClaimRaw := a.heHu2022Lemma211BetaClaimLong t b hm hBIntegral j
        hjEven (by simpa only [idx] using hjBefore) hSourcePrefixOrderEven
        (by simpa only [idx, sourceNext] using hSourceLeJ)
        (by simpa only [sourceNext, targetLast, lastGap] using hBetaBound)
        hJOrderNonnegative hCommonNonnegative hCommonOneOfEven
      simpa only [sourceNext, targetLast, lastGap] using hClaimRaw
    calc
      (((a.order ⟨2 * t + 3, by omega⟩ -
            b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) ≤
          (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
            WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) := by
              have hSourceNextEq :
                  (⟨2 * t + 3, by omega⟩ : Fin (m + 3)) =
                    sourceNext := by rfl
              have hTargetLastEq :
                  (⟨2 * t + 2, by omega⟩ : Fin (2 * t + 3)) =
                    targetLast := by rfl
              rw [hSourceNextEq, hTargetLastEq]
              exact add_le_add_right hMixedLeBeta _
      _ ≤ a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := hClaim

/-- Exact-rank specialization retained for downstream users. -/
theorem heHu2022Lemma211 (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hLocal :
      a.truncatedPrefixDefect a (-1) (2 * t + 2) (2 * t + 4) =
        (((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) ≤
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  exact a.heHu2022Lemma211LongSource (m := 2 * t + 1) t b (by omega)
    hAIntegral hBIntegral hRBefore hRAt hAlpha hLocal

end BONG.GoodBONG

end Bong
