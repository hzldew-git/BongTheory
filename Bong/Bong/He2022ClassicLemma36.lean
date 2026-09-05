/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma35
import Bong.Bong.HeHu2022Lemma211Claim

/-!
# He (2024), Lemma 3.6

This file proves the terminal odd-rank inequality in the published paper.
The paper's odd target rank `n >= 3` is written as `2 * t + 3`; coefficient
orders remain zero based.  Thus the hypotheses `R_(n-1) = R_n = 0` occur at
indices `2 * t + 1` and `2 * t + 2`.
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

/-- He, Lemma 3.6, with an arbitrary source tail beyond the displayed
`n + 1` coefficients. -/
theorem he2022ClassicLemma36LongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  let alphaV : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  let alphaW : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
  let sourceProfile := a.he2022ClassicProposition24 hAClassic
  let targetProfile := b.he2022ClassicProposition24 hBClassic
  let idx : LongRepresentationIndex (m + 3) (2 * t + 2) :=
    { val := 2 * t + 2
      one_lt := by omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  have hiEven : Even idx.val := by
    refine ⟨t + 1, ?_⟩
    simp only [idx]
    omega
  have hLemma35 := a.he2022ClassicLemma35 (m := m + 1)
    (n := 2 * t + 1) b hBClassic idx hiEven
    (by
      have hindex :
          (⟨idx.val - 1, by have := idx.succ_lt_large; omega⟩ :
            Fin (m + 3)) = ⟨2 * t + 1, by omega⟩ := by
        apply Fin.ext
        simp only [idx]
        omega
      rw [hindex]
      exact hRBefore)
    (by simpa only [idx] using hRAt)
    (by
      have hdiv : (idx.val + 2) / 2 = t + 2 := by
        simp only [idx]
        omega
      rw [hdiv]
      convert hSourceEquality using 1)
  let sourceGap : Fin (m + 2) := ⟨2 * t + 1, by omega⟩
  have hSourceZero :
      forall i : Fin (m + 3), i <= sourceGap.succ -> a.order i = 0 := by
    apply sourceProfile.zeroPairForcesPrefixZero sourceGap
    · have hindex : sourceGap.castSucc =
          (⟨2 * t + 1, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRBefore
    · have hindex : sourceGap.succ =
          (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRAt
  have hSourcePrefixZero :
      a.orderSequence.prefixSum (2 * t + 3) = 0 := by
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply hSourceZero ⟨i, by omega⟩
    apply Fin.mk_le_mk.mpr
    change i <= 2 * t + 2
    omega
  have hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))) := by
    rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * t + 3) (by omega), hSourcePrefixZero]
    exact Even.zero
  have hCommonNonnegative :
      (0 : WithTop ℚ) <=
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
    a.truncatedPrefixDefect_nonneg (alphaV := alphaV)
      (alphaW := alphaW) b 1 (2 * t + 3) (2 * t + 3)
  have hCommonOneOfEven
      (heven : Even (ordUnit K
        (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3)))) :
      (1 : WithTop ℚ) <=
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
  rcases hLemma35 with hMixedEquality | hWitness
  · let sourceNext : Fin (m + 3) := ⟨2 * t + 3, by omega⟩
    let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    have hTargetLastEven : Even targetLast.val := by
      refine ⟨t + 1, ?_⟩
      simp only [targetLast]
      omega
    have hTargetLastNonnegative : 0 <= b.order targetLast := by
      have h := targetProfile.oddIndexed 0 targetLast
        (Fin.zero_le targetLast) Even.zero hTargetLastEven
      exact h.1.trans h.2
    have hMixed :
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) =
          ((((1 - a.order sourceNext : Int) : ℚ) : WithTop ℚ)) := by
      simpa only [idx, sourceNext] using hMixedEquality
    by_cases hTargetZero : b.order targetLast = 0
    · have targetParity := targetProfile.zeroAtPaperOdd targetLast
          hTargetLastEven hTargetZero
      have hTargetOrdersEven (k : Nat) (hk : k < 2 * t + 3) :
          Even (b.orderSequence.entryOrZero k) := by
        let kFin : Fin (2 * t + 3) := ⟨k, hk⟩
        rw [b.orderSequence_entryOrZero_eq_order kFin]
        exact targetParity.2 kFin (Fin.mk_le_mk.mpr (by omega))
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
        _ <= a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
          hCommonOneOfEven hProductEven
    · have hTargetOne : 1 <= b.order targetLast := by omega
      calc
        (((a.order ⟨2 * t + 3, by omega⟩ -
              b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) :
              WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) =
            ((((1 - b.order targetLast : Int) : ℚ) : WithTop ℚ)) := by
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
        _ <= 0 := by
          exact_mod_cast (show 1 - b.order targetLast <= 0 by omega)
        _ <= a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) :=
          hCommonNonnegative
  · rcases hWitness with
      ⟨j, hjEven, hjBefore, hSourceLeJ, hBetaBounds⟩
    let sourceNext : Fin (m + 3) := ⟨2 * t + 3, by omega⟩
    let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    let lastGap : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
    have hjLeLast : j <= lastGap := by
      apply Fin.mk_le_mk.mpr
      have hjBefore' : j.val + 1 < 2 * t + 2 := by
        simpa only [idx] using hjBefore
      omega
    have hBetaRaw := (hBetaBounds lastGap hjLeLast).1
    have hBetaBound :
        b.alphaValue lastGap <=
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
    have hJEvenAsTarget : Even (j.castSucc.val) := by
      simpa only [Fin.val_castSucc] using hjEven
    have hJOrderNonnegative : 0 <= b.order j.castSucc := by
      have h := targetProfile.oddIndexed 0 j.castSucc
        (Fin.zero_le j.castSucc) Even.zero hJEvenAsTarget
      exact h.1.trans h.2
    have hMixedLeBeta :
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
          (b.alphaValue lastGap : WithTop ℚ) := by
      have hcap := a.truncatedPrefixDefect_le_rightCap b (-1)
        (2 * t + 4) (2 * t + 2)
      rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      convert hcap using 1
      congr 2
    have hClaim :
        (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
            WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) <=
          a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
      have hClaimRaw := a.heHu2022Lemma211BetaClaimLong (m := m + 2)
        t b hm hBClassic.isIntegral j hjEven
        (by simpa only [idx] using hjBefore) hSourcePrefixOrderEven
        (by simpa only [idx, sourceNext] using hSourceLeJ)
        (by simpa only [sourceNext, targetLast, lastGap] using hBetaBound)
        hJOrderNonnegative hCommonNonnegative hCommonOneOfEven
      simpa only [sourceNext, targetLast, lastGap] using hClaimRaw
    calc
      (((a.order ⟨2 * t + 3, by omega⟩ -
            b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
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
      _ <= a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := hClaim

/-- The final sentence of He, Lemma 3.6: the displayed inequality implies
Theorem 2.5(ii) at the terminal paper index `n = 2 * t + 3`. -/
theorem he2022ClassicLemma36DefectConditionLongSource {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 <= m + 3)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : RepresentationIndex (m + 3) (2 * t + 3) :=
      { val := 2 * t + 3
        pos := by omega
        lt_large := by omega
        le_small := by omega }
    (a.representationAlphaValue b i : WithTop ℚ) <=
      a.truncatedPrefixDefect b 1 i.val i.val := by
  dsimp only
  let i : RepresentationIndex (m + 3) (2 * t + 3) :=
    { val := 2 * t + 3
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hInequality := a.he2022ClassicLemma36LongSource t b hm
    hAClassic hBClassic hRBefore hRAt hAlpha hSourceEquality
  rw [a.coe_representationAlphaValue b i]
  apply (a.representationAlpha_le_primary b i).trans
  unfold representationPrimaryDefect
  have hplus : 2 * t + 3 + 1 = 2 * t + 4 := by omega
  have hminus : 2 * t + 3 - 1 = 2 * t + 2 := by omega
  simpa only [i, hplus, hminus] using hInequality

/-- Exact-rank specialization of He, Lemma 3.6. -/
theorem he2022ClassicLemma36 (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (2 * t + 4) (2 * t + 2) <=
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  exact a.he2022ClassicLemma36LongSource (m := 2 * t + 1) t b (by omega)
    hAClassic hBClassic hRBefore hRAt hAlpha hSourceEquality

/-- Exact-rank specialization of the terminal defect condition. -/
theorem he2022ClassicLemma36DefectCondition (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hRBefore : a.order ⟨2 * t + 1, by omega⟩ = 0)
    (hRAt : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let i : RepresentationIndex (2 * t + 4) (2 * t + 3) :=
      { val := 2 * t + 3
        pos := by omega
        lt_large := by omega
        le_small := by omega }
    (a.representationAlphaValue b i : WithTop ℚ) <=
      a.truncatedPrefixDefect b 1 i.val i.val := by
  exact a.he2022ClassicLemma36DefectConditionLongSource
    (m := 2 * t + 1) t b (by omega) hAClassic hBClassic
      hRBefore hRAt hAlpha hSourceEquality

end BONG.GoodBONG

end Bong
