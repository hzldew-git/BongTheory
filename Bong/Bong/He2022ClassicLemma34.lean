/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma33
import Bong.Bong.Beli2019CappedDominationOrderBound
import Bong.Bong.Beli2019CappedDefectTriangle
import Bong.Bong.Beli2019Lemma79DefectOneCap

/-!
# He (2024), Lemma 3.4

This file proves the even-index defect condition under the source zero-pair,
source-alpha-one, and ramification/alternating-prefix hypothesis of the
published lemma.  Paper indices are one based; BONG coefficient arrays are
zero based.

The publisher proof says near the end of its `e > 1` branch that `j + 2` is
odd.  Since `j` is even this is a typographical error.  The needed conclusion
`0 <= R_(j+2)` follows instead from good-BONG two-step monotonicity and
`R_j = 0`; this is the route used below.
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

/-- He, Lemma 3.4.  At a paper-even index `j`, the zero source pair and
`alpha_j = 1`, together with the published ramification hypothesis, imply
Theorem 2.5(ii) at `j`. -/
theorem he2022ClassicLemma34 {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (j : RepresentationIndex (m + 2) (n + 2))
    (hjEven : Even j.val)
    (hjNextTwo : j.val + 1 < m + 2)
    (hRj : a.order ⟨j.val - 1, by omega⟩ = 0)
    (hRjOne : a.order ⟨j.val, j.lt_large⟩ = 0)
    (halphaJ : a.alphaValue ⟨j.val - 1, by omega⟩ = 1)
    (hfield :
      ramificationIndex K = 1 ∨
        (1 < ramificationIndex K ∧
          a.truncatedPrefixDefect a ((-1) ^ ((j.val + 2) / 2))
              0 (j.val + 2) ≤
            ((((1 - a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) :
              WithTop ℚ)))) :
    a.HeClassicDefectConditionAt b j := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  letI : PerfectResidueFieldLaws K := perfectResidueFieldLaws K
  let sourceProfile := a.he2022ClassicProposition24 hAClassic
  let targetProfile := b.he2022ClassicProposition24 hBClassic
  have hjTwo : 2 ≤ j.val := by
    rcases hjEven with ⟨t, ht⟩
    have := j.pos
    omega
  have hjSmall := j.le_small
  let sourceGap : Fin (m + 1) := ⟨j.val - 1, by omega⟩
  let targetPreviousGap : Fin (n + 1) := ⟨j.val - 2, by omega⟩
  have hsourceZero :
      ∀ i : Fin (m + 2), i ≤ sourceGap.succ → a.order i = 0 := by
    apply sourceProfile.zeroPairForcesPrefixZero sourceGap
    · have hindex : sourceGap.castSucc =
          (⟨j.val - 1, by omega⟩ : Fin (m + 2)) := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hRj
    · have hindex : sourceGap.succ = ⟨j.val, j.lt_large⟩ := by
        apply Fin.ext
        simp only [sourceGap, Fin.val_succ]
        omega
      rw [hindex]
      exact hRjOne
  have hsourcePrefixZero : a.orderSequence.prefixSum j.val = 0 := by
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    apply hsourceZero ⟨i, by omega⟩
    change i ≤ sourceGap.succ.val
    simp only [sourceGap, Fin.val_succ]
    omega
  have hRjTwoNonnegative :
      0 ≤ a.order ⟨j.val + 1, hjNextTwo⟩ := by
    have htwo : a.order ⟨j.val - 1, by omega⟩ ≤
        a.order ⟨j.val + 1, hjNextTwo⟩ := by
      have hraw := a.orderSequence.twoStep (j.val - 1) (by omega)
      change a.order ⟨j.val - 1, by omega⟩ ≤
        a.order ⟨j.val - 1 + 2, by omega⟩ at hraw
      have hindex :
          (⟨j.val - 1 + 2, by omega⟩ : Fin (m + 2)) =
            ⟨j.val + 1, hjNextTwo⟩ := by
        apply Fin.ext
        change j.val - 1 + 2 = j.val + 1
        omega
      rw [hindex] at hraw
      exact hraw
    rw [hRj] at htwo
    exact htwo
  have htargetPreviousNonnegative :
      0 ≤ b.order ⟨j.val - 2, by omega⟩ := by
    have hpreviousEven : Even (j.val - 2) := by
      rcases hjEven with ⟨t, ht⟩
      exact ⟨t - 1, by omega⟩
    have hbounds := targetProfile.oddIndexed
      (0 : Fin (n + 2)) ⟨j.val - 2, by omega⟩
      (Fin.zero_le _) Even.zero hpreviousEven
    exact hbounds.1.trans hbounds.2
  let primaryDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)
  by_cases hprimaryEasy : primaryDefect ≤
      ((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  · unfold HeClassicDefectConditionAt
    rw [a.coe_representationAlphaValue b j]
    calc
      a.representationAlpha b j ≤ a.representationPrimaryDefect b j :=
        a.representationAlpha_le_primary b j
      _ ≤ 0 := by
        unfold representationPrimaryDefect
        dsimp only [primaryDefect] at hprimaryEasy
        rw [hRjOne]
        simp only [zero_sub]
        change
          (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                WithTop ℚ) + primaryDefect ≤ 0
        have hneg :
            (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                WithTop ℚ) +
              (((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) :
                WithTop ℚ) = 0 := by
          push_cast
          simp
        calc
          (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                WithTop ℚ) + primaryDefect ≤
              (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                WithTop ℚ) +
                (((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) :
                  WithTop ℚ) := by
            have hsum := add_le_add_left hprimaryEasy
              (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                WithTop ℚ)
            simpa only [primaryDefect, add_comm] using hsum
          _ = 0 := hneg
      _ ≤ a.truncatedPrefixDefect b 1 j.val j.val :=
        a.truncatedPrefixDefect_nonneg
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws) b 1 j.val j.val
  by_cases htwoEEasy :
      2 * (ramificationIndex K : Int) ≤
        b.order ⟨j.val - 1, by omega⟩
  · unfold HeClassicDefectConditionAt
    rw [a.coe_representationAlphaValue b j]
    calc
      a.representationAlpha b j ≤ a.representationHalfGap b j :=
        a.representationAlpha_le_halfGap b j
      _ ≤ 0 := by
        unfold representationHalfGap
        apply WithTop.coe_le_coe.mpr
        rw [hRjOne]
        push_cast
        have htwoEQ :
            2 * (ramificationIndex K : ℚ) ≤
              (b.order ⟨j.val - 1, by omega⟩ : ℚ) := by
          exact_mod_cast htwoEEasy
        linarith
      _ ≤ a.truncatedPrefixDefect b 1 j.val j.val :=
        a.truncatedPrefixDefect_nonneg
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws) b 1 j.val j.val
  have hprimaryStrict :
      ((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) <
        primaryDefect := lt_of_not_ge hprimaryEasy
  have htwoEStrict :
      b.order ⟨j.val - 1, by omega⟩ <
        2 * (ramificationIndex K : Int) := lt_of_not_ge htwoEEasy
  have hprimaryLeTargetCap :
      primaryDefect ≤ b.prefixAlphaCap (j.val - 1) := by
    exact a.truncatedPrefixDefect_le_rightCap b (-1)
      (j.val + 1) (j.val - 1)
  have hprimaryLeBeta : primaryDefect ≤
      (b.alphaValue targetPreviousGap : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hprimaryLeTargetCap
    have hindex :
        (⟨j.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          targetPreviousGap := by
      apply Fin.ext
      change j.val - 1 - 1 = targetPreviousGap.val
      simp only [targetPreviousGap]
      omega
    rw [hindex] at hprimaryLeTargetCap
    exact hprimaryLeTargetCap
  have hlastLower :
      (((((b.order targetPreviousGap.castSucc -
          b.order targetPreviousGap.succ : Int) : ℚ) +
          b.alphaValue targetPreviousGap : ℚ)) : WithTop ℚ) ≤
        b.truncatedPrefixDefect b (-1) targetPreviousGap.val
          (targetPreviousGap.val + 2) := by
    letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
    exact b.order_sub_add_alpha_le_cappedAdjacent targetPreviousGap
  have hlastPositive : (0 : WithTop ℚ) <
      b.truncatedPrefixDefect b (-1) (j.val - 2) j.val := by
    have hprimaryStrictTop :
        (((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) <
          primaryDefect := hprimaryStrict
    have hbetaStrict :
        (((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) <
          (b.alphaValue targetPreviousGap : WithTop ℚ) :=
      hprimaryStrictTop.trans_le hprimaryLeBeta
    have hstrictLower : (0 : WithTop ℚ) <
        (((((b.order targetPreviousGap.castSucc -
          b.order targetPreviousGap.succ : Int) : ℚ) +
          b.alphaValue targetPreviousGap : ℚ)) : WithTop ℚ) := by
      exact_mod_cast (show (0 : ℚ) <
          ((b.order targetPreviousGap.castSucc -
            b.order targetPreviousGap.succ : Int) : ℚ) +
            b.alphaValue targetPreviousGap by
        have hbetaStrictQ :
            (b.order ⟨j.val - 1, by omega⟩ : ℚ) <
              b.alphaValue targetPreviousGap := by
          exact_mod_cast hbetaStrict
        have hleftIndex : targetPreviousGap.castSucc =
            (⟨j.val - 2, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        have hrightIndex : targetPreviousGap.succ =
            (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := by
          apply Fin.ext
          simp only [targetPreviousGap, Fin.val_succ]
          omega
        rw [hleftIndex, hrightIndex]
        push_cast
        have hprevQ : (0 : ℚ) ≤
            (b.order ⟨j.val - 2, by omega⟩ : ℚ) := by
          exact_mod_cast htargetPreviousNonnegative
        linarith)
    exact hstrictLower.trans_le (by
      simpa only [targetPreviousGap,
        show j.val - 2 + 2 = j.val by omega] using hlastLower)
  have htargetCapOne : (1 : WithTop ℚ) ≤ b.prefixAlphaCap j.val := by
    letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
    letI : Beli2009AlphaParityLaws.{u, w} K :=
      beliUniversalAlphaParityLaws
    by_cases hjTargetInternal : j.val < n + 2
    · rw [b.prefixAlphaCap_of_internal j.pos hjTargetInternal]
      let targetCurrentGap : Fin (n + 1) := ⟨j.val - 1, by omega⟩
      have hlastLeCurrentCap :=
        b.truncatedPrefixDefect_le_rightCap b (-1) (j.val - 2) j.val
      rw [b.prefixAlphaCap_of_internal j.pos hjTargetInternal] at hlastLeCurrentCap
      have hbetaNe : b.alphaValue targetCurrentGap ≠ 0 := by
        intro hzero
        have hcapZero :
            (b.alphaValue ⟨j.val - 1, by omega⟩ : WithTop ℚ) = 0 := by
          exact_mod_cast (show
            b.alphaValue ⟨j.val - 1, by omega⟩ = (0 : ℚ) by
              simpa only [targetCurrentGap] using hzero)
        rw [hcapZero] at hlastLeCurrentCap
        exact (not_lt_of_ge hlastLeCurrentCap) hlastPositive
      exact_mod_cast b.one_le_alphaValue_of_ne_zero targetCurrentGap hbetaNe
    · have hjLast : j.val = n + 2 := by omega
      rw [hjLast]
      simp [prefixAlphaCap]
  have hsourceCapOne :
      a.prefixAlphaCap j.val = (1 : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal j.pos j.lt_large]
    have hindex :
        (⟨j.val - 1, by omega⟩ : Fin (m + 1)) = sourceGap := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact_mod_cast (show a.alphaValue sourceGap = (1 : ℚ) by
      simpa only [sourceGap] using halphaJ)
  obtain ⟨pairs, hjPairs⟩ := hjEven
  have hjFormula : j.val = 2 * pairs := by omega
  have hpairsPositive : 0 < pairs := by omega
  let prefixSign : Kˣ := (-1) ^ pairs
  let previousSign : Kˣ := (-1) ^ (pairs - 1)
  have hjDiv : j.val / 2 = pairs := by
    rw [hjFormula]
    omega
  have hjPreviousDiv : (j.val - 2) / 2 = pairs - 1 := by
    rw [hjFormula]
    omega
  have hprefixSignSquare : prefixSign * prefixSign = 1 := by
    dsimp only [prefixSign]
    rw [← pow_add]
    have hsum : pairs + pairs = 2 * pairs := by omega
    rw [hsum, pow_mul]
    norm_num
  have hpreviousSignSquare : previousSign * previousSign = 1 := by
    dsimp only [previousSign]
    rw [← pow_add]
    have hsum : pairs - 1 + (pairs - 1) = 2 * (pairs - 1) := by omega
    rw [hsum, pow_mul]
    norm_num
  have hpreviousMulNeg : previousSign * (-1) = prefixSign := by
    calc
      previousSign * (-1) = (-1 : Kˣ) ^ (pairs - 1) * (-1) := rfl
      _ = (-1 : Kˣ) ^ ((pairs - 1) + 1) :=
        (pow_succ (-1 : Kˣ) (pairs - 1)).symm
      _ = (-1 : Kˣ) ^ pairs := by
        congr 1
        omega
      _ = prefixSign := rfl
  have hprefixSignOrder : ordUnit K prefixSign = 0 := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (-1 : Kˣ) (-1)
      have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
      rw [hmul, hone] at h
      omega
    dsimp only [prefixSign]
    rw [ordUnit_pow, hnegOne]
    simp
  have hsourcePrefixOne : (1 : WithTop ℚ) ≤
      a.truncatedPrefixDefect a prefixSign 0 j.val := by
    have hprefixOrder :
        ordUnit K (a.toBONG.prefixProduct j.val) = 0 := by
      simpa only [GoodBONG.prefixProduct] using
        (a.ordUnit_prefixProduct_eq_orderSequence_prefixSum j.val
          j.lt_large.le).trans hsourcePrefixZero
    have hrawEven : Even (ordUnit K
        (prefixSign * a.prefixProduct 0 * a.prefixProduct j.val)) := by
      simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero, mul_one]
      rw [ordUnit_mul,
        hprefixSignOrder, hprefixOrder, add_zero]
      exact Even.zero
    have hraw : (1 : WithTop ℚ) ≤ defectOrder (K := K)
        (prefixSign * a.prefixProduct 0 * a.prefixProduct j.val) :=
      defectOrder_one_le_of_even _ hrawEven
    unfold truncatedPrefixDefect
    exact le_min hraw (by rw [a.prefixAlphaCap_zero, hsourceCapOne]; simp)
  rcases Int.even_or_odd (b.orderSequence.prefixSum j.val) with
      htargetPrefixEven | htargetPrefixOdd
  · have hcomparisonEven : Even (ordUnit K
        (a.prefixProduct j.val * b.prefixProduct j.val)) := by
      rw [ordUnit_mul,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum j.val
          j.lt_large.le,
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum j.val j.le_small,
        hsourcePrefixZero, zero_add]
      exact htargetPrefixEven
    have hcomparisonRawOne : (1 : WithTop ℚ) ≤ defectOrder (K := K)
        (1 * a.prefixProduct j.val * b.prefixProduct j.val) := by
      simpa only [one_mul] using
        defectOrder_one_le_of_even
          (a.prefixProduct j.val * b.prefixProduct j.val) hcomparisonEven
    have hcomparisonOne : (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 j.val j.val := by
      unfold truncatedPrefixDefect
      exact le_min hcomparisonRawOne
        (le_min (by rw [hsourceCapOne]) htargetCapOne)
    have hAlphaOne : a.representationAlpha b j ≤ (1 : WithTop ℚ) := by
      rcases hfield with heOne | heLarge
      · have htargetCurrentLower :
            -(1 : Int) ≤ b.order ⟨j.val - 1, by omega⟩ := by
          have hcurrentOdd : Odd (j.val - 1) := by
            exact ⟨pairs - 1, by omega⟩
          have hbounds := targetProfile.evenIndexed
            ⟨j.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ le_rfl
            hcurrentOdd hcurrentOdd
          rw [heOne] at hbounds
          exact hbounds.1
        by_cases htargetCurrentNonnegative :
            0 ≤ b.order ⟨j.val - 1, by omega⟩
        · calc
            a.representationAlpha b j ≤ a.representationHalfGap b j :=
              a.representationAlpha_le_halfGap b j
            _ ≤ 1 := by
              unfold representationHalfGap
              apply WithTop.coe_le_coe.mpr
              rw [hRjOne, heOne]
              push_cast
              have hcurrentQ : (0 : ℚ) ≤
                  (b.order ⟨j.val - 1, by omega⟩ : ℚ) := by
                exact_mod_cast htargetCurrentNonnegative
              linarith
        · have htargetCurrentMinusOne :
              b.order ⟨j.val - 1, by omega⟩ = -1 := by omega
          have hadjacent := targetProfile.adjacentOrderSum targetPreviousGap
          have hgap := b.orderGap_ge_neg_two_mul_e targetPreviousGap
          have hleft : targetPreviousGap.castSucc =
              (⟨j.val - 2, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          have hright : targetPreviousGap.succ =
              (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [targetPreviousGap, Fin.val_succ]
            omega
          unfold adjacentOrderSum at hadjacent
          unfold orderGap at hgap
          rw [hleft, hright, htargetCurrentMinusOne] at hadjacent hgap
          rw [heOne] at hgap
          have htargetPreviousOne :
              b.order ⟨j.val - 2, by omega⟩ = 1 := by omega
          have hgapExact : b.orderGap targetPreviousGap =
              -(2 * (ramificationIndex K : Int)) := by
            unfold orderGap
            rw [hleft, hright, htargetCurrentMinusOne,
              htargetPreviousOne, heOne]
            norm_num
          have hbetaZero : b.alphaValue targetPreviousGap = 0 :=
            (b.he2022ClassicProposition23 targetPreviousGap).alphaZero.mpr
              hgapExact
          have hprimaryZero : primaryDefect ≤ 0 := by
            have hzeroTop :
                (b.alphaValue targetPreviousGap : WithTop ℚ) = 0 := by
              exact_mod_cast hbetaZero
            rw [hzeroTop] at hprimaryLeBeta
            exact hprimaryLeBeta
          calc
            a.representationAlpha b j ≤ a.representationPrimaryDefect b j :=
              a.representationAlpha_le_primary b j
            _ ≤ 1 := by
              unfold representationPrimaryDefect
              rw [hRjOne, htargetCurrentMinusOne]
              norm_num
              change (1 : WithTop ℚ) + primaryDefect ≤ 1
              simpa only [add_zero, zero_add, add_comm] using
                add_le_add_left hprimaryZero
                (1 : WithTop ℚ)
      · let fullSign : Kˣ := (-1) ^ (pairs + 1)
        let sourceExtended :=
          a.truncatedPrefixDefect a fullSign 0 (j.val + 2)
        let targetPrevious :=
          b.truncatedPrefixDefect b previousSign 0 (j.val - 2)
        let secondaryMixed :=
          a.truncatedPrefixDefect b 1 (j.val + 2) (j.val - 2)
        let threshold : WithTop ℚ :=
          ((((1 - a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) :
            WithTop ℚ))
        have hfullDiv : (j.val + 2) / 2 = pairs + 1 := by
          rw [hjFormula]
          omega
        have hfullSignSquare : fullSign * fullSign = 1 := by
          dsimp only [fullSign]
          rw [← pow_add]
          have hsum : pairs + 1 + (pairs + 1) = 2 * (pairs + 1) := by
            omega
          rw [hsum, pow_mul]
          norm_num
        have hfullMulPrevious : fullSign * previousSign = 1 := by
          dsimp only [fullSign, previousSign]
          rw [← pow_add]
          have hsum : pairs + 1 + (pairs - 1) = 2 * pairs := by omega
          rw [hsum, pow_mul]
          norm_num
        have hpreviousMulFull : previousSign * fullSign = 1 := by
          rw [mul_comm, hfullMulPrevious]
        have hsourceExtendedBound : sourceExtended ≤ threshold := by
          dsimp only [sourceExtended, threshold, fullSign]
          rw [← hfullDiv]
          exact heLarge.2
        by_cases hprefixNe : sourceExtended ≠ targetPrevious
        · have hmixedLeSource : secondaryMixed ≤ sourceExtended := by
            rcases lt_or_gt_of_ne hprefixNe with hsourceLt | htargetLt
            · have hstrict :
                  a.truncatedPrefixDefect a fullSign (j.val + 2) 0 <
                    a.truncatedPrefixDefect b previousSign 0
                      (j.val - 2) := by
                rw [a.truncatedPrefixDefect_comm a fullSign,
                  a.truncatedPrefixDefect_zero_left_eq_self
                    b previousSign]
                exact hsourceLt
              have hsharp :=
                a.truncatedPrefixDefect_mul_eq_left_of_lt_right
                  a b fullSign previousSign (j.val + 2) 0
                    (j.val - 2) hstrict
              have hmixedEq : secondaryMixed = sourceExtended := by
                dsimp only [secondaryMixed, sourceExtended]
                rw [← hfullMulPrevious]
                exact hsharp.trans
                  (a.truncatedPrefixDefect_comm a fullSign
                    (j.val + 2) 0)
              exact hmixedEq.le
            · have hstrict :
                  b.truncatedPrefixDefect b previousSign (j.val - 2) 0 <
                    b.truncatedPrefixDefect a fullSign 0
                      (j.val + 2) := by
                rw [b.truncatedPrefixDefect_comm b previousSign,
                  b.truncatedPrefixDefect_zero_left_eq_self a fullSign]
                exact htargetLt
              have hsharp :=
                b.truncatedPrefixDefect_mul_eq_left_of_lt_right
                  b a previousSign fullSign (j.val - 2) 0
                    (j.val + 2) hstrict
              have hmixedEq : secondaryMixed = targetPrevious := by
                calc
                  secondaryMixed =
                      b.truncatedPrefixDefect a 1 (j.val - 2)
                        (j.val + 2) := by
                    dsimp only [secondaryMixed]
                    exact a.truncatedPrefixDefect_comm b 1
                      (j.val + 2) (j.val - 2)
                  _ = b.truncatedPrefixDefect a
                        (previousSign * fullSign) (j.val - 2)
                        (j.val + 2) := by rw [hpreviousMulFull]
                  _ = b.truncatedPrefixDefect b previousSign
                        (j.val - 2) 0 := hsharp
                  _ = targetPrevious := by
                    dsimp only [targetPrevious]
                    exact b.truncatedPrefixDefect_comm b previousSign
                      (j.val - 2) 0
              exact hmixedEq.le.trans htargetLt.le
          have hadjacent := targetProfile.adjacentOrderSum targetPreviousGap
          have hleft : targetPreviousGap.castSucc =
              (⟨j.val - 2, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            rfl
          have hright : targetPreviousGap.succ =
              (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [targetPreviousGap, Fin.val_succ]
            omega
          unfold adjacentOrderSum at hadjacent
          rw [hleft, hright] at hadjacent
          have hoffset :
              (((a.order ⟨j.val + 1, hjNextTwo⟩ -
                b.order ⟨j.val - 2, by omega⟩ -
                b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) :
                  WithTop ℚ) ≤
                ((a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) := by
            exact_mod_cast (show
              a.order ⟨j.val + 1, hjNextTwo⟩ -
                  b.order ⟨j.val - 2, by omega⟩ -
                  b.order ⟨j.val - 1, by omega⟩ ≤
                a.order ⟨j.val + 1, hjNextTwo⟩ by omega)
          calc
            a.representationAlpha b j ≤
                a.representationSecondaryDefect b j
                  ⟨by omega, hjNextTwo⟩ :=
              a.representationAlpha_le_secondary b j
                ⟨by omega, hjNextTwo⟩
            _ ≤ ((a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) +
                  sourceExtended := by
              unfold representationSecondaryDefect
              rw [hRjOne, zero_add]
              change
                (((a.order ⟨j.val + 1, hjNextTwo⟩ -
                  b.order ⟨j.val - 2, by omega⟩ -
                  b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) :
                    WithTop ℚ) + secondaryMixed ≤
                  ((a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) +
                    sourceExtended
              exact add_le_add hoffset hmixedLeSource
            _ ≤ ((a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) +
                  threshold := by
              simpa only [add_comm] using
                add_le_add_left hsourceExtendedBound
                  (((a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ) :
                    WithTop ℚ)
            _ = 1 := by
              dsimp only [threshold]
              norm_cast
              ring
        · have hprefixEq : sourceExtended = targetPrevious :=
            Classical.not_not.mp hprefixNe
          have hjThree : 2 < j.val := by
            by_contra hnot
            have hjEqTwo : j.val = 2 := by omega
            have hpairsOne : pairs = 1 := by omega
            have htargetTop : targetPrevious = ⊤ := by
              dsimp only [targetPrevious, previousSign]
              rw [hjEqTwo, hpairsOne]
              norm_num
              exact b.truncatedPrefixDefect_self_one_zero_eq_top
            have hsourceTop : sourceExtended = ⊤ :=
              hprefixEq.trans htargetTop
            rw [hsourceTop] at hsourceExtendedBound
            exact (WithTop.not_top_le_coe
              (((1 - a.order ⟨j.val + 1, hjNextTwo⟩ : Int) : ℚ)))
                hsourceExtendedBound
          have hlengthPositive : 0 < j.val - 2 := by omega
          have hlengthEven : Even (j.val - 2) :=
            ⟨pairs - 1, by omega⟩
          rcases b.exists_even_cappedAdjacent_le_alternatingPrefix
              (j.val - 2) hlengthPositive (by omega) hlengthEven with
            ⟨k, hkEven, hkBefore, hkLocal⟩
          have hkLocalThreshold :
              b.truncatedPrefixDefect b (-1) k.val (k.val + 2) ≤
                threshold := by
            rw [hjPreviousDiv] at hkLocal
            change b.truncatedPrefixDefect b (-1) k.val (k.val + 2) ≤
              targetPrevious at hkLocal
            exact hkLocal.trans (hprefixEq.symm.le.trans
              hsourceExtendedBound)
          have hkLeFinal : k ≤ targetPreviousGap := by
            change k.val ≤ targetPreviousGap.val
            simp only [targetPreviousGap]
            omega
          have hrightEndpoint := b.alphaRightEndpoint_antitone hkLeFinal
          have hkOrderNonnegative : 0 ≤ b.order k.castSucc := by
            have hbounds := targetProfile.oddIndexed
              (0 : Fin (n + 2)) k.castSucc (Fin.zero_le _)
              Even.zero (by simpa only [Fin.val_castSucc] using hkEven)
            exact hbounds.1.trans hbounds.2
          have hkLower :
              (((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
                b.alphaValue k : ℚ)) : WithTop ℚ) ≤
                  b.truncatedPrefixDefect b (-1) k.val (k.val + 2) := by
            letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
            exact b.order_sub_add_alpha_le_cappedAdjacent k
          have hfinalEndpointThreshold :
              ((-(b.order targetPreviousGap.succ : ℚ) +
                b.alphaValue targetPreviousGap : ℚ) : WithTop ℚ) ≤
                  threshold := by
            have hkEndpointThreshold :
                ((-(b.order k.succ : ℚ) + b.alphaValue k : ℚ) :
                    WithTop ℚ) ≤ threshold := by
              have hkRaw :
                  ((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
                    b.alphaValue k : ℚ) : WithTop ℚ) ≤ threshold :=
                hkLower.trans hkLocalThreshold
              have hkOrderQ : (0 : ℚ) ≤ b.order k.castSucc := by
                exact_mod_cast hkOrderNonnegative
              apply hkRaw.trans' 
              exact_mod_cast (show
                -(b.order k.succ : ℚ) + b.alphaValue k ≤
                  ((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
                    b.alphaValue k by
                push_cast
                linarith)
            unfold alphaRightEndpoint at hrightEndpoint
            exact (show
              ((b.alphaRightEndpoint targetPreviousGap : ℚ) : WithTop ℚ) ≤
                (b.alphaRightEndpoint k : WithTop ℚ) by
                  exact_mod_cast hrightEndpoint).trans hkEndpointThreshold
          have hsucc : targetPreviousGap.succ =
              (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [targetPreviousGap, Fin.val_succ]
            omega
          have hprimaryCandidateThreshold :
              (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                  WithTop ℚ) + primaryDefect ≤ threshold := by
            have hprimaryEndpoint :
                (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                    WithTop ℚ) + primaryDefect ≤
                  ((-(b.order targetPreviousGap.succ : ℚ) +
                    b.alphaValue targetPreviousGap : ℚ) : WithTop ℚ) := by
              rw [hsucc]
              change
                (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                    WithTop ℚ) + primaryDefect ≤
                  (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                    WithTop ℚ) +
                    (b.alphaValue targetPreviousGap : WithTop ℚ)
              have hsum := add_le_add_left hprimaryLeBeta
                (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                  WithTop ℚ)
              simpa only [add_comm] using hsum
            exact hprimaryEndpoint.trans hfinalEndpointThreshold
          calc
            a.representationAlpha b j ≤ a.representationPrimaryDefect b j :=
              a.representationAlpha_le_primary b j
            _ ≤ threshold := by
              unfold representationPrimaryDefect
              rw [hRjOne]
              simp only [zero_sub]
              change
                (((-(b.order ⟨j.val - 1, by omega⟩ : Int) : Int) : ℚ) :
                    WithTop ℚ) + primaryDefect ≤ threshold
              exact hprimaryCandidateThreshold
            _ ≤ 1 := by
              dsimp only [threshold]
              exact_mod_cast (show
                (1 - a.order ⟨j.val + 1, hjNextTwo⟩ : Int) ≤ 1 by
                  omega)
    unfold HeClassicDefectConditionAt
    rw [a.coe_representationAlphaValue b j]
    exact hAlphaOne.trans hcomparisonOne
  · have hcomparisonOdd : Odd (ordUnit K
        (a.prefixProduct j.val * b.prefixProduct j.val)) := by
      rw [ordUnit_mul,
        a.ordUnit_prefixProduct_eq_orderSequence_prefixSum j.val
          j.lt_large.le,
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum j.val j.le_small,
        hsourcePrefixZero, zero_add]
      exact htargetPrefixOdd
    have hcomparisonZero :
        a.truncatedPrefixDefect b 1 j.val j.val = 0 :=
      a.truncatedPrefixDefect_eq_zero_of_odd_order
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws) b j.val hcomparisonOdd
    have hsourceReversedOne : (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect a prefixSign j.val 0 := by
      rw [a.truncatedPrefixDefect_comm a prefixSign]
      exact hsourcePrefixOne
    have hcomparisonStrict :
        a.truncatedPrefixDefect b 1 j.val j.val <
          a.truncatedPrefixDefect a (1 * prefixSign) j.val 0 := by
      rw [one_mul, hcomparisonZero]
      exact (show (0 : WithTop ℚ) < 1 by norm_num).trans_le
        hsourceReversedOne
    have htriangle := a.truncatedPrefixDefect_eq_middle_of_lt_composite
      b a 1 prefixSign (by simp) hprefixSignSquare
      j.val j.val 0 hcomparisonStrict
    have htargetFullZero :
        b.truncatedPrefixDefect b prefixSign 0 j.val = 0 := by
      calc
        b.truncatedPrefixDefect b prefixSign 0 j.val =
            b.truncatedPrefixDefect b prefixSign j.val 0 :=
          b.truncatedPrefixDefect_comm b prefixSign 0 j.val
        _ = b.truncatedPrefixDefect a prefixSign j.val 0 :=
          (b.truncatedPrefixDefect_zero_right_eq_self
            a prefixSign j.val).symm
        _ = a.truncatedPrefixDefect b 1 j.val j.val := htriangle.symm
        _ = 0 := hcomparisonZero
    have hdomination := b.truncatedPrefixDefect_domination b b
      previousSign (-1) 0 (j.val - 2) j.val
    have hdomination' :
        min
            (b.truncatedPrefixDefect b previousSign 0 (j.val - 2))
            (b.truncatedPrefixDefect b (-1) (j.val - 2) j.val) ≤ 0 := by
      rw [hpreviousMulNeg, htargetFullZero] at hdomination
      exact hdomination
    have htargetPreviousZero :
        b.truncatedPrefixDefect b previousSign 0 (j.val - 2) = 0 := by
      have hpreviousNonnegative : (0 : WithTop ℚ) ≤
          b.truncatedPrefixDefect b previousSign 0 (j.val - 2) :=
        b.truncatedPrefixDefect_nonneg
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws) b previousSign 0 (j.val - 2)
      by_cases hpreviousLe :
          b.truncatedPrefixDefect b previousSign 0 (j.val - 2) ≤
            b.truncatedPrefixDefect b (-1) (j.val - 2) j.val
      · apply le_antisymm
        · simpa only [min_eq_left hpreviousLe] using hdomination'
        · exact hpreviousNonnegative
      · have hlastNonpositive :
            b.truncatedPrefixDefect b (-1) (j.val - 2) j.val ≤ 0 := by
          simpa only [min_eq_right (le_of_not_ge hpreviousLe)] using
            hdomination'
        exact False.elim ((not_lt_of_ge hlastNonpositive) hlastPositive)
    have hjThree : 2 < j.val := by
      by_contra hnot
      have hjEqTwo : j.val = 2 := by omega
      have htop :
          b.truncatedPrefixDefect b previousSign 0 (j.val - 2) = ⊤ := by
        rw [hjEqTwo]
        norm_num
        dsimp only [previousSign]
        have hpairsOne : pairs = 1 := by omega
        rw [hpairsOne]
        norm_num
        exact b.truncatedPrefixDefect_self_one_zero_eq_top
      rw [htop] at htargetPreviousZero
      exact WithTop.top_ne_coe htargetPreviousZero
    have hlengthPositive : 0 < j.val - 2 := by omega
    have hlengthEven : Even (j.val - 2) := by
      exact ⟨pairs - 1, by omega⟩
    rcases b.exists_even_cappedAdjacent_le_alternatingPrefix
        (j.val - 2) hlengthPositive (by omega) hlengthEven with
      ⟨k, hkEven, hkBefore, hkLocal⟩
    have hkLocalZero :
        b.truncatedPrefixDefect b (-1) k.val (k.val + 2) ≤ 0 := by
      rw [hjPreviousDiv] at hkLocal
      change b.truncatedPrefixDefect b (-1) k.val (k.val + 2) ≤
        b.truncatedPrefixDefect b previousSign 0 (j.val - 2) at hkLocal
      rw [htargetPreviousZero] at hkLocal
      exact hkLocal
    have hkLeFinal : k ≤ targetPreviousGap := by
      change k.val ≤ targetPreviousGap.val
      simp only [targetPreviousGap]
      omega
    have hrightEndpoint := b.alphaRightEndpoint_antitone hkLeFinal
    have hkOrderNonnegative : 0 ≤ b.order k.castSucc := by
      have hbounds := targetProfile.oddIndexed
        (0 : Fin (n + 2)) k.castSucc (Fin.zero_le _)
        Even.zero (by simpa only [Fin.val_castSucc] using hkEven)
      exact hbounds.1.trans hbounds.2
    have hkLower :
        (((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
          b.alphaValue k : ℚ)) : WithTop ℚ) ≤
            b.truncatedPrefixDefect b (-1) k.val (k.val + 2) := by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      exact b.order_sub_add_alpha_le_cappedAdjacent k
    have hfinalEndpointNonpositive :
        -(b.order targetPreviousGap.succ : ℚ) +
            b.alphaValue targetPreviousGap ≤ 0 := by
      have hkEndpointLeLocal :
          -(b.order k.succ : ℚ) + b.alphaValue k ≤ 0 := by
        have hkLowerQ :
            ((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
                b.alphaValue k ≤ 0 := by
          exact_mod_cast hkLower.trans hkLocalZero
        have hkOrderQ : (0 : ℚ) ≤ b.order k.castSucc := by
          exact_mod_cast hkOrderNonnegative
        push_cast at hkLowerQ
        linarith
      unfold alphaRightEndpoint at hrightEndpoint
      exact hrightEndpoint.trans hkEndpointLeLocal
    have hbetaLeCurrent :
        b.alphaValue targetPreviousGap ≤
          (b.order ⟨j.val - 1, by omega⟩ : ℚ) := by
      have hsucc : targetPreviousGap.succ =
          (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [targetPreviousGap, Fin.val_succ]
        omega
      rw [hsucc] at hfinalEndpointNonpositive
      linarith
    have hbetaLeCurrentTop :
        (b.alphaValue targetPreviousGap : WithTop ℚ) ≤
          ((b.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) := by
      exact_mod_cast hbetaLeCurrent
    exact False.elim ((not_lt_of_ge
      (hprimaryLeBeta.trans hbetaLeCurrentTop)) hprimaryStrict)

end BONG.GoodBONG

end Bong
