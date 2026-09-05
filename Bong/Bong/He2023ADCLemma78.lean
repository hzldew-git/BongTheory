/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma76
import Bong.Bong.HeHu2022Lemma510
import Bong.Bong.Beli2009AlphaLocalizationProof

/-!
# He (2025), Lemma 7.8

The nonterminal indices descend to the even target prefix and use the
boundary form of He--Hu, Lemma 5.10.  At the final index, the source and
target order parities make the current defect zero; Lemma 7.6(v) then
contradicts the strict trigger.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- He (2025), Lemma 7.8: condition (iii) of Theorem 3.6 holds for every
maximal rank-`n` target. -/
theorem heADC2025Lemma78 (k : Nat)
    (a : GoodBONG q L ((2 * k + 2) + 3))
    (b : GoodBONG r M (2 * k + 3))
    (hA : Lattice.IsIntegral q L)
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hTerminalGap : a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩ ≤
        2 * (ramificationIndex K : Int))
    (hAlternative :
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
        (a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
          a.heADCAdjacentCappedDefect ⟨2 * k + 2, by omega⟩ =
            (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) :
              WithTop ℚ) ∧
          Even (a.order ⟨2 * k + 3, by omega⟩) ∧
          2 - 2 * (ramificationIndex K : Int) ≤
            a.order ⟨2 * k + 3, by omega⟩ ∧
          a.order ⟨2 * k + 3, by omega⟩ ≤ 0 ∧
          (a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
            a.order ⟨2 * k + 4, by omega⟩ = 1)))
    (hM : Lattice.IsOMaximal r M) :
    a.CentralRepresentationConditions b := by
  let sourceLaws : Beli2006AlphaLaws.{u, u} K := beliUniversalAlphaLaws
  let targetLaws : Beli2006AlphaLaws.{u, u} K := beliUniversalAlphaLaws
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : Beli2009AlphaLocalizationLaws.{u, u} K :=
    beli2009AlphaLocalizationLaws_proved
  have hI2 : a.HeHuI2E (2 * k + 2) (by omega) := by
    dsimp only [HeHuI2E]
    rcases hAlternative with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr ⟨hone.1, hone.2.1⟩
  apply (a.heHuLemma510_original_iff_prime sourceLaws targetLaws b
    (m := 2 * k + 2) (by omega) hA hM.isIntegral hInitial hI2).mpr
  intro i htrigger
  by_cases hiNonterminal : i.val ≤ 2 * k + 3
  · exact a.heHuLemma510_nonterminal_representation
      (sourceLaws := sourceLaws) (m := 2 * k + 2) b (by omega)
      hA hM.isIntegral hInitial hI2 i hiNonterminal htrigger
  · have hiTerminal : i.val = 2 * k + 4 := by
      have hi := i.le_small_succ
      omega
    let targetLast : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
    let sourceLast : Fin ((2 * k + 2) + 3) := ⟨2 * k + 4, by omega⟩
    have hTargetIndex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * k + 3)) = targetLast := by
      apply Fin.ext
      dsimp only [targetLast]
      omega
    have hSourceIndex :
        (⟨i.val, by have := i.lt_large; omega⟩ :
          Fin ((2 * k + 2) + 3)) = sourceLast := by
      apply Fin.ext
      exact hiTerminal
    have hOrderTrigger : b.order targetLast < a.order sourceLast := by
      have h := htrigger.1
      rw [hTargetIndex, hSourceIndex] at h
      exact h
    let C := b.heADC2025Proposition413 k hM
    have hTargetLastCases : b.order targetLast = 0 ∨ b.order targetLast = 1 := by
      rcases C.penultimate with hstandard | hraised
      · simpa only [targetLast] using (C.standardTail hstandard).1
      · exact Or.inl (by simpa only [targetLast] using (C.raisedTail hraised).1)
    have hTargetLastNonnegative : 0 ≤ b.order targetLast := by
      rcases hTargetLastCases with hzero | hone <;> omega
    rcases hAlternative with hAlphaZero | hAlphaOne
    · let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
      have hBefore : a.order boundary.castSucc = 0 := by
        have h : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
          apply hInitial.oddOrder
            (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3))
          simpa only [Fin.val_mk] using
            (show Odd (2 * k + 3) from ⟨k + 1, by omega⟩)
        have hindex : boundary.castSucc =
            (⟨2 * k + 2, by omega⟩ : Fin ((2 * k + 2) + 3)) := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact h
      have hgap : a.orderGap boundary = a.order ⟨2 * k + 3, by omega⟩ := by
        unfold orderGap
        rw [hBefore]
        simp only [boundary, Fin.succ_mk, sub_zero]
      have hNext := (a.heADC2025Proposition34 boundary).alphaZero.mp (by
        simpa only [boundary] using hAlphaZero)
      rw [hgap] at hNext
      have hLastNonpositive : a.order sourceLast ≤ 0 := by
        have hgap' : a.order sourceLast -
            a.order ⟨2 * k + 3, by omega⟩ ≤
              2 * (ramificationIndex K : Int) := by
          simpa only [sourceLast] using hTerminalGap
        omega
      exact (not_lt_of_ge
        (hLastNonpositive.trans hTargetLastNonnegative) hOrderTrigger).elim
    · rcases hAlphaOne with
        ⟨hAlpha, hAdjacent, hNextEven, hNextLower, _hNextUpper, hLastCases⟩
      have hSourceLast : a.order sourceLast = 1 := by
        rcases hLastCases with hzero | hone
        · rw [show a.order sourceLast = 0 by simpa only [sourceLast] using hzero]
            at hOrderTrigger
          exact (not_lt_of_ge hTargetLastNonnegative hOrderTrigger).elim
        · simpa only [sourceLast] using hone
      have hTargetLast : b.order targetLast = 0 := by
        rcases hTargetLastCases with hzero | hone
        · exact hzero
        · rw [hone, hSourceLast] at hOrderTrigger
          omega
      have hSourceEntries (t : Nat) (ht : t < 2 * k + 3) :
          Even (a.orderSequence.entryOrZero t) := by
        let j : Fin ((2 * k + 2) + 3) := ⟨t, by omega⟩
        rw [a.orderSequence_entryOrZero_eq_order j]
        rcases Nat.even_or_odd t with htEven | htOdd
        · have horder : a.order j = 0 := by
            apply hInitial.oddOrder ⟨t, ht⟩
            simpa only [j, Fin.val_mk] using htEven.add_one
          rw [horder]
          exact Even.zero
        · have htBound : t < 2 * k + 2 := by
            rcases htOdd with ⟨d, hd⟩
            omega
          have horder : a.order j =
              -(2 * (ramificationIndex K : Int)) := by
            apply hInitial.evenOrder ⟨t, htBound⟩
            simpa only [j, Fin.val_mk] using htOdd.add_one
          rw [horder]
          exact ⟨-(ramificationIndex K : Int), by ring⟩
      have hSourceHeadEven : Even
          (a.orderSequence.prefixSum (2 * k + 3)) :=
        a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hSourceEntries
      have hSourceNextEven : Even
          (a.orderSequence.prefixSum (2 * k + 4)) := by
        rw [a.orderSequence.prefixSum_succ,
          a.orderSequence_entryOrZero_eq_order
            (⟨2 * k + 3, by omega⟩ : Fin ((2 * k + 2) + 3))]
        exact hSourceHeadEven.add hNextEven
      have hSourceFullOdd : Odd
          (a.orderSequence.prefixSum (2 * k + 5)) := by
        rw [a.orderSequence.prefixSum_succ,
          a.orderSequence_entryOrZero_eq_order sourceLast, hSourceLast]
        exact hSourceNextEven.add_odd odd_one
      have hTargetLastEven : Even targetLast.val := by
        exact ⟨k + 1, by dsimp only [targetLast]; omega⟩
      let targetParity := b.heHu2022Proposition27ii hM.isIntegral targetLast
        hTargetLastEven hTargetLast
      have hTargetEntries (t : Nat) (ht : t < 2 * k + 3) :
          Even (b.orderSequence.entryOrZero t) := by
        let j : Fin (2 * k + 3) := ⟨t, ht⟩
        rw [b.orderSequence_entryOrZero_eq_order j]
        exact targetParity.precedingOrdersEven j (Fin.mk_le_mk.mpr (by
          omega))
      have hTargetFullEven : Even
          (b.orderSequence.prefixSum (2 * k + 3)) :=
        b.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hTargetEntries
      have hMixedOdd : Odd (ordUnit K
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            b.prefixProduct (2 * k + 3))) := by
        rw [ordUnit_mul, ordUnit_mul, ordUnit_neg_one_eq_zero,
          a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
            (2 * k + 5) (by omega),
          b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
            (2 * k + 3) le_rfl]
        exact (Even.zero.add_odd hSourceFullOdd).add_even hTargetFullEven
      have hCurrentZero : a.centralCurrentDefect b i = 0 := by
        have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
          (alphaV := sourceLaws) (alphaW := targetLaws) b (-1)
          (2 * k + 5) (2 * k + 3) hMixedOdd
        unfold centralCurrentDefect
        rw [hiTerminal]
        convert hzero using 1
        all_goals congr 1
      have hPrevious : a.centralPreviousDefect b i =
          (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) :
            WithTop ℚ) := by
        have h := a.heADC2025Lemma76v k b hInitial hAlpha hAdjacent hM
        unfold centralPreviousDefect
        rw [hiTerminal]
        convert h using 1
        all_goals congr 1
      have hDefectTrigger := htrigger.2
      rw [hTargetIndex, hSourceIndex, hTargetLast, hSourceLast,
        hPrevious, hCurrentZero, add_zero] at hDefectTrigger
      have hStrict :
          ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) <
            (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) :
              WithTop ℚ) := by
        convert hDefectTrigger using 1
        all_goals norm_cast
      have hNextLowerQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hNextLower
      have hUpper :
          (((1 : ℚ) - (a.order ⟨2 * k + 3, by omega⟩ : ℚ) : ℚ) :
              WithTop ℚ) ≤
            ((2 * (ramificationIndex K : ℚ) - 1 : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_le_coe.mpr
        linarith
      exact (not_lt_of_ge hUpper hStrict).elim

end BONG.GoodBONG

end Bong
