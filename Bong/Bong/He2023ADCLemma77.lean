/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma77Initial
import Bong.Bong.He2023ADCSectionThree

/-!
# He (2025), Lemma 7.7

This file completes clause (iii).  Its proof follows the paper literally:
all relevant adjacent source gaps are at most `2e`, so the trigger in
Theorem 3.6(iv) is contradictory.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V W : Type u} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Theorem 3.6(iv) is automatic under the hypotheses of He (2025),
Lemma 7.7(iii). -/
theorem heADC2025Lemma77iii (k : Nat)
    (a : GoodBONG q L (((2 * k + 2) + 1) + 2))
    (b : GoodBONG r M ((2 * k + 1) + 2))
    (hInitial : a.HeHuI1E (2 * k + 2) (by omega))
    (hAlpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hTerminalGap : a.order ⟨2 * k + 4, by omega⟩ -
      a.order ⟨2 * k + 3, by omega⟩ ≤
        2 * (ramificationIndex K : Int)) :
    a.LongRepresentationConditions b := by
  unfold LongRepresentationConditions
  intro i htrigger
  have hgapLe :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ -
          a.order ⟨i.val, by
            exact lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large⟩ ≤
        2 * (ramificationIndex K : Int) := by
    by_cases hiEarly : i.val ≤ 2 * k + 1
    · rcases Nat.even_or_odd i.val with hiEven | hiOdd
      · have hcurrent : a.order ⟨i.val, by omega⟩ = 0 := by
          apply hInitial.oddOrder ⟨i.val, by omega⟩
          show Odd (i.val + 1)
          exact hiEven.add_one
        have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ =
            -(2 * (ramificationIndex K : Int)) := by
          rcases hiEven with ⟨t, ht⟩
          have hnextBound : i.val + 1 < 2 * k + 2 := by omega
          apply hInitial.evenOrder ⟨i.val + 1, hnextBound⟩
          show Even (i.val + 1 + 1)
          exact ⟨t + 1, by omega⟩
        rw [hcurrent, hnext]
        have he := ramificationIndex_pos (K := K)
        omega
      · have hcurrent : a.order ⟨i.val, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
          apply hInitial.evenOrder ⟨i.val, by omega⟩
          show Even (i.val + 1)
          exact hiOdd.add_one
        have hnext : a.order ⟨i.val + 1, i.succ_lt_large⟩ = 0 := by
          apply hInitial.oddOrder ⟨i.val + 1, by omega⟩
          rcases hiOdd with ⟨t, ht⟩
          show Odd (i.val + 1 + 1)
          exact ⟨t + 1, by omega⟩
        rw [hcurrent, hnext]
        omega
    · by_cases hiBoundary : i.val = 2 * k + 2
      · have hcurrentIndex :
            (⟨i.val, by
              exact lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large⟩ :
                Fin (((2 * k + 2) + 1) + 2)) =
              ⟨2 * k + 2, by omega⟩ := by
            apply Fin.ext
            exact hiBoundary
        have hnextIndex :
            (⟨i.val + 1, i.succ_lt_large⟩ :
                Fin (((2 * k + 2) + 1) + 2)) =
              ⟨2 * k + 3, by omega⟩ := by
            apply Fin.ext
            exact congrArg (fun t : Nat ↦ t + 1) hiBoundary
        rw [hcurrentIndex, hnextIndex]
        let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
        have hAlphaLe : a.alphaValue boundary ≤ 1 := by
          rcases hAlpha with hzero | hone
          · rw [show boundary = (⟨2 * k + 2, by omega⟩ :
                Fin (2 * k + 4)) by rfl, hzero]
            norm_num
          · rw [show boundary = (⟨2 * k + 2, by omega⟩ :
                Fin (2 * k + 4)) by rfl, hone]
        have heQ : (1 : ℚ) ≤ ramificationIndex K := by
          exact_mod_cast ramificationIndex_pos (K := K)
        have hGapRaw : a.orderGap boundary ≤
            2 * (ramificationIndex K : Int) := by
          apply le_of_not_gt
          intro hgt
          have hAlphaGt :=
            ((a.heADC2025Proposition33 boundary).compareTwoE.1).mp hgt
          linarith
        simpa only [boundary, orderGap, Fin.castSucc_mk, Fin.succ_mk]
          using hGapRaw
      · have hiTerminal : i.val = 2 * k + 3 := by
          have hiUpper := i.succ_lt_large
          omega
        have hcurrentIndex :
            (⟨i.val, by
              exact lt_trans (Nat.lt_succ_self i.val) i.succ_lt_large⟩ :
                Fin (((2 * k + 2) + 1) + 2)) =
              ⟨2 * k + 3, by omega⟩ := by
            apply Fin.ext
            exact hiTerminal
        have hnextIndex :
            (⟨i.val + 1, i.succ_lt_large⟩ :
                Fin (((2 * k + 2) + 1) + 2)) =
              ⟨2 * k + 4, by omega⟩ := by
            apply Fin.ext
            exact congrArg (fun t : Nat ↦ t + 1) hiTerminal
        rw [hcurrentIndex, hnextIndex]
        exact hTerminalGap
  have hcurrentLeTarget :
      a.order ⟨i.val, by omega⟩ ≤
        b.order ⟨i.val - 2, by omega⟩ := by
    have h := htrigger.2.2
    omega
  have htargetLtNext :
      b.order ⟨i.val - 2, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ :=
    htrigger.2.1
  omega

end BONG.GoodBONG

end Bong
