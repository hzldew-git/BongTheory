/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenEndpointExclusion

/-!
# The second-column terminal orders in He (2025), Lemma 6.8

These internal lemmas separate the order argument from the construction of
actual maximal tests. A central alpha alternative is an explicit intermediate
premise here; it must be discharged in any paper-numbered ADC endpoint.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The central alternatives exclude a raised terminal order in an exceptional second column. -/
theorem heADCSecondEndpoint_terminal_lt (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hIntegral : Lattice.IsIntegral q L) (c : Kˣ)
    (hc : c = 1 ∨ c = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hd : HeHuEvenSecondDefined (k + 1) c)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c hd)))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hnext : a.order ⟨2 * k + 2, by omega⟩ ≤ 2)
    (hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)))
    (hAlpha : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩ →
      a.HeADCEvenCentralAlphaAlternatives k) :
    a.order ⟨2 * k + 3, by omega⟩ < 2 - 2 * (ramificationIndex K : Int) := by
  by_contra hnot
  have hR := le_of_not_gt hnot
  have hheadPair : ∀ t : Fin (k + 1),
      a.order ⟨2 * t.val, by omega⟩ = 0 ∧
        a.order ⟨2 * t.val + 1, by omega⟩ = -(2 * (ramificationIndex K : Int)) := by
    intro t
    constructor
    · simpa only [if_pos (show Even (2 * t.val) from ⟨t.val, by omega⟩)] using
        hhead ⟨2 * t.val, by omega⟩
    · simpa only [if_neg (Nat.not_even_two_mul_add_one t.val)] using
        hhead ⟨2 * t.val + 1, by omega⟩
  let current : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  rcases hAlpha hR with hzero | ⟨_, hraw, hcap⟩
  · have hgap := (a.heADC2025Proposition34 current).alphaZero.mp hzero
    change a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ = _ at hgap
    have hnextTwo : a.order ⟨2 * k + 2, by omega⟩ = 2 := by omega
    have hlast : a.order ⟨2 * k + 3, by omega⟩ =
        2 - 2 * (ramificationIndex K : Int) := by omega
    apply a.heADCSecondEndpoint_not_evenTower (k + 1) c hc hd ambient
    · intro t
      by_cases ht : t.val < k + 1
      · obtain ⟨hleft, hright⟩ := hheadPair ⟨t.val, ht⟩
        rw [hleft, hright, sub_zero]
      · have htEq : t.val = k + 1 := by omega
        simpa only [htEq, Nat.mul_add, Nat.mul_one,
          show 2 * k + 2 + 1 = 2 * k + 3 by omega] using hgap
    · intro t
      by_cases ht : t.val < k + 1
      · rw [(hheadPair ⟨t.val, ht⟩).1]
        exact Even.zero
      · have htEq : t.val = k + 1 := by omega
        have H : a.order ⟨2 * t.val, by omega⟩ = 2 := by
          simpa only [htEq, Nat.mul_add, Nat.mul_one] using hnextTwo
        rw [H]
        exact ⟨1, rfl⟩
  · have hrawEq := hraw.trans hcap
    have hpairLt : a.adjacentDefect current <
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
      rw [hrawEq]
      apply WithTop.coe_lt_coe.mpr
      have hRQ : (2 : ℚ) - 2 * (ramificationIndex K : ℚ) ≤
          (a.order ⟨2 * k + 3, by omega⟩ : ℚ) := by exact_mod_cast hR
      linarith
    have hprefix := a.heADCEvenEndpoint_signedPrefix_defect k (by omega) hIntegral
      (hheadPair ⟨k, by omega⟩).2
    have hfullEq : defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)) =
        a.adjacentDefect current := by
      rw [show k + 2 = (k + 1) + 1 by omega,
        a.toBONG.signedEvenPrefixProduct_succ (k + 1) (by omega)]
      exact defectOrder_mul_eq_right_of_lt_left (hpairLt.trans_le hprefix)
    exact (not_lt_of_ge hfull) (hfullEq.trans_lt hpairLt)

/-- The three possible next orders reduce to the pair `1,1-2e` in the second column. -/
theorem heADCSecondEndpoint_terminal_pair (k : Nat) (a : GoodBONG q L (2 * k + 4))
    (hIntegral : Lattice.IsIntegral q L) (c : Kˣ)
    (hc : c = 1 ∨ c = (dyadicDiscriminantClassLawsProved (K := K)).discriminantUnit)
    (hd : HeHuEvenSecondDefined (k + 1) c)
    (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW2Even (k + 1) c hd)))
    (hhead : ∀ i : Fin (2 * k + 2), a.order ⟨i.val, by omega⟩ =
      if Even i.val then 0 else -(2 * (ramificationIndex K : Int)))
    (hnext : a.order ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 2, by omega⟩ = 1 ∨ a.order ⟨2 * k + 2, by omega⟩ = 2)
    (hfull : ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 2)))
    (hAlpha : 2 - 2 * (ramificationIndex K : Int) ≤ a.order ⟨2 * k + 3, by omega⟩ →
      a.HeADCEvenCentralAlphaAlternatives k) :
    a.order ⟨2 * k + 2, by omega⟩ = 1 ∧
      a.order ⟨2 * k + 3, by omega⟩ = 1 - 2 * (ramificationIndex K : Int) := by
  have hlt := a.heADCSecondEndpoint_terminal_lt k hIntegral c hc hd ambient hhead
    (by omega) hfull hAlpha
  have hne := a.heADCSecondEndpoint_last_ne_neg_twoE (k + 1) hIntegral c hc hd ambient
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
  have hlo := ((a.heHu2022Proposition27i hIntegral).evenIndexed
    ⟨2 * k + 3, by omega⟩ ⟨2 * k + 3, by omega⟩ le_rfl hodd hodd).1
  have hlast : a.order ⟨2 * k + 3, by omega⟩ =
      1 - 2 * (ramificationIndex K : Int) := by
    simp only [Nat.mul_add, Nat.mul_one,
      show 2 * k + 2 + 1 = 2 * k + 3 by omega] at hne
    omega
  refine ⟨?_, hlast⟩
  by_contra hn
  have hbad : a.order ⟨2 * k + 2, by omega⟩ = 0 ∨
      a.order ⟨2 * k + 2, by omega⟩ = 2 := by omega
  let current : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hgapOdd : Odd (a.orderGap current) := by
    change Odd (a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩)
    rcases hbad with hzero | htwo
    · rw [hlast, hzero]
      exact ⟨-(ramificationIndex K : Int), by omega⟩
    · rw [hlast, htwo]
      exact ⟨-(ramificationIndex K : Int) - 1, by omega⟩
  have hpositive := a.heADC2025Corollary32i current hgapOdd
  change 0 < a.order ⟨2 * k + 3, by omega⟩ - a.order ⟨2 * k + 2, by omega⟩ at hpositive
  have he := ramificationIndex_pos (K := K)
  omega

end BONG.GoodBONG

end Bong
