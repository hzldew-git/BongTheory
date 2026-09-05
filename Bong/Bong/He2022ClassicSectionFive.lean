/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicTheorem41
import Bong.Bong.HeHu2022SectionFive

/-!
# He (2024), Section 5: odd-rank classic universality conditions

The paper rank is the odd integer `n`.  The definitions below preserve the
printed conditions `J1_O(n)`, `J2_O(n)`, and `J3_O(n)` with one-based paper
indices translated to zero-based `Fin` indices.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- He (2024), Theorem 5.1, condition `J1_O(n)`. -/
noncomputable def HeClassicJ1O {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat)
    (_hn : 3 <= n) (_hm : n + 2 <= m) : Prop :=
  (forall i : Fin n, a.order ⟨i.val, by omega⟩ = 0) ∧
    a.alphaValue ⟨n - 1, by omega⟩ = 1 ∧
      (((a.order ⟨n, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ ((n + 1) / 2)) 0
            (n + 1) = 1

/-- He (2024), equation (5.1), using the shared parity-normalized formula
already proved for the same BONG orders in the He--Hu development. -/
noncomputable def heClassicOddThreshold {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat) (hm : n + 2 <= m) : Int :=
  a.heHuOddThreshold n hm

/-- He (2024), Theorem 5.1, condition `J2_O(n)`. -/
noncomputable def HeClassicJ2O {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat)
    (_hn : 3 <= n) (hm : n + 2 <= m) : Prop :=
  (a.order ⟨n, by omega⟩ = 1 ∨
      1 < a.order ⟨n + 1, by omega⟩) →
    a.alphaValue ⟨n + 1, by omega⟩ <=
      (a.heClassicOddThreshold n hm : ℚ)

/-- He (2024), Theorem 5.1, condition `J3_O(n)`. -/
def HeClassicJ3O {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat)
    (_hn : 3 <= n) (_hm : n + 2 <= m) : Prop :=
  a.order ⟨n + 2, by omega⟩ - a.order ⟨n + 1, by omega⟩ <=
    2 * (ramificationIndex K : Int)

/-- The three printed odd-rank conditions in Theorem 5.1. -/
structure HeClassicOddSectionConditions {m : Nat}
    (a : GoodBONG q L (m + 1)) (n : Nat)
    (hn : 3 <= n) (hm : n + 2 <= m) : Prop where
  j1 : a.HeClassicJ1O n hn hm
  j2 : a.HeClassicJ2O n hn hm
  j3 : a.HeClassicJ3O n hn hm

/-- The identification at the start of the proof of Theorem 5.1:
`J1_O(n)` is exactly `J1_E(n-1)` together with `J2_E(n-1)` under the
standing odd-rank and source-rank hypotheses. -/
theorem heClassicJ1O_iff_j1E_and_j2E {m n : Nat}
    (a : GoodBONG q L (m + 1)) (hn : 3 <= n) (_hnOdd : Odd n)
    (hm : n + 2 <= m) :
    a.HeClassicJ1O n hn hm ↔
      a.HeClassicJ1E (n - 1) (by omega) ∧
        a.HeClassicJ2E (n - 1) (by omega) := by
  unfold HeClassicJ1O HeClassicJ1E HeClassicJ2E
  have hIndex : n - 1 + 1 = n := by omega
  have hLength : n - 1 + 2 = n + 1 := by omega
  have hExponent : (n - 1 + 2) / 2 = (n + 1) / 2 := by omega
  constructor
  · rintro ⟨hOrders, hAlpha, hEquality⟩
    refine ⟨?_, hAlpha, ?_, ?_⟩
    · intro i
      simpa only [Fin.val_cast] using hOrders (Fin.cast hIndex i)
    · simpa only [hIndex, hLength, hExponent] using hEquality
    · intro hBinary
      omega
  · rintro ⟨hOrders, hAlpha, hEquality, _hBinary⟩
    refine ⟨?_, hAlpha, ?_⟩
    · intro i
      simpa only [Fin.val_cast] using hOrders (Fin.cast hIndex.symm i)
    · simpa only [hIndex, hLength, hExponent] using hEquality

/-- A nonnegative boundary order with alpha invariant one is zero or one.
This is the exact use of Proposition 2.3(iii) in Lemma 5.3. -/
theorem heClassicBoundaryOrder_zeroOrOne_of_alphaOne
    {m n : Nat} (a : GoodBONG q L (m + 2))
    (hn : 1 <= n) (hm : n <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hCurrent : a.order ⟨n - 1, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1) :
    a.order ⟨n, by omega⟩ = 0 ∨ a.order ⟨n, by omega⟩ = 1 := by
  let gap : Fin (m + 1) := ⟨n - 1, by omega⟩
  have hGapEq : a.orderGap gap = a.order ⟨n, by omega⟩ := by
    unfold orderGap
    have hleft : gap.castSucc =
        (⟨n - 1, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
    have hright : gap.succ = (⟨n, by omega⟩ : Fin (m + 2)) := by
      apply Fin.ext
      simp only [gap, Fin.val_succ]
      omega
    rw [hleft, hright, hCurrent]
    omega
  have hNonnegative : 0 <= a.order ⟨n, by omega⟩ := by
    have hsum := (a.he2022ClassicProposition24 hClassic).adjacentOrderSum gap
    unfold adjacentOrderSum at hsum
    have hleft : gap.castSucc =
        (⟨n - 1, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
    have hright : gap.succ = (⟨n, by omega⟩ : Fin (m + 2)) := by
      apply Fin.ext
      simp only [gap, Fin.val_succ]
      omega
    rw [hleft, hright, hCurrent, zero_add] at hsum
    exact hsum
  have hCases := (a.he2022ClassicProposition23 gap).alphaOne.mp (by
    simpa only [gap] using hAlpha)
  unfold HeClassicAlphaOneCases at hCases
  rw [hGapEq] at hCases
  rcases hCases with (hEndpoint | hOne) | hInterior
  · left
    have hePositive := ramificationIndex_pos (K := K)
    omega
  · exact Or.inr hOne
  · left
    omega

/-- He (2024), Lemma 5.3.  The published proof uses `R_n=0` when invoking
Proposition 2.3(iii); this premise comes from `J1_E(n-1)` in every
application but is omitted from the printed lemma statement, so it is made
explicit here. -/
theorem he2022ClassicLemma53 {m n : Nat}
    (a : GoodBONG q L (m + 2)) (hn : 3 <= n) (hnOdd : Odd n)
    (hm : n + 2 <= m + 1) (hClassic : Lattice.IsClassicIntegral q L)
    (hRn : a.order ⟨n - 1, by omega⟩ = 0)
    (hAlpha : a.alphaValue ⟨n - 1, by omega⟩ = 1)
    (hJ2 : a.HeClassicJ2O n hn hm) :
    (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ <=
        2 * (ramificationIndex K : Int) - 1) ∧
      ((a.order ⟨n, by omega⟩ = 1 ∨
          1 < a.order ⟨n + 1, by omega⟩) →
        a.order ⟨n + 2, by omega⟩ -
            a.order ⟨n + 1, by omega⟩ <=
          2 * (ramificationIndex K : Int) - 1) := by
  have hRn1 := a.heClassicBoundaryOrder_zeroOrOne_of_alphaOne
    (n := n) (by omega) (by omega) hClassic hRn hAlpha
  have hFirst : a.order ⟨n + 1, by omega⟩ -
      a.order ⟨n, by omega⟩ <=
        2 * (ramificationIndex K : Int) - 1 := by
    by_contra hnot
    have hLarge : 2 * (ramificationIndex K : Int) <=
        a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩ := by
      omega
    have hTrigger : a.order ⟨n, by omega⟩ = 1 ∨
        1 < a.order ⟨n + 1, by omega⟩ := by
      rcases hRn1 with hzero | hone
      · right
        rw [hzero] at hLarge
        have hePositive := ramificationIndex_pos (K := K)
        omega
      · exact Or.inl hone
    have hBound := hJ2 hTrigger
    have hNegative : a.heClassicOddThreshold n hm < 0 := by
      exact a.heHuOddThreshold_lt_zero_of_two_e_le_gap hm hLarge
    have hNegativeQ : (a.heClassicOddThreshold n hm : ℚ) < 0 := by
      exact_mod_cast hNegative
    have hNonnegative := a.zero_le_alphaValue ⟨n + 1, by omega⟩
    exact (not_lt_of_ge hNonnegative) (hBound.trans_lt hNegativeQ)
  refine ⟨hFirst, ?_⟩
  intro hTrigger
  have hRn2GeOne : 1 <= a.order ⟨n + 1, by omega⟩ := by
    rcases hTrigger with hone | hgt
    · exact a.heHu2022Remark52_order_ge_one hn hnOdd hm
        hClassic.isIntegral hone
    · omega
  have hGapNonnegative : 0 <= a.order ⟨n + 1, by omega⟩ -
      a.order ⟨n, by omega⟩ := by
    rcases hRn1 with hzero | hone <;> omega
  have hThresholdBound : a.heClassicOddThreshold n hm <=
      2 * (ramificationIndex K : Int) - 1 := by
    by_cases hEven : Even
        (a.order ⟨n + 1, by omega⟩ - a.order ⟨n, by omega⟩)
    · simp only [heClassicOddThreshold, heHuOddThreshold, hEven, if_pos]
      omega
    · have hGapNe : a.order ⟨n + 1, by omega⟩ -
          a.order ⟨n, by omega⟩ ≠ 0 := by
        intro hzero
        apply hEven
        rw [hzero]
        exact Even.zero
      simp only [heClassicOddThreshold, heHuOddThreshold, hEven]
      omega
  have hAlphaBound : a.alphaValue ⟨n + 1, by omega⟩ <=
      2 * (ramificationIndex K : ℚ) - 1 := by
    have h := hJ2 hTrigger
    have hcast : (a.heClassicOddThreshold n hm : ℚ) <=
        2 * (ramificationIndex K : ℚ) - 1 := by
      exact_mod_cast hThresholdBound
    exact h.trans hcast
  let lastGap : Fin (m + 1) := ⟨n + 1, by omega⟩
  have hAlphaLtTwoE : a.alphaValue lastGap <
      2 * (ramificationIndex K : ℚ) := by
    have hbound : a.alphaValue lastGap <=
        2 * (ramificationIndex K : ℚ) - 1 := by
      simpa only [lastGap] using hAlphaBound
    linarith
  have hGapLt :=
    ((a.he2022ClassicProposition22).compareTwoE lastGap).2.2.mp
      hAlphaLtTwoE
  unfold orderGap at hGapLt
  have hleft : lastGap.castSucc =
      (⟨n + 1, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
  have hright : lastGap.succ =
      (⟨n + 2, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
  rw [hleft, hright] at hGapLt
  omega

end BONG.GoodBONG

end Bong
