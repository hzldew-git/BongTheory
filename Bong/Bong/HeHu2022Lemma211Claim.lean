/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022Lemma211Exceptional

/-! # He--Hu (2024), Lemma 2.11: terminal beta claim -/

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

/-- The rational cancellation used when the preceding target order is zero. -/
private theorem lemma211_beta_le_one {R S P : Int} {beta : ℚ}
    (hbeta : beta ≤ ((S - P : Int) : ℚ) + ((1 - R : Int) : ℚ))
    (hP : P = 0) : ((R - S : Int) : ℚ) + beta ≤ 1 := by
  push_cast at hbeta ⊢
  rw [hP] at hbeta
  norm_num at hbeta
  linarith

/-- The same cancellation when the preceding target order is positive. -/
private theorem lemma211_beta_le_zero {R S P : Int} {beta : ℚ}
    (hbeta : beta ≤ ((S - P : Int) : ℚ) + ((1 - R : Int) : ℚ))
    (hP : 1 ≤ P) : ((R - S : Int) : ℚ) + beta ≤ 0 := by
  push_cast at hbeta ⊢
  have hPq : (1 : ℚ) ≤ (P : ℚ) := by exact_mod_cast hP
  linarith

/-- Embed a finite rational two-term inequality into `ℚ ∪ {∞}`. -/
private theorem lemma211_withTop_add_le {x y z : ℚ} (h : x + y ≤ z) :
    (x : WithTop ℚ) + (y : WithTop ℚ) ≤ (z : WithTop ℚ) := by
  exact_mod_cast h

set_option maxHeartbeats 600000 in
-- The nested parity split is isolated here to keep the public theorem small.
/-- The intermediate claim
`R_(n+1) - S_n + beta_(n-1) ≤ d[a_(1,n)b_(1,n)]`
from the proof of He--Hu, Lemma 2.11. -/
theorem heHu2022Lemma211BetaClaimLong {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 ≤ m + 1)
    (hBIntegral : Lattice.IsIntegral r M)
    (j : Fin (2 * t + 2))
    (hjEven : Even j.val)
    (hjBefore : j.val + 1 < 2 * t + 2)
    (hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))))
    (hSourceLeJ : a.order ⟨2 * t + 3, by omega⟩ ≤ b.order j.succ)
    (hBetaBound :
      b.alphaValue ⟨2 * t + 1, by omega⟩ ≤
        ((b.order ⟨2 * t + 2, by omega⟩ -
          b.order j.castSucc : Int) : ℚ) +
        ((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ))
    (hJOrderNonnegative : 0 ≤ b.order j.castSucc)
    (hCommonNonnegative :
      (0 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3))
    (hCommonOneOfEven :
      Even (ordUnit K
        (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))) →
      (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3)) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (b.alphaValue ⟨2 * t + 1, by omega⟩ : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  let sourceNext : Fin (m + 1) := ⟨2 * t + 3, by omega⟩
  let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  let lastGap : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
  by_cases hJZero : b.order j.castSucc = 0
  · rcases Int.even_or_odd (ordUnit K
        (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))) with
      hProductEven | hProductOdd
    · have hCommonOne := hCommonOneOfEven hProductEven
      have hQ :
          ((a.order sourceNext - b.order targetLast : Int) : ℚ) +
              b.alphaValue lastGap ≤ 1 :=
        lemma211_beta_le_one hBetaBound hJZero
      have hQTop :
          (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
              WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) ≤ 1 := by
        simpa using lemma211_withTop_add_le hQ
      exact hQTop.trans hCommonOne
    · have hQ := a.heHu2022Lemma211ExceptionalTailLong t b hm hBIntegral j
        hjEven hjBefore hJZero hSourcePrefixOrderEven hProductOdd hSourceLeJ
      have hQTop :
          (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
              WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) ≤ 0 := by
        norm_cast
      exact hQTop.trans hCommonNonnegative
  · have hJOne : 1 ≤ b.order j.castSucc := by omega
    have hQ :
        ((a.order sourceNext - b.order targetLast : Int) : ℚ) +
            b.alphaValue lastGap ≤ 0 :=
      lemma211_beta_le_zero hBetaBound hJOne
    have hQTop :
        (((a.order sourceNext - b.order targetLast : Int) : ℚ) :
            WithTop ℚ) + (b.alphaValue lastGap : WithTop ℚ) ≤ 0 := by
      simpa using lemma211_withTop_add_le hQ
    exact hQTop.trans hCommonNonnegative

/-- Exact-rank specialization of the long-source beta claim. -/
theorem heHu2022Lemma211BetaClaim (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hBIntegral : Lattice.IsIntegral r M)
    (j : Fin (2 * t + 2))
    (hjEven : Even j.val)
    (hjBefore : j.val + 1 < 2 * t + 2)
    (hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))))
    (hSourceLeJ : a.order ⟨2 * t + 3, by omega⟩ ≤ b.order j.succ)
    (hBetaBound :
      b.alphaValue ⟨2 * t + 1, by omega⟩ ≤
        ((b.order ⟨2 * t + 2, by omega⟩ -
          b.order j.castSucc : Int) : ℚ) +
        ((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ))
    (hJOrderNonnegative : 0 ≤ b.order j.castSucc)
    (hCommonNonnegative :
      (0 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3))
    (hCommonOneOfEven :
      Even (ordUnit K
        (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))) →
      (1 : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3)) :
    (((a.order ⟨2 * t + 3, by omega⟩ -
          b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (b.alphaValue ⟨2 * t + 1, by omega⟩ : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 (2 * t + 3) (2 * t + 3) := by
  exact a.heHu2022Lemma211BetaClaimLong t b (by omega) hBIntegral j
    hjEven hjBefore hSourcePrefixOrderEven hSourceLeJ hBetaBound
    hJOrderNonnegative hCommonNonnegative hCommonOneOfEven

end BONG.GoodBONG

end Bong
