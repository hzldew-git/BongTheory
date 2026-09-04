/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma34

/-!
# He (2024), Lemma 3.5

This is the classic-integral analogue of He--Hu, Lemma 2.10(iii).  The
publisher statement already assumes the full alternating source-prefix
identity, so the proof starts at the capped-defect triangle and domination
step.  Indices in the conclusion are zero-based starts of the paper's even
adjacent pairs.
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

/-- He, Lemma 3.5.  Either the mixed prefix has the source threshold, or
an even target pair supplies the order/alpha tail bounds used in Lemma 3.8. -/
theorem he2022ClassicLemma35 {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (i : LongRepresentationIndex (m + 2) (n + 1))
    (hiEven : Even i.val)
    (hRi : a.order ⟨i.val - 1, by
      have := i.succ_lt_large
      omega⟩ = 0)
    (_hRiOne : a.order ⟨i.val, by
      have := i.succ_lt_large
      omega⟩ = 0)
    (hsourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ ((i.val + 2) / 2))
          0 (i.val + 2) =
        ((((1 - a.order ⟨i.val + 1, i.succ_lt_large⟩ : Int) : ℚ) :
          WithTop ℚ))) :
    let thresholdValue : ℚ :=
      ((1 - a.order ⟨i.val + 1, i.succ_lt_large⟩ : Int) : ℚ)
    let threshold : WithTop ℚ := (thresholdValue : WithTop ℚ)
    a.truncatedPrefixDefect b (-1) (i.val + 2) i.val = threshold ∨
      ∃ j : Fin (n + 1),
        Even j.val ∧ j.val + 1 < i.val ∧
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤ b.order j.succ ∧
          ∀ k : Fin (n + 1), j ≤ k →
            b.alphaValue k ≤
                ((b.order k.succ - b.order j.castSucc : Int) : ℚ) +
                  thresholdValue ∧
              ((b.order k.succ - b.order j.castSucc : Int) : ℚ) +
                  thresholdValue ≤
                (b.order k.succ : ℚ) + thresholdValue := by
  dsimp only
  have hiEvenCopy := hiEven
  obtain ⟨pairs, hiPairs⟩ := hiEven
  have hiFormula : i.val = 2 * pairs := by omega
  have hpairsPositive : 0 < pairs := by
    have := i.one_lt
    omega
  let nextTwo : Fin (m + 2) := ⟨i.val + 1, i.succ_lt_large⟩
  let thresholdValue : ℚ := ((1 - a.order nextTwo : Int) : ℚ)
  let threshold : WithTop ℚ := (thresholdValue : WithTop ℚ)
  let previousSign : Kˣ := (-1) ^ pairs
  let fullSign : Kˣ := (-1) ^ (pairs + 1)
  have hiDiv : i.val / 2 = pairs := by
    rw [hiFormula]
    omega
  have hfullDiv : (i.val + 2) / 2 = pairs + 1 := by
    rw [hiFormula]
    omega
  have hsourceEquality' :
      a.truncatedPrefixDefect a fullSign 0 (i.val + 2) = threshold := by
    dsimp only [fullSign, threshold, thresholdValue, nextTwo]
    rw [← hfullDiv]
    exact hsourceEquality
  have hleftSign : (-1 : Kˣ) * previousSign = fullSign := by
    simp only [previousSign, fullSign, pow_succ]
    ac_rfl
  have hrightSign : fullSign * previousSign = (-1 : Kˣ) := by
    simp only [fullSign, previousSign, pow_succ]
    rw [mul_assoc]
    have hsquare : ((-1 : Kˣ) ^ pairs) * ((-1 : Kˣ) ^ pairs) = 1 := by
      rw [← pow_add]
      have hsum : pairs + pairs = 2 * pairs := by omega
      rw [hsum, pow_mul]
      norm_num
    rw [mul_comm (-1 : Kˣ), ← mul_assoc, hsquare]
    simp
  have hpreviousSignSquare : previousSign * previousSign = 1 := by
    simp only [previousSign]
    rw [← pow_add]
    have hsum : pairs + pairs = 2 * pairs := by omega
    rw [hsum, pow_mul]
    norm_num
  have hfullSignSquare : fullSign * fullSign = 1 := by
    simp only [fullSign]
    rw [← pow_add]
    have hsum : pairs + 1 + (pairs + 1) = 2 * (pairs + 1) := by omega
    rw [hsum, pow_mul]
    norm_num
  let mixed := a.truncatedPrefixDefect b (-1) (i.val + 2) i.val
  let source := a.truncatedPrefixDefect a fullSign 0 (i.val + 2)
  let target := b.truncatedPrefixDefect b previousSign 0 i.val
  by_cases hmixed : mixed = threshold
  · left
    exact hmixed
  · right
    have hmixedSource : mixed ≠ source := by
      dsimp only [source]
      rw [hsourceEquality']
      exact hmixed
    have htargetUpper : target ≤ threshold := by
      rcases lt_or_gt_of_ne hmixedSource with hmixedLt | hsourceLt
      · have hstrict :
            a.truncatedPrefixDefect b (-1) (i.val + 2) i.val <
              a.truncatedPrefixDefect a ((-1) * previousSign)
                (i.val + 2) 0 := by
          rw [hleftSign, a.truncatedPrefixDefect_comm a fullSign]
          exact hmixedLt
        have htriangle :=
          a.truncatedPrefixDefect_eq_middle_of_lt_composite
            b a (-1) previousSign (by norm_num) hpreviousSignSquare
              (i.val + 2) i.val 0 hstrict
        have htargetEq : target = mixed := by
          calc
            target = b.truncatedPrefixDefect b previousSign i.val 0 :=
              b.truncatedPrefixDefect_comm b previousSign 0 i.val
            _ = b.truncatedPrefixDefect a previousSign i.val 0 :=
              (b.truncatedPrefixDefect_zero_right_eq_self
                a previousSign i.val).symm
            _ = mixed := htriangle.symm
        rw [htargetEq]
        exact hmixedLt.le.trans_eq hsourceEquality'
      · have hstrict :
            a.truncatedPrefixDefect a fullSign (i.val + 2) 0 <
              a.truncatedPrefixDefect b (fullSign * previousSign)
                (i.val + 2) i.val := by
          rw [a.truncatedPrefixDefect_comm a fullSign, hrightSign]
          exact hsourceLt
        have htriangle :=
          a.truncatedPrefixDefect_eq_middle_of_lt_composite
            a b fullSign previousSign hfullSignSquare
              hpreviousSignSquare (i.val + 2) 0 i.val hstrict
        have htargetEq : target = source := by
          calc
            target = a.truncatedPrefixDefect b previousSign 0 i.val :=
              (a.truncatedPrefixDefect_zero_left_eq_self
                b previousSign i.val).symm
            _ = a.truncatedPrefixDefect a fullSign (i.val + 2) 0 :=
              htriangle.symm
            _ = source :=
              a.truncatedPrefixDefect_comm a fullSign (i.val + 2) 0
        rw [htargetEq]
        simpa only [source] using hsourceEquality'.le
    rcases b.exists_even_cappedAdjacent_le_alternatingPrefix i.val
        (by omega) i.le_small_succ hiEvenCopy with
      ⟨j, hjEven, hjBefore, hjLocalTarget⟩
    have hjLocalTarget' :
        b.truncatedPrefixDefect b (-1) j.val (j.val + 2) ≤ target := by
      rw [hiDiv] at hjLocalTarget
      simpa only [target, previousSign] using hjLocalTarget
    have hjLocalUpper :
        b.truncatedPrefixDefect b (-1) j.val (j.val + 2) ≤ threshold :=
      hjLocalTarget'.trans htargetUpper
    have hnextTwoNonnegative : 0 ≤ a.order nextTwo := by
      have htwo := a.orderSequence.twoStep (i.val - 1) (by
        have := i.succ_lt_large
        omega)
      change a.order ⟨i.val - 1, by
          have := i.succ_lt_large
          omega⟩ ≤
        a.order ⟨i.val - 1 + 2, by
          have := i.succ_lt_large
          omega⟩ at htwo
      have hindex :
          (⟨i.val - 1 + 2, by
            have := i.succ_lt_large
            omega⟩ : Fin (m + 2)) = nextTwo := by
        apply Fin.ext
        change i.val - 1 + 2 = nextTwo.val
        simp only [nextTwo]
        omega
      rw [hindex, hRi] at htwo
      exact htwo
    have hthresholdInt :
        1 - a.order nextTwo < 2 * (ramificationIndex K : Int) := by
      have hePositive := ramificationIndex_pos (K := K)
      omega
    have hthresholdTwoE :
        threshold < ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
      dsimp only [threshold, thresholdValue]
      exact_mod_cast hthresholdInt
    let targetProfile := b.he2022ClassicProposition24 hBClassic
    have htargetPreviousNonnegative : 0 ≤ b.order j.castSucc :=
      (targetProfile.oddIndexed j.castSucc j.castSucc le_rfl
        hjEven hjEven).1
    let targetAlpha := b.he2022ClassicProposition23 j
    have htargetAlphaNe : b.alphaValue j ≠ 0 := by
      intro halphaZero
      have htwoE := targetAlpha.alphaZeroDefect halphaZero
      have htwoE' :
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
            b.truncatedPrefixDefect b (-1) j.val (j.val + 2) := by
        simpa only [heHuAdjacentCappedDefect] using htwoE
      exact (not_le_of_gt hthresholdTwoE) (htwoE'.trans hjLocalUpper)
    have htargetAlphaOne : 1 ≤ b.alphaValue j := by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      letI : Beli2009AlphaParityLaws.{u, w} K :=
        beliUniversalAlphaParityLaws
      exact b.one_le_alphaValue_of_ne_zero j htargetAlphaNe
    have hjAdjacent :
        (((((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
          b.alphaValue j : ℚ)) : WithTop ℚ) ≤
            b.truncatedPrefixDefect b (-1) j.val (j.val + 2) := by
      letI : Beli2006AlphaLaws.{u, w} K := beliUniversalAlphaLaws
      exact b.order_sub_add_alpha_le_cappedAdjacent j
    have hjAdjacentThreshold := hjAdjacent.trans hjLocalUpper
    have hsourceOrderLe : a.order nextTwo ≤ b.order j.succ := by
      have hraw := hjAdjacentThreshold
      dsimp only [threshold, thresholdValue] at hraw ⊢
      norm_cast at hraw
      push_cast at hraw
      have hpreviousQ : 0 ≤ (b.order j.castSucc : ℚ) := by
        exact_mod_cast htargetPreviousNonnegative
      have halphaQ : (1 : ℚ) ≤ b.alphaValue j := htargetAlphaOne
      have hsourceQ : (a.order nextTwo : ℚ) ≤
          (b.order j.succ : ℚ) := by
        linarith
      exact_mod_cast hsourceQ
    refine ⟨j, hjEven, hjBefore,
      by simpa only [nextTwo] using hsourceOrderLe, ?_⟩
    intro k hjk
    have hrightMono := b.alphaRightEndpoint_antitone hjk
    have hrightJ :
        b.alphaRightEndpoint j ≤
          -(b.order j.castSucc : ℚ) + thresholdValue := by
      have hraw := hjAdjacentThreshold
      dsimp only [threshold, thresholdValue] at hraw ⊢
      norm_cast at hraw
      unfold alphaRightEndpoint
      push_cast at hraw ⊢
      linarith
    have hrightK :
        b.alphaRightEndpoint k ≤
          -(b.order j.castSucc : ℚ) + thresholdValue :=
      hrightMono.trans hrightJ
    have hfirst :
        b.alphaValue k ≤
          ((b.order k.succ - b.order j.castSucc : Int) : ℚ) +
            thresholdValue := by
      unfold alphaRightEndpoint at hrightK
      push_cast at hrightK ⊢
      linarith
    have hsecond :
        ((b.order k.succ - b.order j.castSucc : Int) : ℚ) +
            thresholdValue ≤
          (b.order k.succ : ℚ) + thresholdValue := by
      have hpreviousQ : 0 ≤ (b.order j.castSucc : ℚ) := by
        exact_mod_cast htargetPreviousNonnegative
      push_cast
      linarith
    exact ⟨hfirst, hsecond⟩

end BONG.GoodBONG

end Bong
