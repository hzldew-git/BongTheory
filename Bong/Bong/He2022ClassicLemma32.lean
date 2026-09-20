/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma31
import Bong.Bong.Beli2019Lemma213Nonessential

/-!
# He (2024), Lemma 3.2

This file supplies the unequal-rank form of Beli's nonessential-index
argument needed in He, Lemma 3.2.  The older Beli implementation used
same-rank order sequences because it served a transitivity proof.  The
proof below retains the actual source and target ranks and therefore
matches the hypotheses of the published classic-universality paper.
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

/-- Essentiality at the paper index immediately to the left of an
ordinary representation boundary, with source and target ranks allowed
to differ.  Proof-quantified clauses implement Beli's endpoint convention. -/
def HeClassicCurrentEssentialAt {m n : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) : Prop :=
  (∀ hiTwo : 1 < i.val,
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ <
        a.order ⟨i.val, i.lt_large⟩) ∧
    (∀ hiThree : 2 < i.val, ∀ hiNext : i.val + 1 < m + 1,
      b.order ⟨i.val - 3, by have := i.le_small; omega⟩ +
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩)

/-- Essentiality at the paper index immediately to the right of an
ordinary representation boundary, again without an equal-rank artifact. -/
def HeClassicNextEssentialAt {m n : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) : Prop :=
  (∀ hiNext : i.val + 1 < m + 1,
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ <
        a.order ⟨i.val + 1, hiNext⟩) ∧
    (∀ hiNextTwo : i.val + 2 < m + 1,
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ +
          b.order ⟨i.val - 1, by have := i.le_small; omega⟩ <
        a.order ⟨i.val + 1, by omega⟩ +
          a.order ⟨i.val + 2, hiNextTwo⟩)

/-- Beli (2006), Lemma 4.8, in the unequal-rank form used by He.  If the
two essential indices adjacent to an interior representation boundary both
fail, Theorem 2.5(ii) is automatic at that boundary. -/
theorem representationDefectAt_of_not_heClassicEssential
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < m + 1)
    (hcurrent : ¬a.HeClassicCurrentEssentialAt b i)
    (hnext : ¬a.HeClassicNextEssentialAt b i) :
    a.RepresentationDefectAt b i := by
  have hiSmall := i.le_small
  have hpair :
      a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hiNext⟩ ≤
        b.order ⟨i.val - 2, by omega⟩ +
          b.order ⟨i.val - 1, by omega⟩ := by
    by_contra hp
    have hpStrict :
        b.order ⟨i.val - 2, by omega⟩ +
            b.order ⟨i.val - 1, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩ +
            a.order ⟨i.val + 1, hiNext⟩ := lt_of_not_ge hp
    by_cases hfirst : b.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, i.lt_large⟩
    · apply hcurrent
      constructor
      · intro _
        exact hfirst
      · intro hiThree _
        have htwoRaw := b.orderSequence.twoStep (i.val - 3) (by omega)
        change b.order ⟨i.val - 3, by omega⟩ ≤
          b.order ⟨i.val - 3 + 2, by omega⟩ at htwoRaw
        have hindex :
            (⟨i.val - 3 + 2, by omega⟩ : Fin (n + 1)) =
              ⟨i.val - 1, by omega⟩ := by
          apply Fin.ext
          change i.val - 3 + 2 = i.val - 1
          omega
        rw [hindex] at htwoRaw
        omega
    · have hfirstNext : b.order ⟨i.val - 1, by omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩ := by omega
      apply hnext
      constructor
      · intro _
        exact hfirstNext
      · intro hiNextTwo
        have htwoRaw := a.orderSequence.twoStep i.val hiNextTwo
        change a.order ⟨i.val, by omega⟩ ≤
          a.order ⟨i.val + 2, hiNextTwo⟩ at htwoRaw
        omega
  have hside :
      a.order ⟨i.val, i.lt_large⟩ ≤
          b.order ⟨i.val - 2, by omega⟩ ∨
        a.order ⟨i.val + 1, hiNext⟩ ≤
          b.order ⟨i.val - 1, by omega⟩ := by
    by_cases hleft : a.order ⟨i.val, i.lt_large⟩ ≤
        b.order ⟨i.val - 2, by omega⟩
    · exact Or.inl hleft
    · right
      omega
  rcases hside with hleft | hright
  · have hnextBound : a.representationAlpha b i ≤
        a.nextFallbackAlphaBound i hiNext := by
      by_cases hfirstNext : b.order ⟨i.val - 1, by omega⟩ <
          a.order ⟨i.val + 1, hiNext⟩
      · have hiNextTwo : i.val + 2 < m + 1 := by
          by_contra hlast
          apply hnext
          constructor
          · intro _
            exact hfirstNext
          · intro hpossible
            omega
        have hsecondLe :
            a.order ⟨i.val + 1, by omega⟩ +
                a.order ⟨i.val + 2, hiNextTwo⟩ ≤
              b.order ⟨i.val - 2, by omega⟩ +
                b.order ⟨i.val - 1, by omega⟩ := by
          by_contra hs
          apply hnext
          constructor
          · intro _
            exact hfirstNext
          · intro _
            exact lt_of_not_ge hs
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_secondaryLeftCap b i
            ⟨hiTwo, hiNext⟩)
        rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        let p : Fin m := ⟨i.val, by omega⟩
        let pNext : Fin m := ⟨i.val + 1, by omega⟩
        have hp1 := by
          letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
          exact (a.alpha_p1 p (by simp only [p]; omega)).2
        unfold alphaRightEndpoint at hp1
        have hsucc : p.succ =
            (⟨i.val + 1, hiNext⟩ : Fin (m + 1)) := by
          apply Fin.ext
          rfl
        have hnextSucc : pNext.succ =
            (⟨i.val + 2, hiNextTwo⟩ : Fin (m + 1)) := by
          apply Fin.ext
          simp only [pNext, Fin.val_succ]
        have hnextAlpha :
            (⟨i.val + 2 - 1, by omega⟩ : Fin m) = pNext := by
          apply Fin.ext
          simp only [pNext]
          omega
        have hp1Next :
            (⟨p.val + 1, by simp only [p]; omega⟩ : Fin m) = pNext := by
          apply Fin.ext
          simp only [p, pNext]
        rw [hnextAlpha] at hcand
        rw [hp1Next] at hp1
        rw [hsucc, hnextSucc] at hp1
        unfold nextFallbackAlphaBound
        have hsecondQ :
            (a.order ⟨i.val + 1, hiNext⟩ : ℚ) +
                (a.order ⟨i.val + 2, hiNextTwo⟩ : ℚ) ≤
              (b.order ⟨i.val - 2, by omega⟩ : ℚ) +
                (b.order ⟨i.val - 1, by omega⟩ : ℚ) := by
          exact_mod_cast hsecondLe
        have hq :
            ((a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hiNext⟩ -
                b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
                a.alphaValue pNext ≤
              ((a.order ⟨i.val, i.lt_large⟩ -
                a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) +
                a.alphaValue p := by
          push_cast
          linarith [hsecondQ, hp1]
        apply hcand.trans
        exact_mod_cast hq
      · have horder : a.order ⟨i.val + 1, hiNext⟩ ≤
            b.order ⟨i.val - 1, by omega⟩ := le_of_not_gt hfirstNext
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_primaryLeftCap b i)
        rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        have hindex :
            (⟨i.val + 1 - 1, by omega⟩ : Fin m) =
              ⟨i.val, by omega⟩ := by
          apply Fin.ext
          change i.val + 1 - 1 = i.val
          omega
        rw [hindex] at hcand
        unfold nextFallbackAlphaBound
        apply hcand.trans
        have hq :
            ((a.order ⟨i.val, i.lt_large⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
              ((a.order ⟨i.val, i.lt_large⟩ -
                a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) := by
          exact_mod_cast sub_le_sub_left horder _
        have hqTop :
            ((((a.order ⟨i.val, i.lt_large⟩ -
              b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
              ((((a.order ⟨i.val, i.lt_large⟩ -
                a.order ⟨i.val + 1, hiNext⟩ : Int) : ℚ) : WithTop ℚ)) := by
          exact_mod_cast hq
        exact add_le_add hqTop le_rfl
    exact a.representationDefectAt_of_le_nextFallbackAlphaBound
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hiTwo hiNext hpair hleft hnextBound
  · have hcurrentBound : a.representationAlpha b i ≤
        a.currentFallbackAlphaBound b i hiTwo := by
      by_cases hfirstCurrent : b.order ⟨i.val - 2, by omega⟩ <
          a.order ⟨i.val, i.lt_large⟩
      · have hiThree : 2 < i.val := by
          by_contra hsmall
          apply hcurrent
          constructor
          · intro _
            exact hfirstCurrent
          · intro hpossible _
            omega
        have hsecondLe :
            a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hiNext⟩ ≤
              b.order ⟨i.val - 3, by omega⟩ +
                b.order ⟨i.val - 2, by omega⟩ := by
          by_contra hs
          apply hcurrent
          constructor
          · intro _
            exact hfirstCurrent
          · intro _ _
            exact lt_of_not_ge hs
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_secondaryRightCap b i
            ⟨hiTwo, hiNext⟩)
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        let p : Fin n := ⟨i.val - 3, by omega⟩
        let pNext : Fin n := ⟨i.val - 2, by omega⟩
        have hp1 := by
          letI : Beli2006AlphaLaws.{u, w} K := targetLaws
          exact (b.alpha_p1 p (by simp only [p]; omega)).1
        unfold alphaLeftEndpoint at hp1
        have hpCast : p.castSucc =
            (⟨i.val - 3, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have hpNextCast : pNext.castSucc =
            (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have halphaIndex :
            (⟨i.val - 2 - 1, by omega⟩ : Fin n) = p := by
          apply Fin.ext
          simp only [p]
          omega
        have hp1Next :
            (⟨p.val + 1, by simp only [p]; omega⟩ : Fin n) = pNext := by
          apply Fin.ext
          simp only [p, pNext]
          omega
        rw [halphaIndex] at hcand
        rw [hp1Next] at hp1
        rw [hpCast, hpNextCast] at hp1
        unfold currentFallbackAlphaBound
        have hsecondQ :
            (a.order ⟨i.val, i.lt_large⟩ : ℚ) +
                (a.order ⟨i.val + 1, hiNext⟩ : ℚ) ≤
              (b.order ⟨i.val - 3, by omega⟩ : ℚ) +
                (b.order ⟨i.val - 2, by omega⟩ : ℚ) := by
          exact_mod_cast hsecondLe
        have hq :
            ((a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hiNext⟩ -
                b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
                b.alphaValue p ≤
              ((b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) +
                b.alphaValue pNext := by
          push_cast
          linarith [hsecondQ, hp1]
        apply hcand.trans
        exact_mod_cast hq
      · have horder : a.order ⟨i.val, i.lt_large⟩ ≤
            b.order ⟨i.val - 2, by omega⟩ := le_of_not_gt hfirstCurrent
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_primaryRightCap b i)
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        have hindex :
            (⟨i.val - 1 - 1, by omega⟩ : Fin n) =
              ⟨i.val - 2, by omega⟩ := by
          apply Fin.ext
          change i.val - 1 - 1 = i.val - 2
          omega
        rw [hindex] at hcand
        unfold currentFallbackAlphaBound
        apply hcand.trans
        have hq :
            ((a.order ⟨i.val, i.lt_large⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) ≤
              ((b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) := by
          exact_mod_cast sub_le_sub_right horder _
        have hqTop :
            ((((a.order ⟨i.val, i.lt_large⟩ -
              b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) ≤
              ((((b.order ⟨i.val - 2, by omega⟩ -
                b.order ⟨i.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ)) := by
          exact_mod_cast hq
        exact add_le_add hqTop le_rfl
    exact a.representationDefectAt_of_le_currentFallbackAlphaBound
      (sourceLaws := sourceLaws) (targetLaws := targetLaws)
      b i hiTwo hiNext hpair hright hcurrentBound

/-- He, Lemma 3.2.  If the first `j + 1` paper orders vanish and `j`
is even, condition 2.5(ii) holds at every boundary `2 ≤ i < j`.
The `RepresentationIndex` itself records the other rank bound. -/
theorem he2022ClassicLemma32 {m n : Nat}
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M (n + 2))
    (hBClassic : Lattice.IsClassicIntegral r M)
    (j : Nat) (_hjPositive : 0 < j) (hjEven : Even j)
    (hjSource : j < m + 2)
    (hzero : ∀ k : Fin (m + 2), k.val ≤ j → a.order k = 0)
    (i : RepresentationIndex (m + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiJ : i.val < j) :
    a.HeClassicDefectConditionAt b i := by
  have hiNext : i.val + 1 < m + 2 := by omega
  have hiSmall := i.le_small
  let targetProfile := b.he2022ClassicProposition24 hBClassic
  have hcurrent : ¬a.HeClassicCurrentEssentialAt b i := by
    intro hessential
    by_cases hiEven : Even i.val
    · have hpreviousEven : Even (i.val - 2) := by
        rcases hiEven with ⟨t, ht⟩
        have htPositive : 0 < t := by omega
        exact ⟨t - 1, by omega⟩
      let previous : Fin (n + 2) := ⟨i.val - 2, by omega⟩
      have hbounds := targetProfile.oddIndexed 0 previous
        (Fin.zero_le previous) Even.zero
        (by simpa only [previous] using hpreviousEven)
      have hnonnegative : 0 ≤ b.order previous := hbounds.1.trans hbounds.2
      have hcross := hessential.1 (by omega)
      have hsourceZero : a.order ⟨i.val, i.lt_large⟩ = 0 :=
        hzero ⟨i.val, i.lt_large⟩ (Nat.le_of_lt hiJ)
      rw [hsourceZero] at hcross
      exact (not_lt_of_ge hnonnegative) (by
        simpa only [previous] using hcross)
    · have hiOdd : Odd i.val := Nat.not_even_iff_odd.mp hiEven
      have hiThree : 2 < i.val := by
        rcases hiOdd with ⟨t, ht⟩
        omega
      have hcross := hessential.2 hiThree hiNext
      have hsourceZero : a.order ⟨i.val, i.lt_large⟩ = 0 :=
        hzero ⟨i.val, i.lt_large⟩ (Nat.le_of_lt hiJ)
      have hsourceNextZero : a.order ⟨i.val + 1, hiNext⟩ = 0 :=
        hzero ⟨i.val + 1, hiNext⟩
          (show i.val + 1 ≤ j by omega)
      let previousPair : Fin (n + 1) := ⟨i.val - 3, by omega⟩
      have htargetNonnegative := targetProfile.adjacentOrderSum previousPair
      unfold adjacentOrderSum at htargetNonnegative
      have hleft : previousPair.castSucc =
          (⟨i.val - 3, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      have hright : previousPair.succ =
          (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [previousPair, Fin.val_succ]
        omega
      rw [hleft, hright] at htargetNonnegative
      rw [hsourceZero, hsourceNextZero, add_zero] at hcross
      exact (not_lt_of_ge htargetNonnegative) hcross
  have hnext : ¬a.HeClassicNextEssentialAt b i := by
    intro hessential
    by_cases hiEven : Even i.val
    · rcases hiEven with ⟨s, hs⟩
      rcases hjEven with ⟨t, ht⟩
      have hiTwoSteps : i.val + 2 ≤ j := by omega
      have hiNextTwo : i.val + 2 < m + 2 := by omega
      have hcross := hessential.2 hiNextTwo
      have hsourceNextZero : a.order ⟨i.val + 1, by omega⟩ = 0 :=
        hzero ⟨i.val + 1, by omega⟩
          (show i.val + 1 ≤ j by omega)
      have hsourceNextTwoZero : a.order ⟨i.val + 2, hiNextTwo⟩ = 0 :=
        hzero ⟨i.val + 2, hiNextTwo⟩ hiTwoSteps
      let previousPair : Fin (n + 1) := ⟨i.val - 2, by omega⟩
      have htargetNonnegative := targetProfile.adjacentOrderSum previousPair
      unfold adjacentOrderSum at htargetNonnegative
      have hleft : previousPair.castSucc =
          (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      have hright : previousPair.succ =
          (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        simp only [previousPair, Fin.val_succ]
        omega
      rw [hleft, hright] at htargetNonnegative
      rw [hsourceNextZero, hsourceNextTwoZero, add_zero] at hcross
      exact (not_lt_of_ge htargetNonnegative) hcross
    · have hiOdd : Odd i.val := Nat.not_even_iff_odd.mp hiEven
      have hpreviousEven : Even (i.val - 1) := by
        rcases hiOdd with ⟨t, ht⟩
        exact ⟨t, by omega⟩
      let previous : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      have hbounds := targetProfile.oddIndexed 0 previous
        (Fin.zero_le previous) Even.zero
        (by simpa only [previous] using hpreviousEven)
      have hnonnegative : 0 ≤ b.order previous := hbounds.1.trans hbounds.2
      have hcross := hessential.1 hiNext
      have hsourceNextZero : a.order ⟨i.val + 1, hiNext⟩ = 0 :=
        hzero ⟨i.val + 1, hiNext⟩
          (show i.val + 1 ≤ j by omega)
      rw [hsourceNextZero] at hcross
      exact (not_lt_of_ge hnonnegative) (by
        simpa only [previous] using hcross)
  have hdefect := a.representationDefectAt_of_not_heClassicEssential
    (sourceLaws := beliUniversalAlphaLaws)
    (targetLaws := beliUniversalAlphaLaws)
    b i hiTwo hiNext hcurrent hnext
  unfold RepresentationDefectAt at hdefect
  unfold HeClassicDefectConditionAt
  rw [a.coe_representationAlphaValue b i]
  exact hdefect

end BONG.GoodBONG

end Bong
