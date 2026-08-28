/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma211Defect

/-!
# Beli (2019), Lemma 2.13: nonessential defect conditions

If neither endpoint of an ordinary representation boundary is essential,
the secondary order shift is nonpositive.  One of the two adjacent alpha
bounds then applies, and Lemma 2.11 makes condition 2.1(ii) automatic.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

private theorem isCurrentEssential_of_local
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < n + 1)
    (hfirst : b.order ⟨i.val - 2, by omega⟩ <
      a.order ⟨i.val, i.lt_large⟩)
    (hsecond : ∀ hiThree : 2 < i.val,
      b.order ⟨i.val - 3, by omega⟩ +
          b.order ⟨i.val - 2, by omega⟩ <
        a.order ⟨i.val, i.lt_large⟩ +
          a.order ⟨i.val + 1, hiNext⟩) :
    a.IsCurrentEssential b i := by
  unfold IsCurrentEssential currentEssentialIndex IsEssentialFor
    BeliOrderSequence.IsEssentialFor
  constructor
  · intro hj0 hjNext
    simp only [orderSequence_at]
    have hleft :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    have hright :
        (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [hleft, hright]
    exact hfirst
  · intro hjTwo hjNext
    change 1 < i.val - 1 at hjTwo
    change i.val - 1 + 2 < n + 1 at hjNext
    have hiThree : 2 < i.val := by omega
    have hs := hsecond hiThree
    simp only [orderSequence_at]
    have hleftTwo :
        (⟨i.val - 1 - 2, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 3, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 2 = i.val - 3
      omega
    have hleftOne :
        (⟨i.val - 1 - 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    have hrightOne :
        (⟨i.val - 1 + 1, by omega⟩ : Fin (n + 1)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hrightTwo :
        (⟨i.val - 1 + 2, by omega⟩ : Fin (n + 1)) =
          ⟨i.val + 1, hiNext⟩ := by
      apply Fin.ext
      change i.val - 1 + 2 = i.val + 1
      omega
    rw [hleftTwo, hleftOne, hrightOne, hrightTwo]
    exact hs

private theorem isNextEssential_of_local
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < i.val) (hiNext : i.val + 1 < n + 1)
    (hfirst : b.order ⟨i.val - 1, by omega⟩ <
      a.order ⟨i.val + 1, hiNext⟩)
    (hsecond : ∀ hiNextTwo : i.val + 2 < n + 1,
      b.order ⟨i.val - 2, by omega⟩ +
          b.order ⟨i.val - 1, by omega⟩ <
        a.order ⟨i.val + 1, by omega⟩ +
          a.order ⟨i.val + 2, hiNextTwo⟩) :
    a.IsNextEssential b i := by
  unfold IsNextEssential nextEssentialIndex IsEssentialFor
    BeliOrderSequence.IsEssentialFor
  constructor
  · intro hj0 hjNext
    simp only [orderSequence_at]
    exact hfirst
  · intro hjTwo hjNextTwo
    simp only [orderSequence_at]
    exact hsecond hjNextTwo

/-- Lemma 2.13 for condition (ii): if both adjacent essential indices fail,
the defect inequality at their common representation boundary is automatic. -/
theorem representationDefectAt_of_not_essential
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : ¬a.IsCurrentEssential b i)
    (hnext : ¬a.IsNextEssential b i) :
    a.RepresentationDefectAt b i := by
  have hiTwo : 1 < i.val := by
    by_contra h
    have hiOne : i.val = 1 := by have := i.pos; omega
    apply hcurrent
    have hz := BeliOrderSequence.isEssentialFor_zero
      a.orderSequence b.orderSequence
    unfold IsCurrentEssential
    have hindex : currentEssentialIndex i = (0 : Fin (n + 1)) := by
      apply Fin.ext
      change i.val - 1 = 0
      omega
    rw [hindex]
    exact hz
  have hiNext : i.val + 1 < n + 1 := by
    by_contra h
    have hiLast : i.val = n := by have := i.lt_large; omega
    apply hnext
    have hl := BeliOrderSequence.isEssentialFor_last
      a.orderSequence b.orderSequence
    unfold IsNextEssential
    have hindex : nextEssentialIndex i = Fin.last n := by
      apply Fin.ext
      simp only [nextEssentialIndex, hiLast, Fin.val_last]
    rw [hindex]
    exact hl
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
      apply isCurrentEssential_of_local a b i hiTwo hiNext hfirst
      intro hiThree
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
      apply isNextEssential_of_local a b i hiTwo hiNext hfirstNext
      intro hiNextTwo
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
      · have hiNextTwo : i.val + 2 < n + 1 := by
          by_contra hlast
          apply hnext
          apply isNextEssential_of_local a b i hiTwo hiNext hfirstNext
          intro hpossible
          omega
        have hsecondLe :
            a.order ⟨i.val + 1, by omega⟩ +
                a.order ⟨i.val + 2, hiNextTwo⟩ ≤
              b.order ⟨i.val - 2, by omega⟩ +
                b.order ⟨i.val - 1, by omega⟩ := by
          by_contra hs
          apply hnext
          apply isNextEssential_of_local a b i hiTwo hiNext hfirstNext
          intro _
          exact lt_of_not_ge hs
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_secondaryLeftCap b i
            ⟨hiTwo, hiNext⟩)
        rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        let p : Fin n := ⟨i.val, by omega⟩
        let pNext : Fin n := ⟨i.val + 1, by omega⟩
        have hp1 := by
          letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
          exact (a.alpha_p1 p (by
            simp only [p]
            omega)).2
        unfold alphaRightEndpoint at hp1
        have hsucc : p.succ =
            (⟨i.val + 1, hiNext⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have hnextSucc :
            pNext.succ =
              (⟨i.val + 2, hiNextTwo⟩ : Fin (n + 1)) := by
          apply Fin.ext
          simp only [pNext, Fin.val_succ]
        have hnextAlpha :
            (⟨i.val + 2 - 1, by omega⟩ : Fin n) =
              pNext := by
          apply Fin.ext
          simp only [pNext]
          omega
        have hp1Next :
            (⟨p.val + 1, by
              simp only [p]
              omega⟩ : Fin n) = pNext := by
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
            (⟨i.val + 1 - 1, by omega⟩ : Fin n) =
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
          apply isCurrentEssential_of_local a b i hiTwo hiNext hfirstCurrent
          intro hpossible
          omega
        have hsecondLe :
            a.order ⟨i.val, i.lt_large⟩ +
                a.order ⟨i.val + 1, hiNext⟩ ≤
              b.order ⟨i.val - 3, by omega⟩ +
                b.order ⟨i.val - 2, by omega⟩ := by
          by_contra hs
          apply hcurrent
          apply isCurrentEssential_of_local a b i hiTwo hiNext hfirstCurrent
          intro _
          exact lt_of_not_ge hs
        have hcand := (a.representationAlpha_le_prime b i).trans
          (a.representationAlphaPrime_le_secondaryRightCap b i
            ⟨hiTwo, hiNext⟩)
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcand
        let p : Fin n := ⟨i.val - 3, by omega⟩
        let pNext : Fin n := ⟨i.val - 2, by omega⟩
        have hp1 := by
          letI : Beli2006AlphaLaws.{u, w} K := targetLaws
          exact (b.alpha_p1 p (by
            simp only [p]
            omega)).1
        unfold alphaLeftEndpoint at hp1
        have hpCast : p.castSucc =
            (⟨i.val - 3, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have hpNextCast :
            pNext.castSucc =
              (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have halphaIndex :
            (⟨i.val - 2 - 1, by omega⟩ : Fin n) = p := by
          apply Fin.ext
          simp only [p]
          omega
        have hp1Next :
            (⟨p.val + 1, by
              simp only [p]
              omega⟩ : Fin n) = pNext := by
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

end BONG.GoodBONG

end Bong
