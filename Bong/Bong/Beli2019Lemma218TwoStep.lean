/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma218
import Bong.Bong.Beli2019AuxiliaryAlphaBounds
import Bong.Bong.Beli2006SectionThree

/-!
# Beli (2019), Section 5: strict two-step consequences of Lemma 2.18

For the central representation condition, Lemma 2.18 gives two capped
adjacent-alpha alternatives on each of the target and source sides.  Away
from a global endpoint the caps are the actual alpha invariants.  Property
P6 then converts a strict adjacent-alpha sum into strict two-step growth of
the corresponding good-BONG order sequence.

This file keeps that argument below the Section 5 and Section 7 assembly
layers.  In particular, it can be used to construct the Lemma 3.7 models
needed by the index-uniformizer proof without importing any later
representation theorem.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- A strict adjacent-alpha sum forces strict two-step growth of the order
sequence.  This is the contrapositive of P6, combined with goodness. -/
theorem order_twoStep_lt_of_alphaSum_gt_twoE_forLemma37
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩) :
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ <
      b.order ⟨i.val, i.lt_large⟩ := by
  have hiOne : 1 < i.val := i.one_lt
  have hiLarge : i.val < n + 2 := i.lt_large
  let leftOrder : Fin (n + 2) := ⟨i.val - 2, by
      have := hiOne
      have := hiLarge
      omega⟩
  have hleftTwo : leftOrder.val + 2 < n + 2 := by
    dsimp only [leftOrder]
    have := i.one_lt
    have := i.lt_large
    omega
  have hmonoRaw := b.good leftOrder hleftTwo
  have hleftOrderIndex : leftOrder =
      (⟨i.val - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hrightOrderIndex :
      (⟨leftOrder.val + 2, hleftTwo⟩ : Fin (n + 2)) =
        (⟨i.val, hiLarge⟩ : Fin (n + 2)) := by
    apply Fin.ext
    dsimp only [leftOrder]
    omega
  have hmono : b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ ≤ b.order ⟨i.val, i.lt_large⟩ := by
    calc
      b.order ⟨i.val - 2, by omega⟩ = b.order leftOrder :=
        congrArg b.order hleftOrderIndex.symm
      _ ≤ b.order ⟨leftOrder.val + 2, hleftTwo⟩ := hmonoRaw
      _ = b.order ⟨i.val, hiLarge⟩ := congrArg b.order hrightOrderIndex
  apply lt_of_le_of_ne hmono
  intro heq
  let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  have hpreviousCast : previousAlpha.castSucc =
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnext : previousAlpha.val + 1 < n + 1 := by
    dsimp only [previousAlpha]
    have := hiLarge
    omega
  have hcurrentSucc :
      (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)).succ =
        (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    change (i.val - 2 + 1) + 1 = i.val
    omega
  have hendpoint : b.order previousAlpha.castSucc =
      b.order (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)).succ := by
    rw [hpreviousCast, hcurrentSucc]
    exact heq
  have hp6 := b.alpha_p6 previousAlpha hnext hendpoint
  have hpreviousAlphaIndex : previousAlpha =
      (⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hcurrentAlphaIndex :
      (⟨previousAlpha.val + 1, hnext⟩ : Fin (n + 1)) =
        (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    dsimp only [previousAlpha]
    have := hiOne
    omega
  have hp6' : b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ +
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ ≤ 2 * (ramificationIndex K : ℚ) := by
    have hpreviousValue :
        b.alphaValue (⟨i.val - 2, by omega⟩ : Fin (n + 1)) =
          b.alphaValue previousAlpha :=
      congrArg b.alphaValue hpreviousAlphaIndex.symm
    have hcurrentValue :
        b.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
          b.alphaValue ⟨previousAlpha.val + 1, hnext⟩ :=
      congrArg b.alphaValue hcurrentAlphaIndex.symm
    calc
      b.alphaValue ⟨i.val - 2, by omega⟩ +
          b.alphaValue ⟨i.val - 1, by omega⟩ =
        b.alphaValue previousAlpha +
          b.alphaValue ⟨previousAlpha.val + 1, hnext⟩ := by
            rw [hpreviousValue, hcurrentValue]
      _ ≤ 2 * (ramificationIndex K : ℚ) := hp6
  exact (not_lt_of_ge hp6' hsum)

/-- Target-side capped alternatives obtained from Lemma 2.18(i) and the
defect condition. -/
theorem centralTrigger_targetLemma37CapAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : b.centralAlphaTrigger c i) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val - 1) ∨
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) := by
  rcases b.beli2019Lemma218_target c hdefect i htrigger with
    hprevious | hcurrent
  · left
    apply hprevious.trans_le
    apply add_le_add le_rfl
    calc
      b.representationAlpha c i.previous ≤
          b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
        have hraw := hdefect i.previous
        rw [← b.coe_representationAlphaValue c i.previous]
        simpa only [CentralRepresentationIndex.previous] using hraw
      _ ≤ b.prefixAlphaCap (i.val - 1) :=
        b.truncatedPrefixDefect_le_leftCap c 1
          (i.val - 1) (i.val - 1)
  · right
    apply hcurrent.trans_le
    apply add_le_add le_rfl
    exact b.centralCurrentDefect_le_leftCap c i

/-- Source-side capped alternatives obtained from Lemma 2.18(ii) and the
defect condition. -/
theorem centralTrigger_sourceLemma37CapAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap (i.val - 2) + b.prefixAlphaCap (i.val - 1) ∨
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap (i.val - 1) + b.prefixAlphaCap i.val := by
  have hsource : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hcurrentCap : a.representationAlpha b (i.current (by omega)) ≤
      b.prefixAlphaCap i.val := by
    have hraw := hdefect (i.current (by omega))
    rw [a.coe_representationAlphaValue b (i.current (by omega))] at hraw
    exact hraw.trans
      (a.truncatedPrefixDefect_le_rightCap b 1 i.val i.val)
  rcases a.beli2019Lemma218_source (targetLaws := inferInstance)
      b hdefect i htrigger hsource with hcurrent | hprevious
  · right
    exact hcurrent.trans_le (add_le_add_right hcurrentCap _)
  · left
    calc
      _ < b.prefixAlphaCap (i.val - 1) +
          a.centralPreviousDefect b i := hprevious
      _ ≤ b.prefixAlphaCap (i.val - 1) +
          b.prefixAlphaCap (i.val - 2) :=
        add_le_add_right (a.centralPreviousDefect_le_rightCap b i) _
      _ = b.prefixAlphaCap (i.val - 2) +
          b.prefixAlphaCap (i.val - 1) := add_comm _ _

/-- Away from the target's right endpoint, Lemma 2.18(i) yields one of the
two strict adjacent target-alpha sums surrounding the represented prefix
boundary. -/
theorem centralTrigger_targetLemma37AlphaAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htrigger : b.centralAlphaTrigger c i) :
    2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ ∨
      2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val, by
            have := hiNext
            omega⟩ := by
  have hcaps := b.centralTrigger_targetLemma37CapAlternative
    c hdefect i htrigger
  rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large,
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) (by
        have := i.lt_large
        omega),
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) hiNext] at hcaps
  rcases hcaps with hleft | hright
  · left
    have hleftQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ +
            b.alphaValue ⟨i.val - 1 - 1, by
              have := i.lt_large
              omega⟩ := by
      exact_mod_cast hleft
    have hprevious :
        (⟨i.val - 1 - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    rw [hprevious] at hleftQ
    simpa only [add_comm] using hleftQ
  · right
    have hrightQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ +
            b.alphaValue ⟨i.val + 1 - 1, by
              have := hiNext
              omega⟩ := by
      exact_mod_cast hright
    have hcurrent :
        (⟨i.val + 1 - 1, by
          have := hiNext
          omega⟩ : Fin (n + 1)) =
          ⟨i.val, by
            have := hiNext
            omega⟩ := by
      apply Fin.ext
      change i.val + 1 - 1 = i.val
      omega
    simpa only [hcurrent] using hrightQ

/-- Away from the source's left endpoint, Lemma 2.18(ii) yields one of the
two strict adjacent source-alpha sums surrounding the source prefix
boundary. -/
theorem centralTrigger_sourceLemma37AlphaAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiPrevious : 2 < i.val)
    (htrigger : a.centralAlphaTrigger b i) :
    2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 3, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ ∨
      2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := by
  have hcaps := a.centralTrigger_sourceLemma37CapAlternative
    b hdefect i htrigger
  rw [b.prefixAlphaCap_of_internal (by
      have := hiPrevious
      omega) (by
        have := i.lt_large
        omega),
    b.prefixAlphaCap_of_internal (by
      have := hiPrevious
      omega) (by
        have := i.lt_large
        omega),
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large] at hcaps
  rcases hcaps with hleft | hright
  · left
    have hleftQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 2 - 1, by
            have := i.lt_large
            omega⟩ +
            b.alphaValue ⟨i.val - 1 - 1, by
              have := i.lt_large
              omega⟩ := by
      exact_mod_cast hleft
    have hfirst :
        (⟨i.val - 2 - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) =
          ⟨i.val - 3, by
            have := i.lt_large
            omega⟩ := by
      apply Fin.ext
      change i.val - 2 - 1 = i.val - 3
      omega
    have hsecond :
        (⟨i.val - 1 - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    simpa only [hfirst, hsecond] using hleftQ
  · right
    have hrightQ :
        2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1 - 1, by
            have := i.lt_large
            omega⟩ +
            b.alphaValue ⟨i.val - 1, by
              have := i.lt_large
              omega⟩ := by
      exact_mod_cast hright
    have hfirst :
        (⟨i.val - 1 - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 1)) =
          ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ := by
      apply Fin.ext
      change i.val - 1 - 1 = i.val - 2
      omega
    simpa only [hfirst] using hrightQ

/-- Strict target-order growth across one of the two Lemma 3.7 intervals. -/
theorem centralTrigger_targetLemma37TwoStepAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htrigger : b.centralAlphaTrigger c i) :
    b.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ < b.order ⟨i.val, i.lt_large⟩ ∨
      b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ <
        b.order ⟨i.val + 1, hiNext⟩ := by
  rcases b.centralTrigger_targetLemma37AlphaAlternative
      c hdefect i hiNext htrigger with hleft | hright
  · exact Or.inl (b.order_twoStep_lt_of_alphaSum_gt_twoE_forLemma37 i hleft)
  · let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by
          have := hiNext
          omega⟩
    have hj := b.order_twoStep_lt_of_alphaSum_gt_twoE_forLemma37 j (by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
        show i.val + 1 - 1 = i.val by omega] using hright)
    exact Or.inr (by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega] using hj)

/-- Strict source-order growth across one of the two Lemma 3.7 intervals. -/
theorem centralTrigger_sourceLemma37TwoStepAlternative
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 2)) (b : GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiPrevious : 2 < i.val)
    (htrigger : a.centralAlphaTrigger b i) :
    b.order ⟨i.val - 3, by
      have := i.lt_large
      omega⟩ < b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ ∨
      b.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ <
        b.order ⟨i.val, i.lt_large⟩ := by
  rcases a.centralTrigger_sourceLemma37AlphaAlternative
      b hdefect i hiPrevious htrigger with hleft | hright
  · let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val - 1, by
        have := hiPrevious
        omega, by
          have := i.lt_large
          omega, by
            have := i.le_small_succ
            omega⟩
    have hj := b.order_twoStep_lt_of_alphaSum_gt_twoE_forLemma37 j (by
      simpa only [j, show i.val - 1 - 2 = i.val - 3 by omega,
        show i.val - 1 - 1 = i.val - 2 by omega] using hleft)
    exact Or.inl (by
      simpa only [j, show i.val - 1 - 2 = i.val - 3 by omega] using hj)
  · exact Or.inr (b.order_twoStep_lt_of_alphaSum_gt_twoE_forLemma37 i hright)

end BONG.GoodBONG

end Bong
