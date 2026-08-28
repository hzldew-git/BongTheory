/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenCandidateShift
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the alpha shift

On a two-step order plateau, Corollary 2.3 gives the exact recurrence for
the alpha at the right boundary.  Applying it to two profiles whose first
order is shifted by `+1` and whose middle order is shifted by `-1` produces
the identity `beta_i = alpha_i + 2` used in the small-gap branch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Corollary 2.3's alpha recurrence across two equal order entries. -/
theorem currentAlpha_eq_order_sub_add_previous_of_twoStep
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (htwoStep : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      b.order ⟨i.val, i.lt_large⟩) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      ((b.order ⟨i.val - 2, by
          have hb := i.lt_large
          omega⟩ -
        b.order ⟨i.val - 1, by
          have hb := i.lt_large
          omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨i.val - 2, by
          have hb := i.lt_large
          omega⟩ := by
  let previous : Fin (n + 1) := ⟨i.val - 2, by
    have hb := i.lt_large
    omega⟩
  let current : Fin (n + 1) := ⟨i.val - 1, by
    have hb := i.lt_large
    omega⟩
  have hpreviousCurrent : previous ≤ current := by
    change i.val - 2 ≤ i.val - 1
    omega
  have hpreviousSucc : previous.succ = current.castSucc := by
    apply Fin.ext
    simp only [previous, current, Fin.val_succ, Fin.val_castSucc]
    omega
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hcurrentCast : current.castSucc =
      (⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hsum : b.adjacentOrderSum previous =
      b.adjacentOrderSum current := by
    unfold adjacentOrderSum
    rw [hpreviousSucc, hcurrentSucc]
    change b.order ⟨i.val - 2, by
          have hb := i.lt_large
          omega⟩ +
        b.order current.castSucc =
      b.order current.castSucc + b.order ⟨i.val, i.lt_large⟩
    rw [htwoStep]
    omega
  have hendpoint :=
    (b.beli2009Corollary23 previous current hpreviousCurrent hsum).leftEndpoint_eq
      current hpreviousCurrent le_rfl
  unfold alphaLeftEndpoint at hendpoint
  have hresult : b.alphaValue current =
      ((b.order previous.castSucc - b.order current.castSucc : Int) : ℚ) +
        b.alphaValue previous := by
    push_cast at hendpoint ⊢
    linarith
  rw [hpreviousCast, hcurrentCast] at hresult
  simpa only [previous, current] using hresult

/-- If the following source gap is below `2e`, a preceding alpha bounded by
one on a two-step plateau is exactly one. -/
theorem previousAlpha_eq_one_of_twoStep_of_nextGap_lt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q L (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (htwoStep : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hnextGap : b.orderGap ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ <
      2 * (ramificationIndex K : Int))
    (hpreviousLe : b.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ ≤ 1) :
    b.alphaValue ⟨i.val - 2, by
      have hb := i.lt_large
      omega⟩ = 1 := by
  let previous : Fin (n + 1) := ⟨i.val - 2, by
    have hb := i.lt_large
    omega⟩
  let current : Fin (n + 1) := ⟨i.val - 1, by
    have hb := i.lt_large
    omega⟩
  have hpreviousSucc : previous.succ = current.castSucc := by
    apply Fin.ext
    simp only [previous, current, Fin.val_succ, Fin.val_castSucc]
    omega
  have hcurrentSucc : current.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hnextGap' : b.order current.succ - b.order current.castSucc <
      2 * (ramificationIndex K : Int) := by
    simpa only [orderGap, current] using hnextGap
  have hpreviousGap : -(2 * (ramificationIndex K : Int)) <
      b.orderGap previous := by
    unfold orderGap
    rw [hpreviousSucc, hpreviousCast]
    rw [hcurrentSucc] at hnextGap'
    rw [← htwoStep] at hnextGap'
    omega
  have hne : b.alphaValue previous ≠ 0 := by
    intro hzero
    have hbottom := (b.alpha_p2 previous).2.mp hzero
    exact (ne_of_gt hpreviousGap) hbottom
  have hlower := b.one_le_alphaValue_of_ne_zero previous hne
  have hupper : b.alphaValue previous ≤ 1 := by
    simpa only [previous] using hpreviousLe
  simpa only [previous] using le_antisymm hupper hlower

/-- Two matching alpha recurrences with order shifts `+1,-1` differ by
exactly two at their right endpoints. -/
theorem currentAlpha_eq_add_two_of_shifted_twoStep
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val)
    (htwoA : a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val, i.lt_large⟩)
    (htwoB : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      b.order ⟨i.val, i.lt_large⟩)
    (hprevious : b.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩)
    (hleft : b.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 2, by
        have hb := i.lt_large
        omega⟩ + 1)
    (hmiddle : b.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.order ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ - 1) :
    b.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hb := i.lt_large
        omega⟩ + 2 := by
  have ha := a.currentAlpha_eq_order_sub_add_previous_of_twoStep
    i hiTwo htwoA
  have hb := b.currentAlpha_eq_order_sub_add_previous_of_twoStep
    i hiTwo htwoB
  push_cast at ha hb
  have hleftQ := congrArg (fun z : Int => (z : ℚ)) hleft
  have hmiddleQ := congrArg (fun z : Int => (z : ℚ)) hmiddle
  push_cast at hleftQ hmiddleQ
  linarith

end BONG.GoodBONG

end Bong
