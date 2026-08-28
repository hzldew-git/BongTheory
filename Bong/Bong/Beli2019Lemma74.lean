/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69CappedPropagation
import Bong.Bong.Beli2019Lemma73
import Bong.Bong.Beli2019ExtremalDifference

/-!
# Beli (2019), Lemma 7.4

This file starts the defect arithmetic used throughout Section 7.  Alternating
adjacent capped defects are joined by the domination principle.  Monotonicity
of the two alpha endpoints then supplies the lower bounds in parts (i) and
(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Read a valid zero-extended order-sequence entry as the corresponding
BONG order. -/
theorem orderSequence_entryOrZero_eq_order
    (b : GoodBONG q L n) (i : Fin n) :
    b.orderSequence.entryOrZero i.val = b.order i := by
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt]
  exact b.orderSequence_at i.val i.isLt

/-- Every same-parity entry between two equal endpoints of a Beli order
sequence has the same order. -/
theorem order_eq_of_evenGap_between_equal
    (b : GoodBONG q L n) (i k j : Fin n)
    (hik : i ≤ k) (hkj : k ≤ j)
    (hikEven : Even (k.val - i.val))
    (hkjEven : Even (j.val - k.val))
    (horder : b.order i = b.order j) :
    b.order k = b.order j := by
  have hikEntry := b.orderSequence.entryOrZero_le_of_evenGap
    i.val k.val (by omega) k.isLt hikEven
  have hkjEntry := b.orderSequence.entryOrZero_le_of_evenGap
    k.val j.val (by omega) j.isLt hkjEven
  rw [b.orderSequence_entryOrZero_eq_order i,
    b.orderSequence_entryOrZero_eq_order k] at hikEntry
  rw [b.orderSequence_entryOrZero_eq_order k,
    b.orderSequence_entryOrZero_eq_order j] at hkjEntry
  apply le_antisymm hkjEntry
  rwa [← horder]

/-- Repeated capped-defect domination along alternating adjacent pairs. -/
theorem truncatedPrefixDefect_alternating_ge
    (b : GoodBONG q L (n + 1)) (start pairs : Nat)
    (hbound : start + 2 * (pairs + 1) ≤ n + 1)
    (c : WithTop ℚ)
    (hlocal : ∀ t, t ≤ pairs →
      c ≤ b.truncatedPrefixDefect b (-1)
        (start + 2 * t) (start + 2 * t + 2)) :
    c ≤ b.truncatedPrefixDefect b ((-1) ^ (pairs + 1))
      start (start + 2 * (pairs + 1)) := by
  induction pairs with
  | zero =>
      simpa using hlocal 0 le_rfl
  | succ pairs ih =>
      have hprevious := ih (by omega) (fun t ht ↦
        hlocal t (by omega))
      have hlast := hlocal (pairs + 1) (by omega)
      have hend : start + 2 * (pairs + 1) + 2 =
          start + 2 * (pairs + 2) := by
        omega
      rw [hend] at hlast
      have hdom := b.truncatedPrefixDefect_domination b b
        ((-1) ^ (pairs + 1)) (-1) start
        (start + 2 * (pairs + 1)) (start + 2 * (pairs + 2))
      have hjoined := (le_min hprevious hlast).trans hdom
      simpa only [pow_succ] using hjoined

/-- Beli (2019), Lemma 7.4(i).  Indices are zero-based: `i` and `j`
represent the paper's entries `i+1` and `j+1`. -/
theorem beli2019Lemma74_i
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hij : i ≤ j) (heven : Even (j.val - i.val))
    (horder : b.order i.castSucc = b.order j.castSucc) :
    (((((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
        b.alphaValue j : ℚ)) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((j.val - i.val + 2) / 2)) i.val (j.val + 2) := by
  rcases heven with ⟨d, hd⟩
  have hjFormula : j.val = i.val + 2 * d := by omega
  have hpairs : (j.val - i.val + 2) / 2 = d + 1 := by omega
  have hend : i.val + 2 * (d + 1) = j.val + 2 := by omega
  let critical : WithTop ℚ :=
    ((((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
      b.alphaValue j : ℚ) : WithTop ℚ)
  have hlocal (t : Nat) (ht : t ≤ d) :
      critical ≤ b.truncatedPrefixDefect b (-1)
        (i.val + 2 * t) (i.val + 2 * t + 2) := by
    let k : Fin (n + 1) := ⟨i.val + 2 * t, by omega⟩
    have hik : i ≤ k := by
      change i.val ≤ k.val
      simp only [k]
      omega
    have hkj : k ≤ j := by
      change k.val ≤ j.val
      simp only [k]
      omega
    have hentryEndpoints : b.orderSequence.entryOrZero i.val =
        b.orderSequence.entryOrZero j.val := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega),
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      exact horder
    have hikOrder := b.orderSequence.entryOrZero_le_of_evenGap
      i.val k.val (by omega) (by omega) ⟨t, by simp only [k]; omega⟩
    have hkjOrder := b.orderSequence.entryOrZero_le_of_evenGap
      k.val j.val (by omega) (by omega) ⟨d - t, by
        simp only [k]
        omega⟩
    have hkEntry : b.orderSequence.entryOrZero k.val =
        b.orderSequence.entryOrZero j.val := by
      omega
    have hkOrder : b.order k.castSucc = b.order j.castSucc := by
      exact (b.orderSequence_entryOrZero_eq_order k.castSucc).symm.trans
        (hkEntry.trans (b.orderSequence_entryOrZero_eq_order j.castSucc))
    have hendpoint := b.alphaRightEndpoint_antitone hkj
    have hcriticalQ :
        ((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
            b.alphaValue j ≤
          ((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
            b.alphaValue k := by
      unfold alphaRightEndpoint at hendpoint
      push_cast at hendpoint ⊢
      have hkOrderQ : (b.order k.castSucc : ℚ) =
          (b.order j.castSucc : ℚ) := by
        exact_mod_cast hkOrder
      linarith
    have hcriticalTop : critical ≤
        (((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
          b.alphaValue k : ℚ)) : WithTop ℚ) := by
      simpa only [critical] using WithTop.coe_le_coe.mpr hcriticalQ
    exact hcriticalTop.trans
      (b.order_sub_add_alpha_le_cappedAdjacent k)
  have hsegment := b.truncatedPrefixDefect_alternating_ge
    i.val d (by omega) critical hlocal
  rw [hpairs, ← hend]
  exact hsegment

/-- Beli (2019), Lemma 7.4(ii). -/
theorem beli2019Lemma74_ii
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hij : i ≤ j) (hipos : 0 < i.val)
    (heven : Even (j.val - i.val))
    (horder : b.order i.castSucc = b.order j.castSucc) :
    let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    (((((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
        b.alphaValue previous : ℚ)) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((j.val - i.val + 2) / 2))
        (i.val - 1) (j.val + 1) := by
  dsimp only
  rcases heven with ⟨d, hd⟩
  have hjFormula : j.val = i.val + 2 * d := by omega
  have hpairs : (j.val - i.val + 2) / 2 = d + 1 := by omega
  have hend : i.val - 1 + 2 * (d + 1) = j.val + 1 := by omega
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let critical : WithTop ℚ :=
    ((((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
      b.alphaValue previous : ℚ) : WithTop ℚ)
  have hpreviousSucc : b.order previous.succ = b.order i.castSucc := by
    apply congrArg b.order
    apply Fin.ext
    simp only [previous, Fin.val_succ, Fin.val_castSucc]
    omega
  have hlocal (t : Nat) (ht : t ≤ d) :
      critical ≤ b.truncatedPrefixDefect b (-1)
        (i.val - 1 + 2 * t) (i.val - 1 + 2 * t + 2) := by
    let k : Fin (n + 1) := ⟨i.val - 1 + 2 * t, by omega⟩
    have hpreviousK : previous ≤ k := by
      change previous.val ≤ k.val
      simp only [previous, k]
      omega
    have hnextIndex : k.val + 1 = i.val + 2 * t := by
      simp only [k]
      omega
    have hentryEndpoints : b.orderSequence.entryOrZero i.val =
        b.orderSequence.entryOrZero j.val := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega),
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
      exact horder
    have hiNext := b.orderSequence.entryOrZero_le_of_evenGap
      i.val (k.val + 1) (by omega) (by omega) ⟨t, by
        rw [hnextIndex]
        omega⟩
    have hnextJ := b.orderSequence.entryOrZero_le_of_evenGap
      (k.val + 1) j.val (by omega) (by omega) ⟨d - t, by
        rw [hnextIndex]
        omega⟩
    have hkNextEntry : b.orderSequence.entryOrZero (k.val + 1) =
        b.orderSequence.entryOrZero i.val := by
      omega
    have hkNextOrder : b.order k.succ = b.order i.castSucc := by
      exact (b.orderSequence_entryOrZero_eq_order k.succ).symm.trans
        (hkNextEntry.trans
          (b.orderSequence_entryOrZero_eq_order i.castSucc))
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousK
    have hcriticalQ :
        ((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
            b.alphaValue previous ≤
          ((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
            b.alphaValue k := by
      unfold alphaLeftEndpoint at hendpoint
      push_cast at hendpoint ⊢
      have hpreviousSuccQ : (b.order previous.succ : ℚ) =
          (b.order i.castSucc : ℚ) := by
        exact_mod_cast hpreviousSucc
      have hkNextOrderQ : (b.order k.succ : ℚ) =
          (b.order i.castSucc : ℚ) := by
        exact_mod_cast hkNextOrder
      linarith
    have hcriticalTop : critical ≤
        (((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
          b.alphaValue k : ℚ)) : WithTop ℚ) := by
      simpa only [critical] using WithTop.coe_le_coe.mpr hcriticalQ
    exact hcriticalTop.trans
      (b.order_sub_add_alpha_le_cappedAdjacent k)
  have hsegment := b.truncatedPrefixDefect_alternating_ge
    (i.val - 1) d (by omega) critical hlocal
  rw [hpairs, ← hend]
  exact hsegment

/-- Beli (2019), Lemma 7.4(iii).  The two conjunctions state the two
three-term equality chains in the order used in the paper. -/
theorem beli2019Lemma74_iii
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1))
    (hij : i < j) (heven : Even (j.val - i.val))
    (horder : b.order i.castSucc = b.order j.castSucc) :
    let jPrevious : Fin (n + 1) := ⟨j.val - 2, by omega⟩
    let jMiddle : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    let iNext : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    let leftCritical : ℚ :=
      ((b.order jPrevious.castSucc - b.order jPrevious.succ : Int) : ℚ) +
        b.alphaValue jPrevious
    let rightCritical : ℚ :=
      ((b.order iNext.castSucc - b.order iNext.succ : Int) : ℚ) +
        b.alphaValue iNext
    (b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          i.val j.val = (leftCritical : WithTop ℚ) ∧
        leftCritical = b.alphaValue jMiddle) ∧
      (b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          (i.val + 1) (j.val + 1) = (rightCritical : WithTop ℚ) ∧
        rightCritical = b.alphaValue i) := by
  dsimp only
  rcases heven with ⟨d, hd⟩
  have hjFormula : j.val = i.val + 2 * d := by omega
  have hdPos : 0 < d := by omega
  let jPrevious : Fin (n + 1) := ⟨j.val - 2, by omega⟩
  let jMiddle : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let iNext : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  let iAfterTwo : Fin (n + 1) := ⟨i.val + 2, by omega⟩
  let leftCritical : ℚ :=
    ((b.order jPrevious.castSucc - b.order jPrevious.succ : Int) : ℚ) +
      b.alphaValue jPrevious
  let rightCritical : ℚ :=
    ((b.order iNext.castSucc - b.order iNext.succ : Int) : ℚ) +
      b.alphaValue iNext
  have hpreviousOrder :
      b.order jPrevious.castSucc = b.order j.castSucc := by
    apply b.order_eq_of_evenGap_between_equal
      i.castSucc jPrevious.castSucc j.castSucc
    · change i.val ≤ jPrevious.val
      simp only [jPrevious]
      omega
    · change jPrevious.val ≤ j.val
      simp only [jPrevious]
      omega
    · change Even (jPrevious.val - i.val)
      refine ⟨d - 1, ?_⟩
      simp only [jPrevious]
      omega
    · change Even (j.val - jPrevious.val)
      refine ⟨1, ?_⟩
      simp only [jPrevious]
      omega
    · exact horder
  have hafterTwoOrder :
      b.order iAfterTwo.castSucc = b.order j.castSucc := by
    apply b.order_eq_of_evenGap_between_equal
      i.castSucc iAfterTwo.castSucc j.castSucc
    · change i.val ≤ iAfterTwo.val
      simp only [iAfterTwo]
      omega
    · change iAfterTwo.val ≤ j.val
      simp only [iAfterTwo]
      omega
    · change Even (iAfterTwo.val - i.val)
      refine ⟨1, ?_⟩
      simp only [iAfterTwo]
      omega
    · change Even (j.val - iAfterTwo.val)
      refine ⟨d - 1, ?_⟩
      simp only [iAfterTwo]
      omega
    · exact horder
  have hleftOrder :
      b.order i.castSucc = b.order jPrevious.castSucc :=
    horder.trans hpreviousOrder.symm
  have hleftLowerRaw := b.beli2019Lemma74_i i jPrevious
    (by change i.val ≤ jPrevious.val; simp only [jPrevious]; omega)
    (by
      change Even (jPrevious.val - i.val)
      refine ⟨d - 1, ?_⟩
      simp only [jPrevious]
      omega)
    hleftOrder
  have hleftExponent :
      (jPrevious.val - i.val + 2) / 2 = (j.val - i.val) / 2 := by
    simp only [jPrevious]
    omega
  have hleftEnd : jPrevious.val + 2 = j.val := by
    simp only [jPrevious]
    omega
  rw [hleftExponent, hleftEnd] at hleftLowerRaw
  have hleftLower :
      (leftCritical : WithTop ℚ) ≤
        b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          i.val j.val := by
    change (leftCritical : WithTop ℚ) ≤ _ at hleftLowerRaw
    exact hleftLowerRaw
  have hleftUpperRaw := b.truncatedPrefixDefect_le_rightCap b
    ((-1) ^ ((j.val - i.val) / 2)) i.val j.val
  rw [b.prefixAlphaCap_of_internal (i := j.val) (by omega) (by omega)]
    at hleftUpperRaw
  have hleftUpper :
      b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          i.val j.val ≤ (b.alphaValue jMiddle : WithTop ℚ) := by
    simpa only [jMiddle] using hleftUpperRaw
  have hpreviousSucc : jPrevious.succ = jMiddle.castSucc := by
    apply Fin.ext
    simp only [jPrevious, jMiddle, Fin.val_succ, Fin.val_castSucc]
    omega
  have hmiddleSucc : jMiddle.succ = j.castSucc := by
    apply Fin.ext
    simp only [jMiddle, Fin.val_succ, Fin.val_castSucc]
    omega
  have hleftSum :
      b.adjacentOrderSum jPrevious = b.adjacentOrderSum jMiddle := by
    unfold adjacentOrderSum
    rw [hpreviousSucc, hmiddleSucc, hpreviousOrder]
    omega
  have hleftEndpoint :=
    (b.beli2009Corollary23 jPrevious jMiddle
      (by change jPrevious.val ≤ jMiddle.val;
          simp only [jPrevious, jMiddle]; omega) hleftSum).leftEndpoint_eq
      jMiddle
      (by change jPrevious.val ≤ jMiddle.val;
          simp only [jPrevious, jMiddle]; omega)
      le_rfl
  have hleftBridge : b.order jPrevious.succ =
      b.order jMiddle.castSucc := congrArg b.order hpreviousSucc
  have hleftBridgeQ : (b.order jPrevious.succ : ℚ) =
      (b.order jMiddle.castSucc : ℚ) := by
    exact_mod_cast hleftBridge
  have hleftCritical : leftCritical = b.alphaValue jMiddle := by
    unfold alphaLeftEndpoint at hleftEndpoint
    dsimp only [leftCritical]
    push_cast at hleftEndpoint ⊢
    linarith
  have hleftDefect :
      b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          i.val j.val = (leftCritical : WithTop ℚ) := by
    apply le_antisymm
    · rw [hleftCritical]
      exact hleftUpper
    · exact hleftLower
  have hrightLowerRaw := b.beli2019Lemma74_ii iAfterTwo j
    (by change iAfterTwo.val ≤ j.val; simp only [iAfterTwo]; omega)
    (by simp only [iAfterTwo]; omega)
    (by
      change Even (j.val - iAfterTwo.val)
      refine ⟨d - 1, ?_⟩
      simp only [iAfterTwo]
      omega)
    hafterTwoOrder
  dsimp only at hrightLowerRaw
  have hrightExponent :
      (j.val - iAfterTwo.val + 2) / 2 = (j.val - i.val) / 2 := by
    simp only [iAfterTwo]
    omega
  have hrightStart : iAfterTwo.val - 1 = i.val + 1 := by
    simp only [iAfterTwo]
    omega
  rw [hrightExponent] at hrightLowerRaw
  simp only [hrightStart] at hrightLowerRaw
  have hrightLower :
      (rightCritical : WithTop ℚ) ≤
        b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          (i.val + 1) (j.val + 1) := by
    change (rightCritical : WithTop ℚ) ≤ _ at hrightLowerRaw
    exact hrightLowerRaw
  have hrightUpperRaw := b.truncatedPrefixDefect_le_leftCap b
    ((-1) ^ ((j.val - i.val) / 2)) (i.val + 1) (j.val + 1)
  rw [b.prefixAlphaCap_of_internal (i := i.val + 1)
    (by omega) (by omega)] at hrightUpperRaw
  have hrightUpper :
      b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          (i.val + 1) (j.val + 1) ≤
        (b.alphaValue i : WithTop ℚ) := by
    let iCap : Fin (n + 1) := ⟨i.val + 1 - 1, by omega⟩
    change _ ≤ (b.alphaValue iCap : WithTop ℚ) at hrightUpperRaw
    have hiCap : iCap = i := by
      apply Fin.ext
      simp only [iCap]
      omega
    rwa [hiCap] at hrightUpperRaw
  have hcurrentSucc : i.succ = iNext.castSucc := by
    apply Fin.ext
    simp only [iNext, Fin.val_succ, Fin.val_castSucc]
  have hnextSucc : iNext.succ = iAfterTwo.castSucc := by
    apply Fin.ext
    simp only [iNext, iAfterTwo, Fin.val_succ, Fin.val_castSucc]
  have hbaseAfter :
      b.order i.castSucc = b.order iAfterTwo.castSucc :=
    horder.trans hafterTwoOrder.symm
  have hrightSum :
      b.adjacentOrderSum i = b.adjacentOrderSum iNext := by
    unfold adjacentOrderSum
    rw [hcurrentSucc, hnextSucc, hbaseAfter]
    omega
  have hrightEndpoint :=
    (b.beli2009Corollary23 i iNext
      (by change i.val ≤ iNext.val; simp only [iNext]; omega)
      hrightSum).rightEndpoint_eq iNext
      (by change i.val ≤ iNext.val; simp only [iNext]; omega)
      le_rfl
  have hrightBridge : b.order i.succ =
      b.order iNext.castSucc := congrArg b.order hcurrentSucc
  have hrightBridgeQ : (b.order i.succ : ℚ) =
      (b.order iNext.castSucc : ℚ) := by
    exact_mod_cast hrightBridge
  have hrightCritical : rightCritical = b.alphaValue i := by
    unfold alphaRightEndpoint at hrightEndpoint
    dsimp only [rightCritical]
    push_cast at hrightEndpoint ⊢
    linarith
  have hrightDefect :
      b.truncatedPrefixDefect b ((-1) ^ ((j.val - i.val) / 2))
          (i.val + 1) (j.val + 1) =
        (rightCritical : WithTop ℚ) := by
    apply le_antisymm
    · rw [hrightCritical]
      exact hrightUpper
    · exact hrightLower
  change
    (_ = (leftCritical : WithTop ℚ) ∧
        leftCritical = b.alphaValue jMiddle) ∧
      (_ = (rightCritical : WithTop ℚ) ∧
        rightCritical = b.alphaValue i)
  exact ⟨⟨hleftDefect, hleftCritical⟩,
    ⟨hrightDefect, hrightCritical⟩⟩

end BONG.GoodBONG

end Bong
