/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Remark 1.1 along a left alpha interval

The local capped defect at any earlier adjacent pair remains a valid
candidate for a later alpha value.  This is the propagation form of
Remark 1.1 used repeatedly in the proof of Lemma 6.9.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Remark 1.1 with an arbitrary earlier adjacent pair. -/
theorem alpha_le_order_sub_add_cappedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) {i j : Fin n} (hji : j ≤ i) :
    (a.alphaValue i : WithTop ℚ) ≤
      ((((a.order i.succ - a.order j.castSucc : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) j.val (j.val + 2)) := by
  by_cases heq : j = i
  · subst j
    simpa only [] using a.alpha_le_orderGap_add_cappedAdjacent i
  · have hlt : j < i := lt_of_le_of_ne hji heq
    have hrightAnti : Antitone a.alphaRightEndpoint := by
      cases n with
      | zero =>
          intro x
          exact Fin.elim0 x
      | succ n =>
          exact a.alphaRightEndpoint_antitone
    let shift : ℚ :=
      ((a.order i.succ - a.order j.castSucc : Int) : ℚ)
    have hraw : (a.alphaValue i : WithTop ℚ) ≤
        (shift : WithTop ℚ) +
          defectOrder (K := K)
            ((-1) * a.prefixProduct j.val *
              a.prefixProduct (j.val + 2)) := by
      rw [a.defectOrder_prefixPair_eq_adjacentDefect j]
      rw [a.coe_alphaValue]
      simpa only [shift, leftDefectCandidate] using
        (a.alpha_le_leftDefectCandidate (i := i) (j := j) hji)
    have hleft : (a.alphaValue i : WithTop ℚ) ≤
        (shift : WithTop ℚ) + a.prefixAlphaCap j.val := by
      by_cases hj0 : j.val = 0
      · rw [hj0, a.prefixAlphaCap_zero]
        simp
      · let previous : Fin n := ⟨j.val - 1, by omega⟩
        rw [a.prefixAlphaCap_of_internal (Nat.pos_of_ne_zero hj0)
          (by omega)]
        have hpreviousI : previous ≤ i := by
          change previous.val ≤ i.val
          simp only [previous]
          omega
        have hmono := hrightAnti hpreviousI
        have hindex : previous.succ = j.castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc, previous]
          omega
        unfold alphaRightEndpoint at hmono
        rw [hindex] at hmono
        have hrational : a.alphaValue i ≤
            shift + a.alphaValue previous := by
          dsimp only [shift]
          push_cast
          linarith
        exact_mod_cast hrational
    have hright : (a.alphaValue i : WithTop ℚ) ≤
        (shift : WithTop ℚ) + a.prefixAlphaCap (j.val + 2) := by
      let next : Fin n := ⟨j.val + 1, by omega⟩
      rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
      have hnextI : next ≤ i := by
        change next.val ≤ i.val
        simp only [next]
        omega
      have hmono := hrightAnti hnextI
      have hnextSucc : next.succ =
          (⟨j.val + 2, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      have hcapIndex :
          (⟨j.val + 2 - 1, by omega⟩ : Fin n) = next := by
        apply Fin.ext
        simp only [next]
        omega
      rw [hcapIndex]
      unfold alphaRightEndpoint at hmono
      rw [hnextSucc] at hmono
      let k : Fin (n + 1) := ⟨j.val, by omega⟩
      have hgood := a.good k (by simp only [k]; omega)
      have horder : a.order j.castSucc ≤ a.order next.succ := by
        change a.order j.castSucc ≤ a.order next.succ at hgood
        exact hgood
      have hrational : a.alphaValue i ≤
          shift + a.alphaValue next := by
        dsimp only [shift]
        push_cast at hmono ⊢
        have horderQ : (a.order j.castSucc : ℚ) ≤
            (a.order next.succ : ℚ) := by
          exact_mod_cast horder
        rw [hnextSucc] at horderQ
        linarith
      exact_mod_cast hrational
    change (a.alphaValue i : WithTop ℚ) ≤
      (shift : WithTop ℚ) +
        min (defectOrder (K := K)
          ((-1) * a.prefixProduct j.val *
            a.prefixProduct (j.val + 2)))
          (min (a.prefixAlphaCap j.val)
            (a.prefixAlphaCap (j.val + 2)))
    exact withTop_le_shift_add_min _ shift _ _ hraw
      (withTop_le_shift_add_min _ shift _ _ hleft hright)

end BONG.GoodBONG

end Bong
