/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74

/-!
# Beli (2019), Lemma 7.4(ii) through the terminal boundary

The original finite-index statement stops one entry before a full-rank
segment.  This natural-index form keeps the same proof and permits the final
order coordinate as the right endpoint.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Lemma 7.4(ii), allowing the segment to end at the full-rank boundary. -/
theorem beli2019Lemma74_ii_nat
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Nat)
    (hij : i ≤ j) (hipos : 0 < i)
    (hiBound : i < n + 2) (hjBound : j < n + 2)
    (heven : Even (j - i))
    (horder : b.order ⟨i, hiBound⟩ = b.order ⟨j, hjBound⟩) :
    let previous : Fin (n + 1) := ⟨i - 1, by omega⟩
    (((((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
        b.alphaValue previous : ℚ)) : WithTop ℚ) ≤
      b.truncatedPrefixDefect b
        ((-1) ^ ((j - i + 2) / 2)) (i - 1) (j + 1) := by
  dsimp only
  rcases heven with ⟨d, hd⟩
  have hjFormula : j = i + 2 * d := by omega
  have hpairs : (j - i + 2) / 2 = d + 1 := by omega
  have hend : i - 1 + 2 * (d + 1) = j + 1 := by omega
  let previous : Fin (n + 1) := ⟨i - 1, by omega⟩
  let critical : WithTop ℚ :=
    ((((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
      b.alphaValue previous : ℚ) : WithTop ℚ)
  have hpreviousSucc : b.order previous.succ = b.order ⟨i, hiBound⟩ := by
    apply congrArg b.order
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hlocal (t : Nat) (ht : t ≤ d) :
      critical ≤ b.truncatedPrefixDefect b (-1)
        (i - 1 + 2 * t) (i - 1 + 2 * t + 2) := by
    let k : Fin (n + 1) := ⟨i - 1 + 2 * t, by omega⟩
    have hpreviousK : previous ≤ k := by
      change previous.val ≤ k.val
      simp only [previous, k]
      omega
    have hnextIndex : k.val + 1 = i + 2 * t := by
      simp only [k]
      omega
    have hentryEndpoints : b.orderSequence.entryOrZero i =
        b.orderSequence.entryOrZero j := by
      rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hiBound,
        BeliOrderSequence.entryOrZero_of_lt b.orderSequence hjBound]
      exact horder
    have hiNext := b.orderSequence.entryOrZero_le_of_evenGap
      i (k.val + 1) (by omega) (by omega) ⟨t, by
        rw [hnextIndex]
        omega⟩
    have hnextJ := b.orderSequence.entryOrZero_le_of_evenGap
      (k.val + 1) j (by omega) hjBound ⟨d - t, by
        rw [hnextIndex]
        omega⟩
    have hkNextEntry : b.orderSequence.entryOrZero (k.val + 1) =
        b.orderSequence.entryOrZero i := by
      omega
    have hkNextOrder : b.order k.succ = b.order ⟨i, hiBound⟩ := by
      exact (b.orderSequence_entryOrZero_eq_order k.succ).symm.trans
        (hkNextEntry.trans
          (b.orderSequence_entryOrZero_eq_order ⟨i, hiBound⟩))
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousK
    have hcriticalQ :
        ((b.order previous.castSucc - b.order previous.succ : Int) : ℚ) +
            b.alphaValue previous ≤
          ((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
            b.alphaValue k := by
      unfold alphaLeftEndpoint at hendpoint
      push_cast at hendpoint ⊢
      have hpreviousSuccQ : (b.order previous.succ : ℚ) =
          (b.order ⟨i, hiBound⟩ : ℚ) := by
        exact_mod_cast hpreviousSucc
      have hkNextOrderQ : (b.order k.succ : ℚ) =
          (b.order ⟨i, hiBound⟩ : ℚ) := by
        exact_mod_cast hkNextOrder
      linarith
    have hcriticalTop : critical ≤
        (((((b.order k.castSucc - b.order k.succ : Int) : ℚ) +
          b.alphaValue k : ℚ)) : WithTop ℚ) := by
      simpa only [critical] using WithTop.coe_le_coe.mpr hcriticalQ
    exact hcriticalTop.trans
      (b.order_sub_add_alpha_le_cappedAdjacent k)
  have hsegment := b.truncatedPrefixDefect_alternating_ge
    (i - 1) d (by omega) critical hlocal
  rw [hpairs, ← hend]
  exact hsegment

end BONG.GoodBONG

end Bong
