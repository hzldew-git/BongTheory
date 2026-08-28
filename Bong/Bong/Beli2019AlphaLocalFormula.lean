/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaCompression
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Remark 1.1: the local formula for `alpha`

Beli's bracketed adjacent defect absorbs the two neighboring alpha terms in
Corollary 2.5(i).  Consequently `alpha_i` is the minimum of the half-gap term
and the order gap plus that capped defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Beli (2019), Remark 1.1:
`alpha_i = min ((R_(i+1)-R_i)/2+e)
  (R_(i+1)-R_i+d[-a_(i,i+1)])`. -/
theorem alpha_eq_min_halfGap_add_cappedAdjacent_of_succ
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (((((b.order i.succ - b.order i.castSucc : Int) : ℚ)) :
            WithTop ℚ) +
          b.truncatedPrefixDefect b (-1) i.val (i.val + 2)) := by
  let shift : ℚ :=
    ((b.order i.succ - b.order i.castSucc : Int) : ℚ)
  have hhalf : b.alpha i ≤ b.halfGapCandidate i :=
    b.alpha_le_halfGapCandidate i
  have hcapped : b.alpha i ≤
      (shift : WithTop ℚ) +
        b.truncatedPrefixDefect b (-1) i.val (i.val + 2) := by
    rw [← b.coe_alphaValue]
    simpa only [shift] using b.alpha_le_orderGap_add_cappedAdjacent i
  rw [b.coe_alphaValue]
  apply le_antisymm
  · exact le_min hhalf hcapped
  · rw [b.beli2009Corollary25_i i]
    apply Finset.le_min'
    intro y hy
    simp only [recursiveAlphaCandidates, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · exact min_le_left _ _
    · refine (min_le_right _ _).trans ?_
      unfold leftDefectCandidate
      have hraw := b.truncatedPrefixDefect_le_defect b (-1)
        i.val (i.val + 2)
      rw [b.defectOrder_prefixPair_eq_adjacentDefect i] at hraw
      simpa only [shift, add_comm] using
        add_le_add_left hraw (shift : WithTop ℚ)
    · unfold neighborAlphaCandidates at hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      rcases (Finset.mem_filter.mp hj).2 with hprevious | hnext
      · have hcap : b.prefixAlphaCap i.val =
            (b.alphaValue j : WithTop ℚ) := by
          rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
          have hindex : (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = j := by
            apply Fin.ext
            change i.val - 1 = j.val
            omega
          rw [hindex]
        have hdefect : b.truncatedPrefixDefect b (-1)
            i.val (i.val + 2) ≤ (b.alphaValue j : WithTop ℚ) := by
          rw [← hcap]
          exact b.truncatedPrefixDefect_le_leftCap b (-1)
            i.val (i.val + 2)
        refine (min_le_right _ _).trans ?_
        unfold neighborAlphaCandidate alphaGapValue
        simpa only [shift, WithTop.coe_add, add_comm] using
          add_le_add_left hdefect (shift : WithTop ℚ)
      · have hcap : b.prefixAlphaCap (i.val + 2) =
            (b.alphaValue j : WithTop ℚ) := by
          rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
          have hindex : (⟨i.val + 2 - 1, by omega⟩ : Fin (n + 1)) = j := by
            apply Fin.ext
            change i.val + 2 - 1 = j.val
            omega
          rw [hindex]
        have hdefect : b.truncatedPrefixDefect b (-1)
            i.val (i.val + 2) ≤ (b.alphaValue j : WithTop ℚ) := by
          rw [← hcap]
          exact b.truncatedPrefixDefect_le_rightCap b (-1)
            i.val (i.val + 2)
        refine (min_le_right _ _).trans ?_
        unfold neighborAlphaCandidate alphaGapValue
        simpa only [shift, WithTop.coe_add, add_comm] using
          add_le_add_left hdefect (shift : WithTop ℚ)

/-- The same local formula at an arbitrary nonempty alpha index type. -/
theorem alpha_eq_min_halfGap_add_cappedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (((((b.order i.succ - b.order i.castSucc : Int) : ℚ)) :
            WithTop ℚ) +
          b.truncatedPrefixDefect b (-1) i.val (i.val + 2)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ k => exact b.alpha_eq_min_halfGap_add_cappedAdjacent_of_succ i

end BONG.GoodBONG

end Bong
