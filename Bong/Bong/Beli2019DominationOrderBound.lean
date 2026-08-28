/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DominationWitness
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019): the order form of the domination witness

Remark 1.1 bounds the defect of the selected adjacent pair by its order
difference and alpha.  Antitonicity of the right alpha endpoint transports
that alpha to the last boundary of the alternating prefix.  This is the
precise inequality denoted by the domination principle in Lemma 7.9(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Remark 1.1 gives the raw adjacent-defect lower bound after removing
the two prefix caps. -/
theorem order_sub_add_alpha_le_adjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (j : Fin (n + 1)) :
    (((((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
        b.alphaValue j : ℚ)) : WithTop ℚ) ≤
      b.adjacentDefect j := by
  have hcapped := b.order_sub_add_alpha_le_cappedAdjacent j
  have hraw := b.truncatedPrefixDefect_le_defect
    b (-1) j.val (j.val + 2)
  rw [b.defectOrder_prefixPair_eq_adjacentDefect j] at hraw
  exact hcapped.trans hraw

/-- The witness form used in the paper: some even zero-based pair start
`j` satisfies
`d[-c_(j+1)c_(j+2)] ≥ T_(j+1)-T_i+gamma_(i-1)`. -/
theorem exists_even_domination_order_bound
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hiPos : 0 < i) (hiBound : i ≤ n + 2) (hiEven : Even i) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < i ∧
      (((((b.order j.castSucc -
          b.order ⟨i - 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i - 2, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        b.alternatingPrefixDefect i := by
  rcases b.exists_even_adjacentDefect_le_alternatingPrefixDefect
      i hiPos hiBound hiEven with ⟨j, hjEven, hjlt, hjDefect⟩
  let last : Fin (n + 1) := ⟨i - 2, by omega⟩
  have hjLast : j ≤ last := by
    change j.val ≤ last.val
    simp only [last]
    omega
  have hendpoint := b.alphaRightEndpoint_antitone hjLast
  have hlastSucc : last.succ =
      (⟨i - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  have hlastAlpha : b.alphaValue last =
      b.alphaValue ⟨i - 2, by omega⟩ := by
    congr 1
  have horderBound :
      ((b.order j.castSucc - b.order ⟨i - 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i - 2, by omega⟩ ≤
        ((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
          b.alphaValue j := by
    unfold alphaRightEndpoint at hendpoint
    rw [hlastSucc, hlastAlpha] at hendpoint
    push_cast
    linarith
  have horderBoundTop :
      (((((b.order j.castSucc -
          b.order ⟨i - 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i - 2, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        (((((b.order j.castSucc - b.order j.succ : Int) : ℚ) +
          b.alphaValue j : ℚ)) : WithTop ℚ) := by
    exact_mod_cast horderBound
  refine ⟨j, hjEven, hjlt, horderBoundTop.trans ?_⟩
  exact (b.order_sub_add_alpha_le_adjacentDefect j).trans hjDefect

end BONG.GoodBONG

end Bong
