/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIThirdPrefix
import Bong.Bong.Beli2019DominationOrderBound
import Bong.Bong.Beli2019CappedDominationWitness

/-!
# Beli (2019), Lemma 7.9(ii), case 6: extended domination

The ordinary domination witness transports its alpha endpoint to the final
gap inside an even prefix.  Case 6 needs one further gap: the prefix ends at
`length`, while the coefficient uses the order at `length` and the alpha at
`length - 1`.  Right-endpoint antitonicity supplies this extension.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Domination for an even prefix, with its order-alpha coefficient
transported through the immediately following endpoint. -/
theorem exists_even_domination_order_bound_through_next
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q L (n + 2)) (length : Nat)
    (hlengthPos : 0 < length) (hnextBound : length < n + 2)
    (hlengthEven : Even length) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < length ∧
      (((((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        c.alternatingPrefixDefect length := by
  rcases c.exists_even_adjacentDefect_le_alternatingPrefixDefect
      length hlengthPos hnextBound.le hlengthEven with
    ⟨j, hjEven, hjlt, hjDefect⟩
  let last : Fin (n + 1) := ⟨length - 1, by omega⟩
  have hjLast : j ≤ last := by
    change j.val ≤ last.val
    simp only [last]
    omega
  have hendpoint := c.alphaRightEndpoint_antitone hjLast
  have hlastSucc : last.succ =
      (⟨length, hnextBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  have hlastAlpha : c.alphaValue last =
      c.alphaValue ⟨length - 1, by omega⟩ := by
    congr 1
  have horderBound :
      ((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ ≤
        ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j := by
    unfold alphaRightEndpoint at hendpoint
    rw [hlastSucc, hlastAlpha] at hendpoint
    push_cast
    linarith
  have horderBoundTop :
      (((((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        (((((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j : ℚ)) : WithTop ℚ) := by
    exact_mod_cast horderBound
  refine ⟨j, hjEven, hjlt, horderBoundTop.trans ?_⟩
  exact (c.order_sub_add_alpha_le_adjacentDefect j).trans hjDefect

/-- Capped form of the preceding extension.  This is the form that can be
rewritten by the exact capped prefix identity obtained from Lemma 7.8. -/
theorem exists_even_capped_domination_order_bound_through_next
    [Beli2006AlphaLaws.{u, v} K]
    (c : GoodBONG q L (n + 2)) (length : Nat)
    (hlengthPos : 0 < length) (hnextBound : length < n + 2)
    (hlengthEven : Even length) :
    ∃ j : Fin (n + 1), Even j.val ∧ j.val + 1 < length ∧
      c.truncatedPrefixDefect c (-1) j.val (j.val + 2) ≤
        c.truncatedPrefixDefect c ((-1) ^ (length / 2)) 0 length ∧
      (((((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        c.truncatedPrefixDefect c ((-1) ^ (length / 2)) 0 length := by
  rcases c.exists_even_cappedAdjacent_le_alternatingPrefix
      length hlengthPos hnextBound.le hlengthEven with
    ⟨j, hjEven, hjlt, hjDefect⟩
  let last : Fin (n + 1) := ⟨length - 1, by omega⟩
  have hjLast : j ≤ last := by
    change j.val ≤ last.val
    simp only [last]
    omega
  have hendpoint := c.alphaRightEndpoint_antitone hjLast
  have hlastSucc : last.succ =
      (⟨length, hnextBound⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  have hlastAlpha : c.alphaValue last =
      c.alphaValue ⟨length - 1, by omega⟩ := by
    congr 1
  have horderBound :
      ((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ ≤
        ((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j := by
    unfold alphaRightEndpoint at hendpoint
    rw [hlastSucc, hlastAlpha] at hendpoint
    push_cast
    linarith
  have horderBoundTop :
      (((((c.order j.castSucc - c.order ⟨length, hnextBound⟩ : Int) : ℚ) +
          c.alphaValue ⟨length - 1, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        (((((c.order j.castSucc - c.order j.succ : Int) : ℚ) +
          c.alphaValue j : ℚ)) : WithTop ℚ) := by
    exact_mod_cast horderBound
  refine ⟨j, hjEven, hjlt, hjDefect, horderBoundTop.trans ?_⟩
  exact (c.order_sub_add_alpha_le_cappedAdjacent j).trans hjDefect

end BONG.GoodBONG

end Bong
