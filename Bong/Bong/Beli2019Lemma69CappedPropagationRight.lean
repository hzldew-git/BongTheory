/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightTail

/-!
# Beli (2019), Remark 1.1 along a right alpha interval

The capped adjacent defect at a later pair remains a valid candidate for an
earlier alpha value.  This is the rightward counterpart of
`alpha_le_order_sub_add_cappedAdjacent`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Remark 1.1 with an arbitrary later adjacent pair. -/
theorem alpha_le_laterOrder_sub_add_cappedAdjacent
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) {i j : Fin n} (hij : i ≤ j) :
    (a.alphaValue i : WithTop ℚ) ≤
      ((((a.order j.succ - a.order i.castSucc : Int) : ℚ) :
          WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) j.val (j.val + 2)) := by
  let leftShift : ℚ :=
    ((a.order j.castSucc - a.order i.castSucc : Int) : ℚ)
  let gapShift : ℚ :=
    ((a.order j.succ - a.order j.castSucc : Int) : ℚ)
  let totalShift : ℚ :=
    ((a.order j.succ - a.order i.castSucc : Int) : ℚ)
  let capped : WithTop ℚ :=
    a.truncatedPrefixDefect a (-1) j.val (j.val + 2)
  change (a.alphaValue i : WithTop ℚ) ≤
    (totalShift : WithTop ℚ) + capped
  have hmono : a.alphaLeftEndpoint i ≤ a.alphaLeftEndpoint j := by
    have hiter : ∀ (m : Nat) (him : i.val ≤ m) (hm : m < n),
        a.alphaLeftEndpoint i ≤
          a.alphaLeftEndpoint (⟨m, hm⟩ : Fin n) := by
      intro m him
      induction m, him using Nat.le_induction with
      | base =>
          intro hm
          have heq : (⟨i.val, hm⟩ : Fin n) = i := by
            apply Fin.ext
            rfl
          rw [heq]
      | succ m him ih =>
          intro hmSucc
          have hm : m < n := by omega
          exact (ih hm).trans (a.alpha_p1 ⟨m, hm⟩ hmSucc).1
    exact hiter j.val hij j.isLt
  unfold alphaLeftEndpoint at hmono
  have hleft : a.alphaValue i ≤ leftShift + a.alphaValue j := by
    dsimp only [leftShift]
    push_cast
    linarith
  have hleftTop : (a.alphaValue i : WithTop ℚ) ≤
      (leftShift : WithTop ℚ) + a.alphaValue j := by
    exact_mod_cast hleft
  have hadjacent := a.alpha_le_orderGap_add_cappedAdjacent j
  have hadjacent' : (a.alphaValue j : WithTop ℚ) ≤
      (gapShift : WithTop ℚ) + capped := by
    simpa only [gapShift, capped] using hadjacent
  have hshift : totalShift = leftShift + gapShift := by
    dsimp only [totalShift, leftShift, gapShift]
    push_cast
    ring
  have hshiftTop : (totalShift : WithTop ℚ) =
      (leftShift : WithTop ℚ) + gapShift := by
    simpa using congrArg (fun x : ℚ => (x : WithTop ℚ)) hshift
  rw [hshiftTop]
  calc
    (a.alphaValue i : WithTop ℚ) ≤
        (leftShift : WithTop ℚ) + a.alphaValue j := hleftTop
    _ ≤ (leftShift : WithTop ℚ) +
        ((gapShift : WithTop ℚ) + capped) :=
      by
        simpa only [add_comm] using
          add_le_add_left hadjacent' (leftShift : WithTop ℚ)
    _ = ((leftShift : WithTop ℚ) + (gapShift : WithTop ℚ)) +
        capped :=
      (add_assoc (leftShift : WithTop ℚ) (gapShift : WithTop ℚ)
        capped).symm

end BONG.GoodBONG

end Bong
