/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationAlphaDual

/-!
# Beli (2019): reverse-duality of condition 2.1(ii)

The representation alpha and the equal-boundary capped comparison defect
both agree at complementary boundaries.  Therefore condition 2.1(ii) is
preserved when equal-rank source and target BONGs are reverse-dualized and
swapped.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Condition 2.1(ii) is transported to a swapped reverse-dual pair. -/
theorem representationDefectCondition_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (hCondition : a.RepresentationDefectCondition b) :
    bDual.RepresentationDefectCondition aDual := by
  intro j
  let i := j.reverse
  have hAlpha := a.representationAlphaValue_reverseDual_swap
    b aDual bDual haOrders hbOrders hDefect i
  have hrev : i.reverse = j := by
    dsimp only [i]
    exact j.reverse_reverse
  rw [hrev] at hAlpha
  have hOriginal := hCondition i
  have hComparison := hDefect j.val j.val
    (Nat.le_of_lt j.lt_large) (Nat.le_of_lt j.lt_large) 1
  rw [hAlpha, hComparison]
  simpa only [i, RepresentationIndex.reverse_val] using hOriginal

/-- Reverse-dual BONGs can be selected so that condition 2.1(ii) holds for
the swapped pair and all order, alpha, and capped-defect identities remain
available to later dual arguments. -/
theorem exists_reverseDualPair_with_representationDefectCondition
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hCondition : a.RepresentationDefectCondition b) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1)),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 → ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p)) ∧
      bDual.RepresentationDefectCondition aDual := by
  rcases a.exists_reverseDualPair_with_truncatedPrefixDefect b with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, hDefect⟩
  refine ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha,
    hDefect, ?_⟩
  exact a.representationDefectCondition_reverseDual_swap b aDual bDual
    haOrders hbOrders hDefect hCondition

end BONG.GoodBONG

end Bong
