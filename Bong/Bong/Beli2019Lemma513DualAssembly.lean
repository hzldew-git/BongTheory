/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513
import Bong.Bong.Beli2019DefectConditionDual

/-!
# Beli (2019), Section 5.2: dual completion of Lemma 5.13

The calculation following Lemma 5.13 is performed only up to the selected
Jordan block.  Section 5.2 covers every remaining boundary by applying the
same calculation to the swapped reverse-dual pair.  This file packages that
logical assembly independently of the later Jordan calculations.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Pointwise proofs on a reduced original range and on a complementary
swapped reverse-dual range assemble to the full condition 2.1(ii). -/
theorem representationDefectCondition_of_reverseDual_cover
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
    (originalRange dualRange :
      RepresentationIndex (n + 1) (n + 1) → Prop)
    (originalAt : ∀ i, originalRange i →
      (a.representationAlphaValue b i : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 i.val i.val)
    (dualAt : ∀ j, dualRange j →
      (bDual.representationAlphaValue aDual j : WithTop ℚ) ≤
        bDual.truncatedPrefixDefect aDual 1 j.val j.val)
    (cover : ∀ i, originalRange i ∨ dualRange i.reverse) :
    a.RepresentationDefectCondition b := by
  intro i
  rcases cover i with hi | hi
  · exact originalAt i hi
  · have hDualAt := dualAt i.reverse hi
    have hAlpha := a.representationAlphaValue_reverseDual_swap
      b aDual bDual haOrders hbOrders hDefect i
    have hComparison := hDefect i.reverse.val i.reverse.val
      (Nat.le_of_lt i.reverse.lt_large)
      (Nat.le_of_lt i.reverse.lt_large) 1
    have hBoundary : n + 1 - i.reverse.val = i.val := by
      simp only [RepresentationIndex.reverse_val]
      have hpos := i.pos
      have hlt := i.lt_large
      omega
    rw [hBoundary] at hComparison
    rw [← hAlpha, ← hComparison]
    exact hDualAt

end BONG.GoodBONG

end Bong
