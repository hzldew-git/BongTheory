/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EvenComparisonDual
import Bong.Bong.Beli2019DefectConditionDual
import Bong.Bong.Beli2019OrderConditionDual

/-!
# Beli (2019), Proposition 6.2 in equal rank

Conditions 2.1(i) and 2.1(ii) give all even comparisons for `W(M), W(N)`.
The same conditions hold for the swapped reverse-dual pair, whose even
comparisons are precisely the missing odd comparisons.  Hence `W(M) ≤ W(N)`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Explicit reverse-dual order and alpha identities determine the whole
`W`-sequence. -/
theorem weightSequence_eq_reverseNegate_of_orders_alpha
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (horders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (halphas : ∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) :
    aDual.weightSequence = a.weightSequence.reverseNegate := by
  apply BeliOrderSequence.ext
  funext i
  rcases Nat.mod_two_eq_zero_or_one i.val with heven | hodd
  · let j : Fin n := ⟨i.val / 2, by omega⟩
    have hindex : i = ⟨2 * j.val, by
        simp only [j]
        omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    rw [aDual.weightSequence_even, horders j.castSucc, halphas j]
    unfold weightSequence
    rw [BeliOrderSequence.reverseNegate_interleave_value_even]
    simp only [alphaRightEndpoint]
    rw [Fin.rev_castSucc]
    push_cast
    ring
  · let j : Fin n := ⟨i.val / 2, by omega⟩
    have hindex : i = ⟨2 * j.val + 1, by
        simp only [j]
        omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex]
    rw [aDual.weightSequence_odd, horders j.succ, halphas j]
    unfold weightSequence
    rw [BeliOrderSequence.reverseNegate_interleave_value_odd]
    simp only [alphaLeftEndpoint]
    rw [Fin.rev_succ]
    push_cast
    ring

set_option maxHeartbeats 800000 in
-- Selecting a coherent dual pair and normalizing both `W` identities is elaboration-heavy.
/-- Beli (2019), Proposition 6.2 for equal-rank lattices. -/
theorem weightSequence_le_of_representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b) :
    BeliOrderLE a.weightSequence b.weightSequence := by
  have hEven := a.weightSequence_beliEvenLE b horder hdefect
  rcases a.exists_reverseDualPair_with_representationDefectCondition b
      hdefect with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, _, hdefectDual⟩
  have horderDual := a.representationOrderCondition_reverseDual_swap
    b aDual bDual haOrders hbOrders horder
  have hEvenDual := bDual.weightSequence_beliEvenLE aDual
    horderDual hdefectDual
  have haWeight := a.weightSequence_eq_reverseNegate_of_orders_alpha
    aDual haOrders haAlpha
  have hbWeight := b.weightSequence_eq_reverseNegate_of_orders_alpha
    bDual hbOrders hbAlpha
  rw [hbWeight, haWeight] at hEvenDual
  exact BeliEvenLE.to_beliOrderLE_of_reverseNegate hEven hEvenDual

end BONG.GoodBONG

end Bong
