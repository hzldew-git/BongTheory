/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79NextAlpha
import Bong.Bong.Beli2019Lemma69TypeIIITargetLocal

/-!
# Beli (2019), Lemma 6.9(i): local type-III target left alphas

The target alpha at the centre is supplied by the local reverse-dual theorem.
Endpoint monotonicity then propagates the bound through the normalized left
profile without any condition on the final unequal coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Every even target alpha on the normalized type-III left interval is at
most one, without a full-rank hypothesis on the last difference. -/
theorem beli2019Lemma69_i_typeIII_targetLeftTail_local
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (k : Nat) (hk : k ≤ D.outer.transition.lastZero) (heven : Even k) :
    b.alphaValue ⟨k, by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega⟩ ≤ 1 := by
  let center : Fin (n + 1) := ⟨D.outer.transition.lastZero, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  let current : Fin (n + 1) := ⟨k, by
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega⟩
  have hcenterEven := D.outer.left_even_of_first_eq_zero hfirst
  have hcurrentOrder := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two k hk heven
  have hcenterOrder := D.outer.target_leftEven_eq_first_add_one
    hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hcenterEven
  have horders : b.order current.castSucc = b.order center.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order current.castSucc,
      ← b.orderSequence_entryOrZero_eq_order center.castSucc]
    change b.orderSequence.entryOrZero k =
      b.orderSequence.entryOrZero D.outer.transition.lastZero
    exact hcurrentOrder.trans hcenterOrder.symm
  have hmono := b.alphaLeftEndpoint_monotone
    (show current ≤ center by
      change k ≤ D.outer.transition.lastZero
      exact hk)
  unfold alphaLeftEndpoint at hmono
  rw [horders] at hmono
  have hcenterAlpha : b.alphaValue center ≤ 1 := by
    simpa only [center] using a.beli2019Lemma69_i_typeIII_target_local
      b D horder hdefect htotal
  have hcurrentAlpha : b.alphaValue current ≤ 1 := by
    linarith
  simpa only [current] using hcurrentAlpha

end BONG.GoodBONG

end Bong
