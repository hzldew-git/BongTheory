/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009TwoAdic
import Bong.Bong.BeliUniversalUnaryConditions

/-!
# Order arithmetic for universal dyadic lattices

This file proves Lemmas 2.5 and 2.12 of Beli's universal-forms paper.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Beli, Lemma 2.5: for an integral source, unary order condition (i) at
orders zero and one is equivalent to `R₁ = 0`. -/
theorem universalUnaryOrderConditions_iff_order_zero
    {m : Nat} (a : GoodBONG q L (m + 2))
    (hintegral : Lattice.IsIntegral q L) :
    (∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
      a.RepresentationOrderCondition (BONG.unaryModelGoodBONG b)
        (by omega)) ↔
      a.order 0 = 0 := by
  constructor
  · intro h
    have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      simp
    have hone := h (1 : Kˣ) (Or.inl honeOrder)
    have hle : a.order 0 ≤ 0 := by
      have hraw :=
        (a.unary_representationOrderCondition_iff (1 : Kˣ)).mp hone
      rw [honeOrder] at hraw
      exact hraw
    have hnonnegative : 0 ≤ a.order 0 :=
      (beliUniversalLemma22 a.toBONG).mp hintegral
    omega
  · intro hzero b hb
    rw [a.unary_representationOrderCondition_iff b, hzero]
    rcases hb with hb | hb
    · rw [hb]
    · rw [hb]
      omega

/-- The first assertion of Beli, Lemma 2.12: goodness gives `R₃ ≥ 0`
when `R₁ = 0`. -/
theorem order_two_nonnegative_of_order_zero_eq_zero
    {m : Nat} (a : GoodBONG q L (m + 3))
    (hzero : a.order 0 = 0) :
    0 ≤ a.order 2 := by
  have hgood := a.order_zero_le_two
  have hzero' : a.order (⟨0, by omega⟩ : Fin (m + 3)) = 0 := by
    simpa using hzero
  rw [hzero'] at hgood
  change 0 ≤ a.order (⟨2, by omega⟩ : Fin (m + 3))
  exact hgood

/-- The second assertion of Beli, Lemma 2.12: if also `R₂ = 1`, the
negative odd adjacent gap obstruction improves the bound to `R₃ ≥ 1`. -/
theorem one_le_order_two_of_order_zero_eq_zero_order_one_eq_one
    {m : Nat} (a : GoodBONG q L (m + 3))
    (hzero : a.order 0 = 0) (hone : a.order 1 = 1) :
    1 ≤ a.order 2 := by
  have hnonnegative := a.order_two_nonnegative_of_order_zero_eq_zero hzero
  by_contra hnot
  have htwo : a.order 2 = 0 := by omega
  let i : Fin (m + 2) := ⟨1, by omega⟩
  have hgap : a.orderGap i = -1 := by
    unfold orderGap
    simp [i, hone, htwo]
  have hnegative : a.orderGap i < 0 := by rw [hgap]; omega
  have heven := a.orderGap_even_of_negative i hnegative
  rw [hgap] at heven
  norm_num at heven

end BONG.GoodBONG

end Bong
