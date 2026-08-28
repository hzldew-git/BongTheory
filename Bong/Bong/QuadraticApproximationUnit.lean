/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma73ProductDefect

/-!
# Valuation-unit quadratic approximations

A positive-depth approximation to a valuation unit is itself a valuation
unit.  Bundling the approximating scalar as an element of `Kˣ` makes it
available for integral changes of unary lattice generators.
-/

namespace Bong

open Dyadic

universe u


variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

theorem exists_valuationUnit_quadraticApproximation
    (a : Kˣ) (ha : IsValuationUnit K (a : K))
    (k : Nat) (hk : 0 < k)
    (hdefect : (k : ℕ∞) ≤ quadraticDefect K a) :
    ∃ s : Kˣ,
      ordUnit K s = 0 ∧
        ((k : Int) : WithTop Int) ≤
          ord K (1 - (s : K) ^ 2 / (a : K)) := by
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
    ⟨x, hx⟩
  have herrorPos : 0 < ord K (1 - x ^ 2 / (a : K)) := by
    exact (show (0 : WithTop Int) < (k : WithTop Int) by
      exact_mod_cast hk).trans_le hx
  have hquotOrder : ord K (x ^ 2 / (a : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K (1 - x ^ 2 / (a : K)) := by
      simpa only [ord_one] using herrorPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - (1 - x ^ 2 / (a : K)) = x ^ 2 / (a : K) := by ring
    rw [heq] at hsub
    simpa only [ord_one] using hsub
  have hxNe : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let s : Kˣ := Units.mk0 x hxNe
  have hsOrder : ordUnit K s = 0 := by
    have hquotUnit : ordUnit K (s ^ 2 / a) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      have hval : ((s ^ 2 / a : Kˣ) : K) =
          x ^ 2 / (a : K) := by
        simp [s]
      rw [hval, hquotOrder]
      rfl
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_pow] at hquotUnit
    have haOrder := (isValuationUnit_iff_ordUnit_eq_zero K a).1 ha
    rw [haOrder] at hquotUnit
    omega
  refine ⟨s, hsOrder, ?_⟩
  simpa [s] using hx

end BONG

end Bong
