/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightAlignedPair
import Bong.Lattice.Omeara9328ScaleSpread

/-!
# Scale spread in O'Meara 93:28, Step 8

The inserted scale is exactly one valuation step above the old first scale.
Consequently deleting the old head after the insertion strictly decreases
the scale-spread induction parameter used in the sufficiency proof.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Pointwise equality of scale-generator orders preserves the scale
spread. -/
theorem scaleSpread_eq_of_scaleGenerator_order_eq
    (J : JordanDecomposition q L (n + 1))
    (H : JordanDecomposition r M (n + 1))
    (h : ∀ i, ordUnit K (H.scaleGenerator i) =
      ordUnit K (J.scaleGenerator i)) :
    H.scaleSpread = J.scaleSpread := by
  unfold scaleSpread
  rw [h (Fin.last n), h 0]

/-- The first gap of the raw Step-8 splitting is exactly one. -/
theorem stepEightJordan_firstScaleGap_eq_one
    (J : JordanDecomposition q L (n + 2))
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    (J.stepEightJordan hgap).fundamentalScaleOrder 1 -
        (J.stepEightJordan hgap).fundamentalScaleOrder 0 = 1 := by
  unfold fundamentalScaleOrder
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightJordan_scaleGenerator,
    J.stepEightScaleGenerator_inserted]
  have hzero : (0 : Fin (n + 3)) =
      (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  rw [hzero, J.stepEightScaleGenerator_old, J.stepEightScale_order]
  omega

/-- Removing the old head after Step 8 strictly decreases the scale
spread. -/
theorem stepEightJordan_tail_scaleSpread_lt
    (J : JordanDecomposition q L (n + 2))
    (hgap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0)) :
    (J.stepEightJordan hgap).tail.scaleSpread < J.scaleSpread := by
  rw [tail_scaleSpread, scaleSpread]
  rw [J.stepEightJordan_scaleGenerator,
    J.stepEightJordan_scaleGenerator]
  have hlast :
      J.stepEightScaleGenerator (Fin.last (n + 2)) =
        J.scaleGenerator (Fin.last (n + 1)) := by
    rw [show Fin.last (n + 2) =
        (1 : Fin (n + 3)).succAbove (Fin.last (n + 1)) by
      exact (Fin.succAbove_ne_last_last (by
        intro h
        have hv := congrArg Fin.val h
        simp at hv)).symm,
      J.stepEightScaleGenerator_old]
  rw [hlast, J.stepEightScaleGenerator_inserted, J.stepEightScale_order]
  have hlastOrder := J.scaleOrder_strict
    (i := (0 : Fin (n + 2))) (j := Fin.last (n + 1)) (by
      change 0 < n + 1
      omega)
  rw [Int.toNat_lt_toNat (by omega)]
  omega

end Lattice.JordanDecomposition

end Bong
