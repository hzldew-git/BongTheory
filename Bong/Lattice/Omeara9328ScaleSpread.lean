/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328SaturatedInduction

/-!
# The scale-spread induction parameter in O'Meara 93:28

The sufficiency proof of O'Meara 93:28 is an induction on the integral
difference between the last and first Jordan scales.  Removing the first
component strictly decreases this natural-valued spread whenever at least
two components remain.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Natural-valued spread between the last and first Jordan scales. -/
noncomputable def scaleSpread (J : JordanDecomposition q L (n + 1)) : Nat :=
  Int.toNat (ordUnit K (J.scaleGenerator (Fin.last n)) -
    ordUnit K (J.scaleGenerator 0))

@[simp]
theorem scaleSpread_single (J : JordanDecomposition q L 1) :
    J.scaleSpread = 0 := by
  simp [scaleSpread]

theorem scaleSpread_pos (J : JordanDecomposition q L (n + 2)) :
    0 < J.scaleSpread := by
  have h := J.scaleOrder_strict (i := (0 : Fin (n + 2)))
    (j := Fin.last (n + 1)) (by
      change 0 < n + 1
      omega)
  rw [scaleSpread]
  omega

@[simp]
theorem tail_scaleSpread (J : JordanDecomposition q L (n + 2)) :
    J.tail.scaleSpread =
      Int.toNat (ordUnit K (J.scaleGenerator (Fin.last (n + 1))) -
        ordUnit K (J.scaleGenerator 1)) := by
  simp [scaleSpread, Fin.succ_last]

theorem tail_scaleSpread_lt (J : JordanDecomposition q L (n + 2)) :
    J.tail.scaleSpread < J.scaleSpread := by
  have hfirst := J.scaleOrder_strict (i := (0 : Fin (n + 2)))
    (j := (1 : Fin (n + 2))) (by simp)
  have hlast := J.scaleOrder_strict (i := (0 : Fin (n + 2)))
    (j := Fin.last (n + 1)) (by
      change 0 < n + 1
      omega)
  rw [tail_scaleSpread, scaleSpread]
  rw [Int.toNat_lt_toNat (by omega)]
  omega

end Lattice.JordanDecomposition

end Bong
