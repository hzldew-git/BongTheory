/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.FormRescale
import Bong.Lattice.DeterminantIsometry
import Bong.Lattice.OrthogonalSumRescale

/-!
# Refined determinant classes under form normalization

This file combines the exact determinant formula for form rescaling with
the identity isometry which cancels an inverse rescaling.  It is the
bookkeeping needed when O'Meara normalizes a modular component to scale one
but states boundary determinant congruences before normalization.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Recover the determinant class of a form from its inverse-scale
normalization. -/
theorem determinantClass_eq_scalePow_mul_rescaleInverse
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) :
    determinantClass q L =
      unitSquareClass K (a ^ finrank K V) *
        determinantClass (q.rescaleUnit a⁻¹) L := by
  let f : Isometry ((q.rescaleUnit a⁻¹).rescaleUnit a) q L L :=
    (rescaleUnitMulLatticeIsometry q L a⁻¹ a).trans (by
      simpa using Isometry.rescaleUnitOne q L)
  calc
    determinantClass q L =
        determinantClass ((q.rescaleUnit a⁻¹).rescaleUnit a) L :=
      (determinantClass_eq_of_isometry f).symm
    _ = unitSquareClass K
          (a ^ finrank K V) *
        determinantClass (q.rescaleUnit a⁻¹) L :=
      determinantClass_rescaleUnit (q.rescaleUnit a⁻¹) a L

end Lattice

end Bong
