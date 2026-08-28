/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.ScaleTruncationIsometry

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Scale truncation respects an arbitrary integral two-block orthogonal
splitting at the level of volume orders. -/
theorem volumeOrder_scaleTruncation_eq_add_components
    (D : OrthogonalDecomposition q L 2) (r : Int) :
    volumeOrder q (scaleTruncation q L r) =
      volumeOrder (D.component 0).space
          (scaleTruncation (D.component 0).space
            (D.component 0).lattice r) +
        volumeOrder (D.component 1).space
          (scaleTruncation (D.component 1).space
            (D.component 1).lattice r) := by
  let f := D.pairProductLatticeIsometry
  have h := volumeOrder_eq_of_isometry (f.scaleTruncation r)
  rw [scaleTruncation_orthogonalProduct,
    volumeOrder_orthogonalProduct] at h
  exact h.symm

end Lattice.OrthogonalDecomposition

end Bong
