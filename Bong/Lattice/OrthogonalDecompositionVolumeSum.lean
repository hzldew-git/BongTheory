/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionTail
import Bong.Lattice.OrthogonalDecompositionVolume

/-!
# Volume order of a finite orthogonal decomposition

The two-component volume formula extends by repeatedly splitting off the
head component.  The nonempty formulation is exactly what is needed for
proper prefixes and suffixes of a Jordan chain.
-/

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The volume order of a nonempty finite orthogonal decomposition is the
sum of the volume orders of its components. -/
theorem volumeOrder_eq_sum_components :
    ∀ {n : Nat} (D : OrthogonalDecomposition q L (n + 1)),
      volumeOrder q L =
        ∑ i, volumeOrder (D.component i).space (D.component i).lattice := by
  intro n D
  induction n generalizing V with
  | zero =>
      rw [Fin.sum_univ_one]
      exact volumeOrder_eq_of_isometry D.singleComponentLatticeIsometry |>.symm
  | succ n ih =>
      have hsplit := D.headTailDecomposition.volumeOrder_eq_add_components
      have htail := ih D.tailDecomposition
      rw [headTailDecomposition_zero, headTailDecomposition_one] at hsplit
      calc
        volumeOrder q L =
            volumeOrder (D.component 0).space (D.component 0).lattice +
              volumeOrder
                (D.suffixQuadraticSublattice 1).space
                (D.suffixQuadraticSublattice 1).lattice := hsplit
        _ = volumeOrder (D.component 0).space (D.component 0).lattice +
              ∑ i, volumeOrder (D.tailDecomposition.component i).space
                (D.tailDecomposition.component i).lattice := by
          rw [htail]
        _ = volumeOrder (D.component 0).space (D.component 0).lattice +
              ∑ i : Fin (n + 1), volumeOrder (D.component i.succ).space
                (D.component i.succ).lattice := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact volumeOrder_eq_of_isometry (D.tailComponentIsometry i) |>.symm
        _ = ∑ i, volumeOrder (D.component i).space
              (D.component i).lattice := by
          exact (Fin.sum_univ_succ fun i ↦
            volumeOrder (D.component i).space (D.component i).lattice).symm

end Lattice.OrthogonalDecomposition

end Bong
