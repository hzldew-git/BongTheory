/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.OrthogonalDecompositionPrefixProduct
import Bong.Lattice.OrthogonalDecompositionVolumeSum

/-!
# Volume order of a nonempty prefix

A prefix is presented by the coordinate block product of its components.
Combining that presentation with additivity of volume gives a formula which
is independent of the auxiliary bases used to build the prefix lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n : Nat}

/-- The volume of a nonempty prefix is the sum of the component volumes
before the cut. -/
theorem volumeOrder_prefixQuadraticSublattice_eq_sum
    (D : OrthogonalDecomposition q L t) (hk : n + 1 ≤ t) :
    volumeOrder
        (D.prefixQuadraticSublattice (n + 1)).space
        (D.prefixQuadraticSublattice (n + 1)).lattice =
      ∑ i : Fin (n + 1),
        volumeOrder (D.prefixBlockSpace hk i)
          (D.prefixBlockLattice hk i) := by
  let E := BONG.blockProductOrthogonalDecomposition
    (D.prefixBlockCarrier hk) (D.prefixBlockSpace hk)
    (D.prefixBlockLattice hk)
  have hpresentation :=
    volumeOrder_eq_of_isometry (D.prefixBlockProductIsometry hk)
  have hsum := E.volumeOrder_eq_sum_components
  calc
    volumeOrder
        (D.prefixQuadraticSublattice (n + 1)).space
        (D.prefixQuadraticSublattice (n + 1)).lattice =
      volumeOrder
        (BONG.blockOrthogonalForm n (D.prefixBlockCarrier hk)
          (D.prefixBlockSpace hk))
        (BONG.blockProductLattice n (D.prefixBlockCarrier hk)
          (D.prefixBlockLattice hk)) := hpresentation.symm
    _ = ∑ i, volumeOrder (E.component i).space
          (E.component i).lattice := hsum
    _ = ∑ i : Fin (n + 1),
          volumeOrder (D.prefixBlockSpace hk i)
            (D.prefixBlockLattice hk i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact volumeOrder_eq_of_isometry
        (BONG.blockProductComponentIsometry
          (D.prefixBlockCarrier hk) (D.prefixBlockSpace hk)
          (D.prefixBlockLattice hk) i) |>.symm

end Lattice.OrthogonalDecomposition

end Bong
