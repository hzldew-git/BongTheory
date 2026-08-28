/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalSup
import Bong.Lattice.NormGeneratorValues
import Bong.Lattice.NormIdealOrthogonalProduct

/-!
# Norm ideals of amalgamated orthogonal components

The concrete `orthogonalSup` construction is isometric to the product of
the two original components.  Consequently its norm ideal is the sum of
the two component norm ideals.  This is the ideal-theoretic statement behind
the minimum formulas for the norm orders of equal-scale blocks in Beli's
almost Jordan decompositions.
-/

namespace Bong

open Dyadic

namespace Lattice
namespace OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The norm ideal of two amalgamated orthogonal components is the sum of
their norm ideals. -/
theorem normIdeal_orthogonalSup
    (D : OrthogonalDecomposition q L t) {i j : Fin t} (hij : i ≠ j) :
    normIdeal (D.orthogonalSup hij).space
        (D.orthogonalSup hij).lattice =
      normIdeal (D.component i).space (D.component i).lattice ⊔
        normIdeal (D.component j).space (D.component j).lattice := by
  let f := D.orthogonalSupLatticeIsometry hij
  calc
    normIdeal (D.orthogonalSup hij).space
        (D.orthogonalSup hij).lattice =
        normIdeal
          ((D.component i).space.orthogonalSum (D.component j).space)
          (product (D.component i).lattice (D.component j).lattice) := by
      exact normIdeal_map_isometry f.toQuadraticSpaceIsometry
        (product (D.component i).lattice (D.component j).lattice)
    _ = normIdeal (D.component i).space (D.component i).lattice ⊔
        normIdeal (D.component j).space (D.component j).lattice :=
      normIdeal_orthogonalProduct

/-- If generators have been chosen for the two component norm ideals and
for their amalgamation, the amalgamated norm order is their minimum. -/
theorem ordUnit_normGenerator_orthogonalSup
    (D : OrthogonalDecomposition q L t) {i j : Fin t} (hij : i ≠ j)
    (a b c : Kˣ)
    (ha : normIdeal (D.component i).space (D.component i).lattice =
      principalIdeal (K := K) (a : K))
    (hb : normIdeal (D.component j).space (D.component j).lattice =
      principalIdeal (K := K) (b : K))
    (hc : normIdeal (D.orthogonalSup hij).space
        (D.orthogonalSup hij).lattice =
      principalIdeal (K := K) (c : K)) :
    ordUnit K c = min (ordUnit K a) (ordUnit K b) := by
  apply ordUnit_eq_min_of_principalIdeal_eq_sup a b c
  rw [← hc, D.normIdeal_orthogonalSup hij, ha, hb]

end OrthogonalDecomposition
end Lattice
end Bong
