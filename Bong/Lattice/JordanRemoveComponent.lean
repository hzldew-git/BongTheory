/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.OrthogonalDecompositionTail
import Mathlib.GroupTheory.Perm.Fin

/-!
# Removing one Jordan component

O'Meara's saturation argument isolates an arbitrary Jordan component while
retaining all remaining components in their original scale order.  The
permutation `i.cycleRange.symm` puts `i` first and enumerates its complement
by `i.succAbove`; taking the exact suffix therefore gives another Jordan
decomposition.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- Reindex a decomposition so that the selected component is first and all
other components retain their original relative order. -/
noncomputable def selectedFirstOrthogonalDecomposition
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2)) :
    OrthogonalDecomposition q L (n + 2) :=
  J.toOrthogonalDecomposition.reindex i.cycleRange.symm

@[simp]
theorem selectedFirst_component_zero
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2)) :
    (J.selectedFirstOrthogonalDecomposition i).component 0 =
      J.component i := by
  change J.component (i.cycleRange.symm 0) = J.component i
  rw [Fin.cycleRange_symm_zero]

@[simp]
theorem selectedFirst_component_succ
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (J.selectedFirstOrthogonalDecomposition i).component j.succ =
      J.component (i.succAbove j) := by
  change J.component (i.cycleRange.symm j.succ) =
    J.component (i.succAbove j)
  rw [Fin.cycleRange_symm_succ]

/-- The exact orthogonal complement of the selected component. -/
noncomputable abbrev selectedRemainder
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2)) :=
  (J.selectedFirstOrthogonalDecomposition i).suffixQuadraticSublattice 1

/-- The exact orthogonal complement of one selected Jordan component,
equipped with the remaining Jordan components in their original order. -/
noncomputable def removeComponent
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2)) :
    JordanDecomposition
      ((J.selectedFirstOrthogonalDecomposition i).suffixQuadraticSublattice 1).space
      ((J.selectedFirstOrthogonalDecomposition i).suffixQuadraticSublattice 1).lattice
      (n + 1) where
  toOrthogonalDecomposition :=
    (J.selectedFirstOrthogonalDecomposition i).tailDecomposition
  scaleGenerator := fun j ↦ J.scaleGenerator (i.succAbove j)
  normGenerator := fun j ↦ J.normGenerator (i.succAbove j)
  modular := by
    intro j
    let E := J.selectedFirstOrthogonalDecomposition i
    have hcomponent : E.component j.succ =
        J.component (i.succAbove j) := by
      exact J.selectedFirst_component_succ i j
    have hmodular := J.modular (i.succAbove j)
    rw [← hcomponent] at hmodular
    exact hmodular.mapLatticeIsometry (E.tailComponentIsometry j)
  scaleIdeal_eq := by
    intro j
    let E := J.selectedFirstOrthogonalDecomposition i
    let g := E.tailComponentIsometry j
    have hcomponent : E.component j.succ =
        J.component (i.succAbove j) := by
      exact J.selectedFirst_component_succ i j
    calc
      scaleIdeal (E.tailComponent j).space (E.tailComponent j).lattice =
          scaleIdeal (E.component j.succ).space
            (E.component j.succ).lattice := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = scaleIdeal (J.component (i.succAbove j)).space
          (J.component (i.succAbove j)).lattice := by rw [hcomponent]
      _ = principalIdeal (K := K)
          (J.scaleGenerator (i.succAbove j) : K) :=
        J.scaleIdeal_eq (i.succAbove j)
  normIdeal_eq := by
    intro j
    let E := J.selectedFirstOrthogonalDecomposition i
    let g := E.tailComponentIsometry j
    have hcomponent : E.component j.succ =
        J.component (i.succAbove j) := by
      exact J.selectedFirst_component_succ i j
    calc
      normIdeal (E.tailComponent j).space (E.tailComponent j).lattice =
          normIdeal (E.component j.succ).space
            (E.component j.succ).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = normIdeal (J.component (i.succAbove j)).space
          (J.component (i.succAbove j)).lattice := by rw [hcomponent]
      _ = principalIdeal (K := K)
          (J.normGenerator (i.succAbove j) : K) :=
        J.normIdeal_eq (i.succAbove j)
  scaleOrder_strict := by
    intro j k hjk
    exact J.scaleOrder_strict ((Fin.succAboveOrderEmb i).strictMono hjk)

@[simp]
theorem removeComponent_component
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (J.removeComponent i).component j =
      (J.selectedFirstOrthogonalDecomposition i).tailComponent j :=
  rfl

@[simp]
theorem removeComponent_scaleGenerator
    (J : JordanDecomposition q L (n + 2)) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (J.removeComponent i).scaleGenerator j =
      J.scaleGenerator (i.succAbove j) :=
  rfl

end Lattice.JordanDecomposition

end Bong
