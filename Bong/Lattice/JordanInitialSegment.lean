/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.OrthogonalDecompositionPrefixProduct

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- A nonempty initial segment of a Jordan decomposition, regarded as a
Jordan decomposition of its intrinsic prefix quadratic lattice. -/
noncomputable def initialSegment
    (J : JordanDecomposition q L t) (m : Nat) (hm : m + 1 ≤ t) :
    JordanDecomposition
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice (m + 1)).lattice
      (m + 1) := by
  let D := J.toOrthogonalDecomposition
  let raw := BONG.blockProductJordanDecomposition
    (D.prefixBlockCarrier hm)
    (D.prefixBlockSpace hm)
    (D.prefixBlockLattice hm)
    (fun i => J.scaleGenerator (D.prefixIndexEquiv (m + 1) hm i).1)
    (fun i => J.normGenerator (D.prefixIndexEquiv (m + 1) hm i).1)
    (fun i => J.modular (D.prefixIndexEquiv (m + 1) hm i).1)
    (fun i => J.scaleIdeal_eq (D.prefixIndexEquiv (m + 1) hm i).1)
    (fun i => J.normIdeal_eq (D.prefixIndexEquiv (m + 1) hm i).1)
    (fun a b hab => J.scaleOrder_strict <| by
      change a.val < b.val at hab
      change
        (D.prefixIndexEquiv (m + 1) hm a).1.val <
          (D.prefixIndexEquiv (m + 1) hm b).1.val
      simpa only [D.prefixIndexEquiv_val (m + 1) hm] using hab)
  exact raw.mapIsometry (D.prefixBlockProductIsometry hm)

@[simp]
theorem initialSegment_scaleGenerator
    (J : JordanDecomposition q L t) (m : Nat) (hm : m + 1 ≤ t)
    (i : Fin (m + 1)) :
    (J.initialSegment m hm).scaleGenerator i =
      J.scaleGenerator
        (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hm i).1 :=
  rfl

@[simp]
theorem initialSegment_normGenerator
    (J : JordanDecomposition q L t) (m : Nat) (hm : m + 1 ≤ t)
    (i : Fin (m + 1)) :
    (J.initialSegment m hm).normGenerator i =
      J.normGenerator
        (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hm i).1 :=
  rfl

@[simp]
theorem initialSegment_componentRank
    (J : JordanDecomposition q L t) (m : Nat) (hm : m + 1 ≤ t)
    (i : Fin (m + 1)) :
    (J.initialSegment m hm).componentRank i =
      J.componentRank
        (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hm i).1 := by
  unfold initialSegment
  rw [mapIsometry_componentRank,
    BONG.blockProductJordanDecomposition_componentRank]
  rfl

/-- Each component of an initial segment is integrally isometric to the
corresponding component of the original Jordan decomposition. -/
noncomputable def initialSegmentComponentIsometry
    (J : JordanDecomposition q L t) (m : Nat) (hm : m + 1 ≤ t)
    (i : Fin (m + 1)) :
    Isometry
      (J.component
        (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hm i).1).space
      ((J.initialSegment m hm).component i).space
      (J.component
        (J.toOrthogonalDecomposition.prefixIndexEquiv (m + 1) hm i).1).lattice
      ((J.initialSegment m hm).component i).lattice := by
  let D := J.toOrthogonalDecomposition
  let raw := BONG.blockProductJordanDecomposition
    (D.prefixBlockCarrier hm)
    (D.prefixBlockSpace hm)
    (D.prefixBlockLattice hm)
    (fun j ↦ J.scaleGenerator (D.prefixIndexEquiv (m + 1) hm j).1)
    (fun j ↦ J.normGenerator (D.prefixIndexEquiv (m + 1) hm j).1)
    (fun j ↦ J.modular (D.prefixIndexEquiv (m + 1) hm j).1)
    (fun j ↦ J.scaleIdeal_eq (D.prefixIndexEquiv (m + 1) hm j).1)
    (fun j ↦ J.normIdeal_eq (D.prefixIndexEquiv (m + 1) hm j).1)
    (fun a b hab ↦ J.scaleOrder_strict <| by
      change a.val < b.val at hab
      change
        (D.prefixIndexEquiv (m + 1) hm a).1.val <
          (D.prefixIndexEquiv (m + 1) hm b).1.val
      simpa only [D.prefixIndexEquiv_val (m + 1) hm] using hab)
  let coordinate := BONG.blockProductComponentIsometry
    (D.prefixBlockCarrier hm)
    (D.prefixBlockSpace hm)
    (D.prefixBlockLattice hm) i
  let ambient := D.prefixBlockProductIsometry hm
  let transported := (raw.component i).mapLatticeIsometry ambient
  change Isometry
    (D.component (D.prefixIndexEquiv (m + 1) hm i).1).space
    ((raw.mapIsometry ambient).component i).space
    (D.component (D.prefixIndexEquiv (m + 1) hm i).1).lattice
    ((raw.mapIsometry ambient).component i).lattice
  exact coordinate.trans transported

end Lattice.JordanDecomposition

end Bong
