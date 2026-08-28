/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BlockProductOrthogonalDecomposition
import Bong.Lattice.OrthogonalDecompositionSuffixProduct

/-!
# Exact suffixes of Jordan decompositions

An exact nonempty suffix of a strict Jordan decomposition is again a strict
Jordan decomposition of its intrinsic suffix quadratic lattice.  This is the
suffix counterpart of `JordanDecomposition.initialSegment`.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n k : Nat}

/-- The exact suffix beginning at component `k`, with its inherited strict
Jordan data. -/
noncomputable def suffixSegment
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t) :
    JordanDecomposition
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).lattice
      (n + 1) := by
  let D := J.toOrthogonalDecomposition
  let raw := BONG.blockProductJordanDecomposition
    (D.suffixBlockCarrier hkn)
    (D.suffixBlockSpace hkn)
    (D.suffixBlockLattice hkn)
    (fun i ↦ J.scaleGenerator (D.suffixIndexEquiv hkn i).1)
    (fun i ↦ J.normGenerator (D.suffixIndexEquiv hkn i).1)
    (fun i ↦ J.modular (D.suffixIndexEquiv hkn i).1)
    (fun i ↦ J.scaleIdeal_eq (D.suffixIndexEquiv hkn i).1)
    (fun i ↦ J.normIdeal_eq (D.suffixIndexEquiv hkn i).1)
    (fun a b hab ↦ J.scaleOrder_strict <| by
      change a.val < b.val at hab
      change
        (D.suffixIndexEquiv hkn a).1.val <
          (D.suffixIndexEquiv hkn b).1.val
      simpa only [D.suffixIndexEquiv_val hkn] using
        Nat.add_lt_add_left hab k)
  exact raw.mapIsometry (D.suffixBlockProductIsometry hkn)

@[simp]
theorem suffixSegment_scaleGenerator
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t)
    (i : Fin (n + 1)) :
    (J.suffixSegment hkn).scaleGenerator i =
      J.scaleGenerator
        (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1 :=
  rfl

@[simp]
theorem suffixSegment_normGenerator
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t)
    (i : Fin (n + 1)) :
    (J.suffixSegment hkn).normGenerator i =
      J.normGenerator
        (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1 :=
  rfl

@[simp]
theorem suffixSegment_componentRank
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t)
    (i : Fin (n + 1)) :
    (J.suffixSegment hkn).componentRank i =
      J.componentRank
        (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1 := by
  unfold suffixSegment
  rw [mapIsometry_componentRank,
    BONG.blockProductJordanDecomposition_componentRank]
  rfl

/-- Each component of an exact suffix is integrally isometric to the
corresponding component of the original Jordan decomposition. -/
noncomputable def suffixSegmentComponentIsometry
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t)
    (i : Fin (n + 1)) :
    Isometry
      (J.component
        (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1).space
      ((J.suffixSegment hkn).component i).space
      (J.component
        (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1).lattice
      ((J.suffixSegment hkn).component i).lattice := by
  let D := J.toOrthogonalDecomposition
  let raw := BONG.blockProductJordanDecomposition
    (D.suffixBlockCarrier hkn)
    (D.suffixBlockSpace hkn)
    (D.suffixBlockLattice hkn)
    (fun j ↦ J.scaleGenerator (D.suffixIndexEquiv hkn j).1)
    (fun j ↦ J.normGenerator (D.suffixIndexEquiv hkn j).1)
    (fun j ↦ J.modular (D.suffixIndexEquiv hkn j).1)
    (fun j ↦ J.scaleIdeal_eq (D.suffixIndexEquiv hkn j).1)
    (fun j ↦ J.normIdeal_eq (D.suffixIndexEquiv hkn j).1)
    (fun a b hab ↦ J.scaleOrder_strict <| by
      change a.val < b.val at hab
      change
        (D.suffixIndexEquiv hkn a).1.val <
          (D.suffixIndexEquiv hkn b).1.val
      simpa only [D.suffixIndexEquiv_val hkn] using
        Nat.add_lt_add_left hab k)
  let coordinate := BONG.blockProductComponentIsometry
    (D.suffixBlockCarrier hkn)
    (D.suffixBlockSpace hkn)
    (D.suffixBlockLattice hkn) i
  let ambient := D.suffixBlockProductIsometry hkn
  let transported := (raw.component i).mapLatticeIsometry ambient
  change Isometry
    (D.component (D.suffixIndexEquiv hkn i).1).space
    ((raw.mapIsometry ambient).component i).space
    (D.component (D.suffixIndexEquiv hkn i).1).lattice
    ((raw.mapIsometry ambient).component i).lattice
  exact coordinate.trans transported

end Lattice.JordanDecomposition

end Bong
