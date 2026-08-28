/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanInitialSegment
import Bong.Lattice.JordanSuffixSegment
import Bong.Lattice.ScaleTruncationDual

/-!
# Scale truncation outside the range of Jordan scales

Below the first Jordan scale, the intrinsic truncation is the lattice
itself.  Above the last Jordan scale, it is the indicated scalar multiple of
the integral dual.  These two elementary endpoint calculations are the
geometric input for splitting a fundamental layer into its dualized prefix
and unchanged suffix.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- If the truncation order is no larger than every Jordan scale, no
component is rescaled. -/
theorem scaleTruncation_eq_self_of_le_scaleOrders
    (J : JordanDecomposition q L t) (r : Int)
    (h : ∀ i : Fin t, r ≤ ordUnit K (J.scaleGenerator i)) :
    scaleTruncation q L r = L := by
  rw [J.scaleTruncation_eq_componentwiseRescaleLattice]
  have hfactor : J.scaleTruncationFactor r = fun _ ↦ 1 := by
    funext i
    unfold scaleTruncationFactor positivePartUnit
    rw [if_neg]
    intro hpos
    rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
      ordUnit_uniformizerPowerUnit] at hpos
    have hle := h i
    omega
  rw [hfactor, J.toOrthogonalDecomposition.componentwiseRescaleLattice_one]

/-- If the truncation order is strictly larger than every Jordan scale, the
intersection has reached the scalar multiple of the full integral dual. -/
theorem scaleTruncation_eq_rescale_dual_of_scaleOrders_lt
    (J : JordanDecomposition q L t) (r : Int)
    (h : ∀ i : Fin t, ordUnit K (J.scaleGenerator i) < r) :
    scaleTruncation q L r =
      rescale (scaleTruncationUnit (K := K) r) (dualLattice q L) := by
  rw [J.scaleTruncation_eq_componentwiseRescaleLattice,
    J.toOrthogonalDecomposition.rescale_dualLattice_eq_componentwiseRescaleLattice
      J.scaleGenerator J.modular]
  congr 1
  funext i
  unfold scaleTruncationFactor positivePartUnit
  rw [if_pos]
  rw [ordUnit_mul, ordUnit_inv, scaleTruncationUnit,
    ordUnit_uniformizerPowerUnit]
  exact sub_pos.mpr (h i)

/-- Every scale in the exact prefix before component `k` is strictly
smaller than the scale of component `k`. -/
theorem initialSegment_scaleOrder_lt_cut
    (J : JordanDecomposition q L t) {k n : Nat}
    (hkn : k + (n + 1) = t) (hk : 0 < k)
    (i : Fin ((k - 1) + 1)) :
    ordUnit K ((J.initialSegment (k - 1) (by omega)).scaleGenerator i) <
      ordUnit K (J.scaleGenerator ⟨k, by omega⟩) := by
  rw [J.initialSegment_scaleGenerator]
  apply J.scaleOrder_strict
  change i.val < k
  omega

/-- At the scale of component `k`, the exact prefix is the indicated
scalar multiple of its integral dual. -/
theorem initialSegment_scaleTruncation_eq_rescale_dual
    (J : JordanDecomposition q L t) {k n : Nat}
    (hkn : k + (n + 1) = t) (hk : 0 < k) :
    let P := J.initialSegment (k - 1) (by omega)
    scaleTruncation
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          ((k - 1) + 1)).space
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          ((k - 1) + 1)).lattice
        (ordUnit K (J.scaleGenerator ⟨k, by omega⟩)) =
      rescale
        (scaleTruncationUnit (K := K)
          (ordUnit K (J.scaleGenerator ⟨k, by omega⟩)))
        (dualLattice
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice
            ((k - 1) + 1)).space
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice
            ((k - 1) + 1)).lattice) := by
  let P := J.initialSegment (k - 1) (by omega)
  apply P.scaleTruncation_eq_rescale_dual_of_scaleOrders_lt
  intro i
  exact J.initialSegment_scaleOrder_lt_cut hkn hk i

/-- Every scale in the exact suffix beginning at component `k` is at least
the scale of component `k`. -/
theorem cut_scaleOrder_le_suffixSegment
    (J : JordanDecomposition q L t) {k n : Nat}
    (hkn : k + (n + 1) = t) (i : Fin (n + 1)) :
    ordUnit K (J.scaleGenerator ⟨k, by omega⟩) ≤
      ordUnit K ((J.suffixSegment hkn).scaleGenerator i) := by
  rw [J.suffixSegment_scaleGenerator]
  let left : Fin t := ⟨k, by omega⟩
  let right : Fin t :=
    (J.toOrthogonalDecomposition.suffixIndexEquiv hkn i).1
  have hindex : left ≤ right := by
    change k ≤ k + i.val
    omega
  change ordUnit K (J.scaleGenerator left) ≤
    ordUnit K (J.scaleGenerator right)
  by_cases heq : left = right
  · rw [heq]
  · exact (J.scaleOrder_strict (lt_of_le_of_ne hindex heq)).le

/-- At the scale of component `k`, its exact suffix is unchanged. -/
theorem suffixSegment_scaleTruncation_eq_self
    (J : JordanDecomposition q L t) {k n : Nat}
    (hkn : k + (n + 1) = t) :
    let S := J.suffixSegment hkn
    scaleTruncation
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).space
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).lattice
        (ordUnit K (J.scaleGenerator ⟨k, by omega⟩)) =
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).lattice := by
  let S := J.suffixSegment hkn
  apply S.scaleTruncation_eq_self_of_le_scaleOrders
  intro i
  exact J.cut_scaleOrder_le_suffixSegment hkn i

end Lattice.JordanDecomposition

end Bong
