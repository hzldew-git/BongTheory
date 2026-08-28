/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturatedTail

/-!
# Fundamental boundary ideals of saturated tails

For a saturated Jordan splitting, every intrinsic invariant of the exact
suffix is the corresponding invariant of the full splitting with its index
shifted by one.  This file extends the norm-group equality to the chosen
norm-generator orders, weights, and O'Meara's boundary ideals `f_i`.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The left endpoint of a tail boundary is the left endpoint of the next
full boundary. -/
@[simp]
theorem boundaryLeftIndex_succ (i : Fin n) :
    (boundaryLeftIndex i).succ = boundaryLeftIndex i.succ := by
  apply Fin.ext
  rfl

/-- The same index shift for the right endpoint. -/
@[simp]
theorem boundaryRightIndex_succ (i : Fin n) :
    (boundaryRightIndex i).succ = boundaryRightIndex i.succ := by
  rfl

variable (J : JordanDecomposition q L (n + 1))

/-- Independently chosen fundamental norm generators on a saturated tail
and on the full splitting have the same valuation order. -/
theorem IsSaturated.tail_fundamentalNormGenerator_order_eq
    (hJ : J.IsSaturated) (i : Fin n) :
    ordUnit K (J.tail.fundamentalNormGenerator i) =
      ordUnit K (J.fundamentalNormGenerator i.succ) := by
  have hcommon : IsNormGeneratorValue
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.tail.fundamentalLattice i)
      (J.fundamentalNormGenerator i.succ) :=
    isNormGeneratorValue_of_normGroupSet_eq
      (J.fundamentalNormGenerator_spec i.succ)
      (IsSaturated.tail_fundamentalNormGroup_eq J hJ i).symm
      (J.tail.exists_fundamentalNormGenerator i)
  apply (principalIdeal_eq_iff_ordUnit_eq
    (J.tail.fundamentalNormGenerator i)
    (J.fundamentalNormGenerator i.succ)).mp
  exact (J.tail.fundamentalNormGenerator_spec i).2.symm.trans hcommon.2

/-- Fundamental weights also shift literally along a saturated tail. -/
theorem IsSaturated.tail_fundamentalWeightIdeal_eq
    (hJ : J.IsSaturated) (i : Fin n) :
    J.tail.fundamentalWeightIdeal i =
      J.fundamentalWeightIdeal i.succ := by
  have htwo : twoScaleIdeal q (J.fundamentalLattice i.succ) =
      twoScaleIdeal
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
        (J.tail.fundamentalLattice i) := by
    rw [J.fundamentalTwoScaleIdeal_eq_powerIdeal,
      J.tail.fundamentalTwoScaleIdeal_eq_powerIdeal,
      J.tail_fundamentalScaleOrder]
  exact (weightIdeal_eq_of_normGroupSet_eq_of_twoScaleIdeal_eq
    (J.fundamentalNormGenerator_spec i.succ)
    (J.tail.exists_fundamentalNormGenerator i)
    (IsSaturated.tail_fundamentalNormGroup_eq J hJ i).symm htwo).symm

/-- Consequently the integral weight orders shift by one. -/
theorem IsSaturated.tail_fundamentalWeightOrder_eq
    (hJ : J.IsSaturated) (i : Fin n) :
    J.tail.fundamentalWeightOrder i =
      J.fundamentalWeightOrder i.succ := by
  unfold fundamentalWeightOrder
  apply powerIdeal_order_eq_of_eq (K := K)
  rw [← weightIdeal_eq_powerIdeal, ← weightIdeal_eq_powerIdeal]
  simpa only [fundamentalWeightIdeal] using
    IsSaturated.tail_fundamentalWeightIdeal_eq J hJ i

variable {m : Nat} {J : JordanDecomposition q L (m + 2)}

/-- The norm-order sum at a tail boundary is the sum at the next full
boundary. -/
theorem IsSaturated.tail_boundaryNormOrderSum_eq
    (hJ : J.IsSaturated) (i : Fin m) :
    J.tail.boundaryNormOrderSum i = J.boundaryNormOrderSum i.succ := by
  unfold boundaryNormOrderSum
  rw [IsSaturated.tail_fundamentalNormGenerator_order_eq J hJ,
    IsSaturated.tail_fundamentalNormGenerator_order_eq J hJ]
  simp only [boundaryLeftIndex_succ, boundaryRightIndex_succ]

/-- Product-defect sums shift with the boundary. -/
theorem IsSaturated.tail_boundaryProductDefectSum_eq
    (hJ : J.IsSaturated) (i : Fin m) :
    J.tail.boundaryProductDefectSum i =
      J.boundaryProductDefectSum i.succ := by
  unfold boundaryProductDefectSum
  rw [IsSaturated.tail_fundamentalNormGroup_eq J hJ,
    IsSaturated.tail_fundamentalNormGroup_eq J hJ]
  simp only [boundaryLeftIndex_succ, boundaryRightIndex_succ]

/-- The parity term in `s_i^2 f_i` shifts with the boundary. -/
theorem IsSaturated.tail_boundaryParityIdeal_eq
    (hJ : J.IsSaturated) (i : Fin m) :
    J.tail.boundaryParityIdeal i = J.boundaryParityIdeal i.succ := by
  unfold boundaryParityIdeal
  rw [IsSaturated.tail_boundaryNormOrderSum_eq hJ,
    J.tail_fundamentalScaleOrder]
  simp only [boundaryLeftIndex_succ]

/-- The scaled O'Meara boundary ideal shifts by one. -/
theorem IsSaturated.tail_scaledFundamentalIdeal_eq
    (hJ : J.IsSaturated) (i : Fin m) :
    J.tail.scaledFundamentalIdeal i =
      J.scaledFundamentalIdeal i.succ := by
  unfold scaledFundamentalIdeal
  rw [IsSaturated.tail_boundaryNormOrderSum_eq hJ,
    IsSaturated.tail_boundaryProductDefectSum_eq hJ,
    IsSaturated.tail_boundaryParityIdeal_eq hJ]

/-- The unscaled fundamental ideal `f_i` shifts by one. -/
theorem IsSaturated.tail_fundamentalIdeal_eq
    (hJ : J.IsSaturated) (i : Fin m) :
    J.tail.fundamentalIdeal i = J.fundamentalIdeal i.succ := by
  unfold fundamentalIdeal
  rw [IsSaturated.tail_scaledFundamentalIdeal_eq hJ]
  simp only [tail_scaleGenerator, boundaryLeftIndex_succ]

end Lattice.JordanDecomposition

end Bong
