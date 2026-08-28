/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaGeneralPlaneDiagonalization
import Bong.Lattice.OmearaUnitLineAdjunction

/-!
# Integral splitting of a general plane with unit first coefficient

If `a` is a valuation unit, the field orthogonalization

`(x,y) |-> (x + a⁻¹y, y)`

is integral in both directions.  Consequently O'Meara's standard lattice
`A(a,b)` is the orthogonal product of the line `<a>` and the line
`<b-a⁻¹>`.  This is the integral splitting used before applying Corollary
93:14a in the proof of 93:18(iv).
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The nonzero coefficient of the orthogonal complement of the first
standard vector in `A(a,b)`. -/
noncomputable def unitGeneralPlaneTail
    (a : Kˣ) (b : K) (hnondegenerate : (a : K) * b ≠ 1) : Kˣ :=
  QuadraticSpace.omearaGeneralPlaneDiagonalUnits a b hnondegenerate 1

@[simp]
theorem coe_unitGeneralPlaneTail
    (a : Kˣ) (b : K) (hnondegenerate : (a : K) * b ≠ 1) :
    (unitGeneralPlaneTail a b hnondegenerate : K) =
      b - (a : K)⁻¹ :=
  rfl

/-- The coordinate equivalence which extracts the unit line and its
orthogonal complement. -/
noncomputable def unitGeneralPlaneSplittingLinearEquiv (a : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] K × K :=
  (QuadraticSpace.omearaGeneralPlaneOrthogonalizingLinearEquiv a).trans
    (LinearEquiv.finTwoArrow K K)

@[simp]
theorem unitGeneralPlaneSplittingLinearEquiv_apply
    (a : Kˣ) (x : Fin 2 → K) :
    unitGeneralPlaneSplittingLinearEquiv a x =
      (x 0 + (a : K)⁻¹ * x 1, x 1) :=
  rfl

@[simp]
theorem unitGeneralPlaneSplittingLinearEquiv_symm_apply
    (a : Kˣ) (x : K × K) :
    (unitGeneralPlaneSplittingLinearEquiv a).symm x =
      ![x.1 - (a : K)⁻¹ * x.2, x.2] := by
  funext i
  fin_cases i <;> simp [unitGeneralPlaneSplittingLinearEquiv,
    QuadraticSpace.omearaGeneralPlaneOrthogonalizingLinearEquiv]

/-- Integral orthogonal splitting of `A(a,b)` when `a` is a valuation
unit.  Both one-dimensional target lattices are the standard unary lattice. -/
noncomputable def unitGeneralPlaneSplittingIsometry
    (a : Kˣ) (b : K) (hnondegenerate : (a : K) * b ≠ 1)
    (ha : IsValuationUnit K (a : K)) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane (a : K) b hnondegenerate)
      ((QuadraticSpace.scaledLine a).orthogonalSum
        (QuadraticSpace.scaledLine
          (unitGeneralPlaneTail a b hnondegenerate)))
      (hyperbolicPlaneLattice (K := K))
      (product (BONG.unaryModelLattice (K := K))
        (BONG.unaryModelLattice (K := K))) where
  toLinearEquiv := unitGeneralPlaneSplittingLinearEquiv a
  map_bilin x y := by
    rw [QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.scaledLine_bilin_apply,
      QuadraticSpace.scaledLine_bilin_apply,
      QuadraticSpace.omearaGeneralPlane_bilin_apply]
    simp only [unitGeneralPlaneSplittingLinearEquiv_apply,
      coe_unitGeneralPlaneTail]
    field_simp [Units.ne_zero a]
    ring
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_product_iff,
      BONG.mem_unaryModelLattice_iff,
      BONG.mem_unaryModelLattice_iff]
    simp only [unitGeneralPlaneSplittingLinearEquiv_apply,
      Prod.fst, Prod.snd]
    have haInv : (a : K)⁻¹ ∈ IntegerRing K := by
      have haInvUnit : IsValuationUnit K ((a : K)⁻¹) := by
        simpa [IsValuationUnit, AddValuation.map_inv, ha]
      exact (mem_integerRing_iff K).2 haInvUnit.ge
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨(IntegerRing K).toSubring.add_mem hx0
        ((IntegerRing K).toSubring.mul_mem haInv hx1), hx1⟩
    · rintro ⟨hsum, hx1⟩
      have hproduct := (IntegerRing K).toSubring.mul_mem haInv hx1
      exact ⟨by
        change x 0 ∈ (IntegerRing K).toSubring
        have hdiff := (IntegerRing K).toSubring.sub_mem hsum hproduct
        simpa only [add_sub_cancel_right] using hdiff, hx1⟩

end Lattice

end Bong
