/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaOddQuaternaryModels
import Bong.Lattice.OmearaGeneralPlaneDiagonalization
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# Field invariants of O'Meara's odd quaternary models

The integral model calculation in `OmearaOddQuaternaryModels` is independent
of the field classification calculation.  This file supplies the latter: an
orthogonal product of two general planes has the explicit four-entry
diagonal coefficient family obtained by appending the two elementary binary
diagonalizations.
-/

namespace Bong

open Dyadic BONG.GoodBONG

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace OmearaOddQuaternaryModelData

variable (D : OmearaOddQuaternaryModelData K)

/-- Four nonzero diagonal coefficients of the model, ordered by its left
binary factor and then its right binary factor. -/
noncomputable def diagonalUnits : Fin 4 → Kˣ :=
  Fin.append
    (QuadraticSpace.omearaGeneralPlaneDiagonalUnits
      D.a D.leftTail D.left_nondegenerate)
    (QuadraticSpace.omearaGeneralPlaneDiagonalUnits
      D.b D.rightTail D.right_nondegenerate)

@[simp]
theorem diagonalUnits_zero : D.diagonalUnits 0 = D.a :=
  rfl

@[simp]
theorem diagonalUnits_one :
    (D.diagonalUnits 1 : K) = D.leftTail - (D.a : K)⁻¹ :=
  rfl

@[simp]
theorem diagonalUnits_two : D.diagonalUnits 2 = D.b :=
  rfl

@[simp]
theorem diagonalUnits_three :
    (D.diagonalUnits 3 : K) = D.rightTail - (D.b : K)⁻¹ :=
  rfl

/-- Explicit field diagonalization of the quaternary model. -/
noncomputable def diagonalizationIsometry :
    QuadraticSpace.Isometry D.space
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients D.diagonalUnits)
        (fun i ↦ Units.ne_zero (D.diagonalUnits i))) :=
  ((QuadraticSpace.omearaGeneralPlaneDiagonalUnitIsometry
      D.a D.leftTail D.left_nondegenerate).orthogonalSum
    (QuadraticSpace.omearaGeneralPlaneDiagonalUnitIsometry
      D.b D.rightTail D.right_nondegenerate)).trans
    (QuadraticSpace.finiteDiagonalOrthogonalSumIsometry
      (QuadraticSpace.omearaGeneralPlaneDiagonalUnits
        D.a D.leftTail D.left_nondegenerate)
      (QuadraticSpace.omearaGeneralPlaneDiagonalUnits
        D.b D.rightTail D.right_nondegenerate))

end OmearaOddQuaternaryModelData

end Lattice

end Bong
