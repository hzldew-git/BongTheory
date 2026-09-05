/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCEvenFirstDefects

/-!
# Signed full determinants and alternating prefixes in He (2025)

The full quadratic defect is transported from an actual ambient isometry.
For a proper prefix, the lower bound is derived from Proposition 3.5,
retaining the alpha caps until passing to the uncapped defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- An actual ambient isometry determines the square class of the full BONG product. -/
theorem heADC_prefixProduct_det_square_of_ambient {n : Nat} (a : GoodBONG q L n)
    (w : Fin n → Kˣ) (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w)) :
    IsSquare (a.prefixProduct n * diagonalUnitDeterminant w) := by
  have hrep : DiagonalRepresents (diagonalUnitCoefficients a.valueUnit)
      (diagonalUnitCoefficients w) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents a.valueUnit w).mp
      ⟨(a.toBONG.exactDiagonalizationIsometry.symm.trans
        (Classical.choice ambient)).toRepresentation⟩
  have h := DiagonalIsometryInvariantLaws.determinant_square a.valueUnit w hrep
  simpa [GoodBONG.prefixProduct, BONG.prefixProduct, GoodBONG.valueUnit,
    diagonalUnitDeterminant] using h

/-- The signed full quadratic defect equals the parameter defect of an isometric model. -/
theorem heADC_signedFullDefect_of_ambient {m n : Nat} (a : GoodBONG q L n)
    (w : Fin m → Kˣ) (hlength : n = m) (pairs : Nat) (hpairs : 2 * pairs = n)
    (c : Kˣ) (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w))
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ pairs * c))) :
    quadraticDefect K (a.toBONG.signedEvenPrefixProduct pairs) = quadraticDefect K c := by
  subst m
  have h := isSquare_mul_trans _ (diagonalUnitDeterminant w) _
    (a.heADC_prefixProduct_det_square_of_ambient w ambient) hclass
  apply heADCQuadraticDefect_eq_of_squareProduct
  simpa [BONG.signedEvenPrefixProduct, hpairs, GoodBONG.prefixProduct,
    mul_assoc, mul_comm, mul_left_comm] using h

/-- The same transport in the extended-rational defect type used by representation criteria. -/
theorem heADC_signedFullDefectOrder_of_ambient {m n : Nat} (a : GoodBONG q L n)
    (w : Fin m → Kˣ) (hlength : n = m) (pairs : Nat) (hpairs : 2 * pairs = n)
    (c : Kˣ) (ambient : q.IsIsometric (BONG.coefficientDiagonalSpace w))
    (hclass : IsSquare (diagonalUnitDeterminant w * ((-1 : Kˣ) ^ pairs * c))) :
    defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct pairs) =
      defectOrder (K := K) c := by
  unfold defectOrder
  rw [a.heADC_signedFullDefect_of_ambient w hlength pairs hpairs c ambient hclass]

/-- The endpoint order in Proposition 3.5 gives the uncapped signed-prefix lower bound. -/
theorem heADCEvenEndpoint_signedPrefix_defect {m : Nat} (a : GoodBONG q L (m + 2))
    (k : Nat) (hbound : 2 * k + 1 < m + 2) (hIntegral : Lattice.IsIntegral q L)
    (hendpoint : a.order ⟨2 * k + 1, hbound⟩ = -(2 * (ramificationIndex K : Int))) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.toBONG.signedEvenPrefixProduct (k + 1)) := by
  have C := a.heHu2022Proposition27iiiiv hIntegral ⟨2 * k + 1, hbound⟩
    (show Odd (2 * k + 1) from ⟨k, rfl⟩) hendpoint
  have H := C.alternatingPrefixDefect
  change _ ≤ a.truncatedPrefixDefect a
    ((-1) ^ ((2 * k + 1 - 1 + 2) / 2)) 0 (2 * k + 1 - 1 + 2) at H
  simp only [Nat.add_sub_cancel, show (2 * k + 2) / 2 = k + 1 by omega] at H
  have Hraw := H.trans (a.truncatedPrefixDefect_le_defect a
    ((-1) ^ (k + 1)) 0 (2 * k + 2))
  simpa [GoodBONG.prefixProduct, BONG.signedEvenPrefixProduct,
    show 2 * (k + 1) = 2 * k + 2 by omega] using Hraw

end BONG.GoodBONG

end Bong
