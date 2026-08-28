/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Bong.BinaryInvariant
import Bong.Dyadic.UnitsCongruentModuloAlgebra

/-!
# The binary weight bound in determinant form

Beli (2009), Lemma 2.14 expresses the weight ideal through the first alpha
invariant.  The defining left-defect candidate then rewrites that estimate
in the basis-free form used in Beli (2019), Lemma 5.13:

`ord w(L) ≤ R₂ + d(-det L)`.

The determinant on the right is the refined determinant unit of the binary
lattice.  The proof below explicitly transports the adjacent BONG product
through its determinant square class; no equality of arbitrary determinant
representatives is assumed.
-/

set_option maxHeartbeats 800000

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The weight order of a binary lattice is bounded by its second BONG
order plus the defect of the adjacent determinant product.  This estimate
does not require choosing one of the increasing/decreasing orientations. -/
theorem weightIdealOrder_le_order_one_add_adjacentDefect
    (b : GoodBONG q L 2) :
    (((Lattice.weightIdealOrder q L : ℚ) : WithTop ℚ)) ≤
      ((b.order 1 : ℚ) : WithTop ℚ) + b.adjacentDefect 0 := by
  have hformula := b.lemma214_weightIdealOrder_all
  have hweightQ : (Lattice.weightIdealOrder q L : ℚ) ≤
      (b.order 0 : ℚ) + b.alphaValue 0 := by
    rw [hformula]
    exact min_le_left _ _
  have hweight : (((Lattice.weightIdealOrder q L : ℚ) : WithTop ℚ)) ≤
      ((b.order 0 : ℚ) : WithTop ℚ) +
        ((b.alphaValue 0 : ℚ) : WithTop ℚ) := by
    exact_mod_cast hweightQ
  have halpha := b.alpha_le_leftDefectCandidate
    (i := (0 : Fin 1)) (j := (0 : Fin 1)) le_rfl
  rw [← b.coe_alphaValue] at halpha
  have halpha' : ((b.alphaValue 0 : ℚ) : WithTop ℚ) ≤
      ((((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ)) +
        b.adjacentDefect 0 := by
    simpa only [leftDefectCandidate, orderGap, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.zero_eta] using halpha
  calc
    (((Lattice.weightIdealOrder q L : ℚ) : WithTop ℚ)) ≤
        ((b.order 0 : ℚ) : WithTop ℚ) +
          ((b.alphaValue 0 : ℚ) : WithTop ℚ) := hweight
    _ ≤ ((b.order 0 : ℚ) : WithTop ℚ) +
          (((((b.order 1 - b.order 0 : Int) : ℚ) : WithTop ℚ)) +
            b.adjacentDefect 0) := add_le_add le_rfl halpha'
    _ = ((b.order 1 : ℚ) : WithTop ℚ) + b.adjacentDefect 0 := by
      rw [← add_assoc]
      congr 1
      norm_cast
      ring

/-- The adjacent defect of a binary good BONG is the defect of the negative
refined determinant representative. -/
theorem adjacentDefect_eq_defectOrder_neg_determinantUnit
    (b : GoodBONG q L 2) :
    b.adjacentDefect 0 =
      defectOrder (K := K) (-(Lattice.determinantUnit q L)) := by
  have hdet := b.toBONG.determinantClass_eq_valueProduct
  rw [b.toBONG.valueProduct_fin_two] at hdet
  have hclass :
      unitSquareClass K (b.adjacentProduct 0) =
        unitSquareClass K (-(Lattice.determinantUnit q L)) := by
    unfold adjacentProduct
    change unitSquareClass K (-(b.valueUnit 0 * b.valueUnit 1)) = _
    rw [show -(b.valueUnit 0 * b.valueUnit 1) =
        (-1 : Kˣ) * (b.valueUnit 0 * b.valueUnit 1) by simp,
      show -(Lattice.determinantUnit q L) =
        (-1 : Kˣ) * Lattice.determinantUnit q L by simp]
    have hprod : unitSquareClass K (b.valueUnit 0 * b.valueUnit 1) =
        Lattice.determinantClass q L := hdet.symm
    simpa only [unitSquareClass_mul, Lattice.determinantClass] using
      congrArg (fun z : UnitSquareClass K ↦
        unitSquareClass K (-1 : Kˣ) * z) hprod
  obtain ⟨s, hs⟩ := exists_square_mul_eq_of_unitSquareClass_eq
    (K := K) (b.adjacentProduct 0) (-(Lattice.determinantUnit q L)) hclass
  unfold adjacentDefect
  rw [← hs, defectOrder_mul_square]

/-- Beli's determinant form of the binary weight inequality:
`ord w(L) ≤ R₂ + d(-det L)`. -/
theorem weightIdealOrder_le_order_one_add_defect_neg_determinantUnit
    (b : GoodBONG q L 2) :
    (((Lattice.weightIdealOrder q L : ℚ) : WithTop ℚ)) ≤
      ((b.order 1 : ℚ) : WithTop ℚ) +
        defectOrder (K := K) (-(Lattice.determinantUnit q L)) := by
  rw [← b.adjacentDefect_eq_defectOrder_neg_determinantUnit]
  exact b.weightIdealOrder_le_order_one_add_adjacentDefect

end BONG.GoodBONG

end Bong
