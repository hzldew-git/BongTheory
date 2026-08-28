/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Binary
import Bong.Bong.SectionTwo

/-!
# The determinant-normalized invariant of a binary BONG

For a binary lattice with first BONG value `a₁`, Beli (2003), Definition 3
defines `a(L) = det(L) * a₁⁻²`, modulo squares of valuation units.
Lemma 3.1 identifies this invariant with the binary BONG parameter `a₂ / a₁`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- Beli's determinant-normalized binary invariant. -/
noncomputable def binaryDeterminantInvariant (b : BONG V q L 2) :
    UnitSquareClass K :=
  Lattice.determinantClass q L *
    (unitSquareClass K (b.valueUnit 0))⁻¹ ^ 2

/-- In rank two, the BONG value product is the product of its two entries. -/
theorem valueProduct_fin_two (b : BONG V q L 2) :
    b.valueProduct = b.valueUnit 0 * b.valueUnit 1 := by
  apply Units.ext
  simp [coe_valueProduct, Fin.prod_univ_succ]

/-- The first value of a binary BONG generates the norm ideal. -/
theorem normIdeal_eq_principal_value_zero (b : BONG V q L 2) :
    Lattice.normIdeal q L =
      Lattice.principalIdeal (K := K) (b.value 0) := by
  rw [b.value_zero_eq_quadratic_head]
  exact b.head_isNormGenerator.normIdeal_eq

/-- Beli (2003), Lemma 3.1: `a(L)` is represented by `a₂ / a₁`. -/
theorem binaryDeterminantInvariant_eq_parameter (b : BONG V q L 2) :
    b.binaryDeterminantInvariant = b.binaryUnitSquareClass := by
  rw [binaryDeterminantInvariant, b.determinantClass_eq_valueProduct,
    valueProduct_fin_two, unitSquareClass_mul]
  change unitSquareClass K (b.valueUnit 0) *
      unitSquareClass K (b.valueUnit 1) *
        (unitSquareClass K (b.valueUnit 0))⁻¹ ^ 2 =
    unitSquareClass K (b.valueUnit 1 / b.valueUnit 0)
  rw [show b.valueUnit 1 / b.valueUnit 0 =
    b.valueUnit 1 * (b.valueUnit 0)⁻¹ by rfl]
  rw [unitSquareClass_mul]
  change unitSquareClass K (b.valueUnit 0) *
      unitSquareClass K (b.valueUnit 1) *
        (unitSquareClass K (b.valueUnit 0))⁻¹ ^ 2 =
    unitSquareClass K (b.valueUnit 1) *
      (unitSquareClass K (b.valueUnit 0))⁻¹
  rw [mul_comm (unitSquareClass K (b.valueUnit 0))]
  group

/-- The binary parameter is independent of the chosen BONG of the lattice. -/
theorem binaryUnitSquareClass_eq (b c : BONG V q L 2) :
    b.binaryUnitSquareClass = c.binaryUnitSquareClass := by
  have hprincipal : Lattice.principalIdeal (K := K) (b.value 0) =
      Lattice.principalIdeal (K := K) (c.value 0) :=
    b.normIdeal_eq_principal_value_zero.symm.trans
      c.normIdeal_eq_principal_value_zero
  rcases Lattice.exists_valuationUnit_mul_eq_of_principalIdeal_eq
      (b.valueUnit 0) (c.valueUnit 0) hprincipal with ⟨u, hu, huc⟩
  have huInv : IsValuationUnit K ((u⁻¹ : Kˣ) : K) := by
    simpa [IsValuationUnit, AddValuation.map_inv, hu]
  have hsquare :
      unitSquareClass K ((c.valueUnit 0)⁻¹ ^ 2) =
        unitSquareClass K ((b.valueUnit 0)⁻¹ ^ 2) := by
    rw [← huc]
    calc
      unitSquareClass K ((u * b.valueUnit 0)⁻¹ ^ 2) =
          unitSquareClass K
            ((b.valueUnit 0)⁻¹ ^ 2 * u⁻¹ ^ 2) := by
        congr 1
        simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
      _ = unitSquareClass K ((b.valueUnit 0)⁻¹ ^ 2) :=
        unitSquareClass_mul_unit_square K
          ((b.valueUnit 0)⁻¹ ^ 2) u⁻¹ huInv
  have hclass :
      (unitSquareClass K (c.valueUnit 0))⁻¹ ^ 2 =
        (unitSquareClass K (b.valueUnit 0))⁻¹ ^ 2 := by
    change unitSquareClass K ((c.valueUnit 0)⁻¹ ^ 2) =
      unitSquareClass K ((b.valueUnit 0)⁻¹ ^ 2)
    exact hsquare
  rw [← b.binaryDeterminantInvariant_eq_parameter,
    ← c.binaryDeterminantInvariant_eq_parameter]
  unfold binaryDeterminantInvariant
  rw [hclass]

/-- The refined determinant identity also identifies the volume order. -/
theorem volumeOrder_eq_ordUnit_valueProduct (b : BONG V q L 2) :
    Lattice.volumeOrder q L = ordUnit K b.valueProduct := by
  have hclass := b.determinantClass_eq_valueProduct
  change unitSquareClass K (Lattice.determinantUnit q L) =
    unitSquareClass K b.valueProduct at hclass
  have hord := ordUnit_eq_of_unitSquareClass_eq (K := K) hclass
  calc
    Lattice.volumeOrder q L =
        ordUnit K (Lattice.determinantUnit q L) := by
      apply WithTop.coe_injective
      rw [Lattice.coe_volumeOrder, coe_ordUnit,
        Lattice.coe_determinantUnit]
    _ = ordUnit K b.valueProduct := hord

/-- Beli's integer `R(L) = ord(vol L) - 2 ord(nL)`, using a BONG norm generator. -/
noncomputable def binaryRelativeOrder (b : BONG V q L 2) : Int :=
  Lattice.volumeOrder q L - 2 * b.order 0

/-- Beli (2003), Definition 3: `R(L) = R₂ - R₁`. -/
theorem binaryRelativeOrder_eq_orderGap (b : BONG V q L 2) :
    b.binaryRelativeOrder = b.binaryOrderGap := by
  rw [binaryRelativeOrder, b.volumeOrder_eq_ordUnit_valueProduct,
    valueProduct_fin_two, ordUnit_mul]
  change ordUnit K (b.valueUnit 0) + ordUnit K (b.valueUnit 1) -
      2 * ordUnit K (b.valueUnit 0) =
    ordUnit K (b.valueUnit 1) - ordUnit K (b.valueUnit 0)
  ring

/-- The order gap of a binary BONG depends only on the lattice. -/
theorem binaryOrderGap_eq (b c : BONG V q L 2) :
    b.binaryOrderGap = c.binaryOrderGap := by
  rw [← b.binaryParameterOrder_eq_orderGap,
    ← c.binaryParameterOrder_eq_orderGap]
  change ordUnit K b.binaryParameter = ordUnit K c.binaryParameter
  apply ordUnit_eq_of_unitSquareClass_eq (K := K)
  exact b.binaryUnitSquareClass_eq c

/-- The second BONG value is the determinant divided by the first value,
in the refined unit-square-class group. -/
theorem valueUnitSquareClass_one_eq_determinant_div_zero
    (b : BONG V q L 2) :
    unitSquareClass K (b.valueUnit 1) =
      Lattice.determinantClass q L *
        (unitSquareClass K (b.valueUnit 0))⁻¹ := by
  have hdet := b.determinantClass_eq_valueProduct
  rw [b.valueProduct_fin_two, unitSquareClass_mul] at hdet
  rw [hdet]
  simp [mul_assoc]

end BONG

end Bong
