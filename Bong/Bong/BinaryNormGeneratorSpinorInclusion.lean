/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryNormGeneratorSquareClass
import Bong.Bong.BinarySpinorGroup
import Bong.Lattice.SpinorNormMultiplicative

/-!
# Norm-generator classes lie in the binary spinor group

This file proves the first assertion of Beli (2003), paragraph 3.16.  The
proof follows the paper: realize a class in `g(a)` by a norm generator and
take the product of its reflection with reflection in the BONG head.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

private theorem squareClass_mul (a c : Kˣ) :
    squareClass K a * squareClass K c = squareClass K (a * c) :=
  rfl

/-- The spinor class of reflection in the BONG head is represented by its
zeroth BONG value. -/
theorem reflectionSpinorClass_head (b : BONG V q L 2) :
    Lattice.reflectionSpinorClass b.head_isAnisotropic =
      squareClass K (b.valueUnit 0) := by
  unfold Lattice.reflectionSpinorClass
  congr 1
  apply Units.ext
  exact b.value_zero_eq_quadratic_head.symm

variable [BinaryNormGeneratorLocalLaws.{u, v} K]
  [BinarySpinorLocalLaws.{u, v} K]

/-- Beli (2003), paragraph 3.16: the field-square-class image of `g(a)` is
contained in `G(a)`. -/
theorem beliNormGeneratorSquareClassGroup_le_beliSpinorGroup
    (b : BONG V q L 2) :
    beliNormGeneratorSquareClassGroup K b.binaryParameter ≤
      beliSpinorGroup K b.binaryUnitSquareClass := by
  intro z hz
  rcases hz with ⟨c, hc, rfl⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  rcases
      b.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
        u hc with
    ⟨y, hy, hratio⟩
  let anisotropicY := b.isAnisotropic_of_isNormGenerator_binary hy
  let integralHead :=
    b.head_isNormGenerator.isIntegralReflection b.head_isAnisotropic
  let integralY := hy.isIntegralReflection anisotropicY
  let reflectionHead : Lattice.IntegralOrthogonalGroup q L :=
    Lattice.integralReflection b.head_isAnisotropic integralHead
  let reflectionY : Lattice.IntegralOrthogonalGroup q L :=
    Lattice.integralReflection anisotropicY integralY
  have hmem :
      valuationUnitClassToSquareClass K (valuationUnitClassHom K u) ∈
        Lattice.spinorNormImage (q := q) (L := L) := by
    refine ⟨Lattice.integralReflectionProduct
      b.head_isAnisotropic integralHead anisotropicY integralY, ?_⟩
    change Lattice.integralSpinorNorm (reflectionHead * reflectionY) = _
    rw [Lattice.integralSpinorNorm_mul]
    rw [Lattice.integralSpinorNorm_integralReflection,
      Lattice.integralSpinorNorm_integralReflection]
    rw [b.reflectionSpinorClass_head]
    change
      squareClass K (b.valueUnit 0) *
          squareClass K
            (Units.mk0 (q.quadratic y) anisotropicY) =
        squareClass K (u : Kˣ)
    rw [squareClass_mul]
    have hproduct :
        b.valueUnit 0 * Units.mk0 (q.quadratic y) anisotropicY =
          (u : Kˣ) * b.valueUnit 0 ^ 2 := by
      calc
        b.valueUnit 0 * Units.mk0 (q.quadratic y) anisotropicY =
            (Units.mk0 (q.quadratic y) anisotropicY /
                b.valueUnit 0) * b.valueUnit 0 ^ 2 := by
              simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
        _ = (u : Kˣ) * b.valueUnit 0 ^ 2 := by
          rw [← hratio]
          rfl
    rw [hproduct]
    exact squareClass_mul_square K (u : Kˣ) (b.valueUnit 0)
  rw [b.spinorNormImage_eq_beliSpinorGroup] at hmem
  exact hmem

end BONG

end Bong
