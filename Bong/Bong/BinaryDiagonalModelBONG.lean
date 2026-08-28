/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryInvariant
import Bong.Bong.UnaryBinaryModel
import Bong.Lattice.FormRescale

/-!
# The canonical BONG of a scaled binary diagonal model

The explicit binary Gram model has a BONG with values `1,a`.  After
rescaling the quadratic form by `first` and taking
`a = second / first`, the first standard vector is still a norm generator.
Extending that prescribed head gives a genuine BONG of the scaled model.
Its second value need not be chosen literally equal to `second`, but its
valuation order is forced to be `ord(second)` by the volume identity.
-/

namespace Bong

open Dyadic
open Module

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A BONG of the concrete binary lattice `[first, second]`, with the
distinguished first standard vector as its head. -/
noncomputable def binaryDiagonalModelBONG
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    BONG (Fin 2 → K)
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K)) 2 := by
  let a : Kˣ := second / first
  let c : K := admissibleBinaryShear a hadmissible
  have htwo : (2 : K) * c ∈ IntegerRing K :=
    two_mul_admissibleBinaryShear_mem a hadmissible
  have hdiag : c ^ 2 + (a : K) ∈ IntegerRing K :=
    admissibleBinaryShear_sq_add_mem a hadmissible
  have generator : Lattice.IsNormGenerator
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K))
      QuadraticSpace.binaryModelFirst := by
    change Lattice.IsNormGenerator
      ((QuadraticSpace.binaryModel a c).rescaleUnit first)
      (binaryModelLattice (K := K))
      QuadraticSpace.binaryModelFirst
    exact (binaryModelFirst_isNormGenerator a c htwo hdiag).rescaleQuadraticUnit first
  have anisotropic :
      (binaryDiagonalModelSpace first second hadmissible).IsAnisotropic
        QuadraticSpace.binaryModelFirst := by
    change ((QuadraticSpace.binaryModel a c).rescaleUnit first).IsAnisotropic
      QuadraticSpace.binaryModelFirst
    exact (binaryModelFirst_isAnisotropic a c).rescaleUnit first
  exact BONG.ofNormGeneratorBinary
    (binaryDiagonalModelSpace first second hadmissible)
    (binaryDiagonalModelLattice (K := K))
    QuadraticSpace.binaryModelFirst generator anisotropic (by simp)

/-- The prescribed head of the scaled binary model BONG. -/
@[simp]
theorem binaryDiagonalModelBONG_head
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelBONG first second hadmissible).head =
      QuadraticSpace.binaryModelFirst := by
  unfold binaryDiagonalModelBONG
  apply BONG.head_ofNormGeneratorBinary

/-- The first value of the scaled model BONG is exactly `first`. -/
@[simp]
theorem binaryDiagonalModelBONG_value_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelBONG first second hadmissible).value 0 =
      (first : K) := by
  rw [(binaryDiagonalModelBONG first second hadmissible).value_zero_eq_quadratic_head,
    binaryDiagonalModelBONG_head]
  exact binaryDiagonalModelSpace_quadratic_first first second hadmissible

/-- The first order of the scaled model is `ord(first)`. -/
@[simp]
theorem binaryDiagonalModelBONG_order_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelBONG first second hadmissible).order 0 =
      ordUnit K first := by
  apply WithTop.coe_injective
  rw [BONG.coe_order, binaryDiagonalModelBONG_value_zero, coe_ordUnit]

/-- The volume order of the scaled binary model is the sum of the two
advertised coefficient orders. -/
theorem volumeOrder_binaryDiagonalModel
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    Lattice.volumeOrder
        (binaryDiagonalModelSpace first second hadmissible)
        (binaryDiagonalModelLattice (K := K)) =
      ordUnit K first + ordUnit K second := by
  let a : Kˣ := second / first
  let c : K := admissibleBinaryShear a hadmissible
  have htwo : (2 : K) * c ∈ IntegerRing K :=
    two_mul_admissibleBinaryShear_mem a hadmissible
  have hdiag : c ^ 2 + (a : K) ∈ IntegerRing K :=
    admissibleBinaryShear_sq_add_mem a hadmissible
  let base := binaryExactModelBONG a c htwo hdiag
  have hzero : base.valueUnit (0 : Fin 2) = 1 := by
    apply Units.ext
    exact binaryExactModelBONG_value_zero a c htwo hdiag
  have hone : base.valueUnit (1 : Fin 2) = a := by
    apply Units.ext
    exact binaryExactModelBONG_value_one a c htwo hdiag
  have hbase : Lattice.volumeOrder (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) = ordUnit K a := by
    rw [base.volumeOrder_eq_ordUnit_valueProduct,
      base.valueProduct_fin_two, hzero, hone, one_mul]
  change Lattice.volumeOrder
      ((QuadraticSpace.binaryModel a c).rescaleUnit first)
      (binaryModelLattice (K := K)) = _
  rw [Lattice.volumeOrder_rescaleUnit, hbase]
  simp only [finrank_fin_fun, Nat.cast_ofNat]
  dsimp only [a]
  rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
  ring

/-- The second order is forced to be `ord(second)`. -/
@[simp]
theorem binaryDiagonalModelBONG_order_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelBONG first second hadmissible).order 1 =
      ordUnit K second := by
  let b := binaryDiagonalModelBONG first second hadmissible
  have hrelative := b.binaryRelativeOrder_eq_orderGap
  have hvolume := volumeOrder_binaryDiagonalModel first second hadmissible
  have hzero := binaryDiagonalModelBONG_order_zero first second hadmissible
  change b.order 1 = ordUnit K second
  unfold binaryRelativeOrder binaryOrderGap at hrelative
  change Lattice.volumeOrder
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K)) - 2 * b.order 0 =
        b.order 1 - b.order 0 at hrelative
  change b.order 0 = ordUnit K first at hzero
  rw [hvolume, hzero] at hrelative
  omega

/-- The canonical binary model BONG, bundled as a good BONG.  Goodness is
automatic in rank two. -/
noncomputable def binaryDiagonalModelGoodBONG
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    GoodBONG
      (binaryDiagonalModelSpace first second hadmissible)
      (binaryDiagonalModelLattice (K := K)) 2 where
  toBONG := binaryDiagonalModelBONG first second hadmissible
  good := BONG.isGood_binary _

@[simp]
theorem binaryDiagonalModelGoodBONG_order_zero
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelGoodBONG first second hadmissible).order 0 =
      ordUnit K first :=
  binaryDiagonalModelBONG_order_zero first second hadmissible

@[simp]
theorem binaryDiagonalModelGoodBONG_order_one
    (first second : Kˣ)
    (hadmissible : IsBinaryParameterAdmissible (second / first)) :
    (binaryDiagonalModelGoodBONG first second hadmissible).order 1 =
      ordUnit K second :=
  binaryDiagonalModelBONG_order_one first second hadmissible

end BONG

end Bong
