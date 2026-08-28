/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryModelIsometry

/-!
# Integral shear isometries of binary models

Changing the second standard vector by an integral multiple of the first does
not change the standard binary lattice.  On Gram matrices this replaces the
shear coefficient `c'` by `c' + t` while preserving the determinant parameter.
-/

namespace Bong

open Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The elementary coordinate shear `(x₀, x₁) ↦ (x₀ + t x₁, x₁)`. -/
def binaryShearLinearEquiv (t : K) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x 0 + t * x 1, x 1]
  invFun x := ![x 0 - t * x 1, x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem binaryShearLinearEquiv_apply_zero (t : K) (x : Fin 2 → K) :
    binaryShearLinearEquiv t x 0 = x 0 + t * x 1 :=
  rfl

@[simp]
theorem binaryShearLinearEquiv_apply_one (t : K) (x : Fin 2 → K) :
    binaryShearLinearEquiv t x 1 = x 1 :=
  rfl

/-- An integral elementary shear preserves the standard binary lattice. -/
theorem mem_binaryModelLattice_binaryShear_iff (t : K)
    (ht : t ∈ IntegerRing K) (x : Fin 2 → K) :
    x ∈ binaryModelLattice (K := K) ↔
      binaryShearLinearEquiv t x ∈ binaryModelLattice (K := K) := by
  have hcoords (z : Fin 2 → K) :
      z ∈ binaryModelLattice (K := K) ↔
        ∀ i, z i ∈ IntegerRing K := by
    rw [show binaryModelLattice (K := K) =
        Lattice.basisLattice (binaryModelBasis (K := K)) by rfl,
      Lattice.mem_basisLattice_iff_repr_mem_integerRing]
    simp [binaryModelBasis]
  rw [hcoords, hcoords]
  constructor
  · intro hx i
    fin_cases i
    · exact (IntegerRing K).add_mem _ _ (hx 0)
        ((IntegerRing K).mul_mem _ _ ht (hx 1))
    · exact hx 1
  · intro hx i
    fin_cases i
    · have hzero := hx 0
      have hone := hx 1
      simp only [binaryShearLinearEquiv_apply_zero] at hzero
      simp only [binaryShearLinearEquiv_apply_one] at hone
      have hmul := (IntegerRing K).mul_mem _ _ ht hone
      have hmem := (IntegerRing K).sub_mem hzero hmul
      have heq : (x 0 + t * x 1) - t * x 1 = x 0 := by ring
      rw [heq] at hmem
      simpa using hmem
    · simpa using hx 1

/-- Two rescaled binary models with equal determinant parameter and shears
differing integrally are isometric as lattices. -/
theorem rescaledBinaryModel_isIsometric_of_shear_sub_integral
    (u a : Kˣ) (c c' : K)
    (hsub : c - c' ∈ IntegerRing K) :
    Lattice.IsIsometric
      (QuadraticSpace.rescaleUnit u (QuadraticSpace.binaryModel a c))
      (QuadraticSpace.rescaleUnit u (QuadraticSpace.binaryModel a c'))
      (binaryModelLattice (K := K)) (binaryModelLattice (K := K)) := by
  let t : K := c - c'
  refine ⟨{
    toLinearEquiv := binaryShearLinearEquiv t
    map_mem := fun x => mem_binaryModelLattice_binaryShear_iff t hsub x
    map_bilin := ?_
  }⟩
  intro x y
  simp only [QuadraticSpace.rescaleUnit_bilin_apply]
  change (u : K) *
      (QuadraticSpace.binaryModel a c').bilin
        (binaryShearLinearEquiv t x) (binaryShearLinearEquiv t y) =
    (u : K) * (QuadraticSpace.binaryModel a c).bilin x y
  congr 1
  rw [QuadraticSpace.binaryModel, QuadraticSpace.binaryModel,
    Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  simp only [Fin.sum_univ_two,
    QuadraticSpace.binaryModelMatrix_zero_zero,
    QuadraticSpace.binaryModelMatrix_zero_one,
    QuadraticSpace.binaryModelMatrix_one_zero,
    QuadraticSpace.binaryModelMatrix_one_one,
    binaryShearLinearEquiv_apply_zero,
    binaryShearLinearEquiv_apply_one]
  dsimp [t]
  ring

end BONG

end Bong
