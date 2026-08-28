/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorPositiveReduction

/-!
# Primitive coordinates and diagonal integral reflections

For the standard binary lattice, a vector is primitive precisely when one
coordinate is a valuation unit.  We then specialize the general coordinate
criterion for an integral reflection to the diagonal model `X² + aY²`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- An integral nonunit is divisible by the fixed uniformizer inside the
valuation ring. -/
theorem uniformizer_inv_mul_mem_integerRing_of_mem_of_not_unit
    {x : K} (hx : x ∈ IntegerRing K)
    (hunit : ¬IsValuationUnit K x) :
    (uniformizer K)⁻¹ * x ∈ IntegerRing K := by
  by_cases hxZero : x = 0
  · simp [hxZero]
  let xu : Kˣ := Units.mk0 x hxZero
  have hxNonneg : 0 ≤ ordUnit K xu :=
    Lattice.ordUnit_nonneg_of_mem_integerRing xu (by simpa [xu] using hx)
  have hxNe : ordUnit K xu ≠ 0 := by
    intro hzero
    apply hunit
    exact (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hzero
  have hxOne : 1 ≤ ordUnit K xu := by omega
  apply (mem_integerRing_iff K).2
  change (0 : WithTop Int) ≤ ord K ((uniformizer K)⁻¹ * x)
  rw [ord_mul, AddValuation.map_inv, ord_uniformizer]
  change (0 : WithTop Int) ≤ -(1 : WithTop Int) + ord K (xu : K)
  rw [← coe_ordUnit]
  change ((0 : Int) : WithTop Int) ≤
    ((-1 + ordUnit K xu : Int) : WithTop Int)
  exact WithTop.coe_le_coe.mpr (by omega)

/-- A vector of the standard binary lattice is primitive exactly when at
least one coordinate is a valuation unit. -/
theorem primitive_binaryModelLattice_iff_coordinate_unit
    (z : Fin 2 → K) (hz : z ∈ binaryModelLattice (K := K)) :
    z ∉ Lattice.rescale (uniformizerUnit K)
        (binaryModelLattice (K := K)) ↔
      IsValuationUnit K (z 0) ∨ IsValuationUnit K (z 1) := by
  have hzCoords := (mem_binaryModelLattice_iff z).1 hz
  constructor
  · intro hprimitive
    by_contra hnoUnit
    have hzero : ¬IsValuationUnit K (z 0) := by
      intro h
      exact hnoUnit (Or.inl h)
    have hone : ¬IsValuationUnit K (z 1) := by
      intro h
      exact hnoUnit (Or.inr h)
    let y : Fin 2 → K := ![
      (uniformizer K)⁻¹ * z 0,
      (uniformizer K)⁻¹ * z 1]
    have hy : y ∈ binaryModelLattice (K := K) := by
      rw [mem_binaryModelLattice_iff]
      intro i
      fin_cases i
      · exact uniformizer_inv_mul_mem_integerRing_of_mem_of_not_unit
          (hzCoords 0) hzero
      · exact uniformizer_inv_mul_mem_integerRing_of_mem_of_not_unit
          (hzCoords 1) hone
    apply hprimitive
    rw [Lattice.mem_rescale_iff]
    refine ⟨y, hy, ?_⟩
    funext i
    fin_cases i <;>
      simp [y, smul_eq_mul, uniformizer_ne_zero]
  · intro hunit hscaled
    rw [Lattice.mem_rescale_iff] at hscaled
    rcases hscaled with ⟨y, hy, hyz⟩
    have hyCoords := (mem_binaryModelLattice_iff y).1 hy
    have hpiMax : IsInMaximalIdeal K (uniformizer K) := by
      rw [IsInMaximalIdeal, ord_uniformizer]
      norm_num
    have hcontra (i : Fin 2) (hi : IsValuationUnit K (z i)) : False := by
      have hcoordinate := congrArg (fun w : Fin 2 → K => w i) hyz
      change uniformizer K * y i = z i at hcoordinate
      have hyIntegral : Dyadic.IsIntegral K (y i) :=
        (mem_integerRing_iff K).1 (hyCoords i)
      have hmax := isInMaximalIdeal_mul_isIntegral K hpiMax hyIntegral
      rw [hcoordinate] at hmax
      rw [IsValuationUnit] at hi
      change (0 : WithTop Int) < ord K (z i) at hmax
      rw [hi] at hmax
      exact (lt_irrefl 0 hmax)
    exact hunit.elim (hcontra 0) (hcontra 1)

/-- In the diagonal model, a primitive vector defines an integral reflection
exactly when its two diagonal reflection coefficients are integral. -/
theorem isIntegralReflection_binaryDiagonal_iff_of_primitive
    (a : Kˣ) {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a 0).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a 0)
        (L := binaryModelLattice (K := K)) hz ↔
      2 * z 0 /
          (QuadraticSpace.binaryModel a 0).quadratic z ∈ IntegerRing K ∧
        2 * (a : K) * z 1 /
          (QuadraticSpace.binaryModel a 0).quadratic z ∈ IntegerRing K := by
  simpa [mul_assoc] using
    (isIntegralReflection_binaryModel_iff_of_primitive
      a 0 hz hzMem hzPrimitive)

end BONG

end Bong
