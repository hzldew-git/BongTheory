/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorReflectionReduction
import Bong.Lattice.PrimitiveBinarySpinor
import Bong.Lattice.ReflectionScaling

/-!
# Integral reflections in the explicit binary model

For a primitive vector of the standard binary lattice, integrality of its
reflection is equivalent to the two familiar coordinate divisibility tests.
This is the exact elementary interface used in the calculations of Hsia and
Xu; the primitivity hypothesis is essential for the converse.
-/

namespace Bong

open Dyadic

namespace QuadraticSpace

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Coordinate formula for the bilinear form in the binary model. -/
theorem binaryModel_bilin_apply (a : Kˣ) (c : K)
    (z y : Fin 2 → K) :
    (binaryModel a c).bilin z y =
      z 0 * y 0 + c * (z 0 * y 1 + z 1 * y 0) +
        (c ^ 2 + (a : K)) * z 1 * y 1 := by
  rw [binaryModel, Matrix.toBilin'_apply]
  simp [Fin.sum_univ_two]
  ring

/-- Pairing with the first standard vector in the binary model. -/
theorem binaryModel_bilin_apply_first (a : Kˣ) (c : K)
    (z : Fin 2 → K) :
    (binaryModel a c).bilin z binaryModelFirst = z 0 + c * z 1 := by
  rw [binaryModel_bilin_apply]
  simp [binaryModelFirst]

/-- Pairing with the second standard vector in the binary model. -/
theorem binaryModel_bilin_apply_second (a : Kˣ) (c : K)
    (z : Fin 2 → K) :
    (binaryModel a c).bilin z binaryModelSecond =
      c * z 0 + (c ^ 2 + (a : K)) * z 1 := by
  rw [binaryModel_bilin_apply]
  simp [binaryModelSecond]

end QuadraticSpace

namespace BONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Square classes of quadratic values of primitive vectors whose two
reflection coefficients are integral.  This is the coordinate set computed
in Hsia (1975) and Xu (1989, 1993). -/
noncomputable def binaryPrimitiveReflectionClassSet
    (a : Kˣ) (c : K) : Set (SquareClass K) :=
  {A | ∃ (z : Fin 2 → K)
      (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z),
    z ∈ binaryModelLattice (K := K) ∧
    z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K)) ∧
    2 * (z 0 + c * z 1) /
        (QuadraticSpace.binaryModel a c).quadratic z ∈ IntegerRing K ∧
    2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
        (QuadraticSpace.binaryModel a c).quadratic z ∈ IntegerRing K ∧
    squareClass K
      (Units.mk0 ((QuadraticSpace.binaryModel a c).quadratic z) hz) = A}

/-- For a primitive standard-lattice vector, the reflection preserves the
lattice exactly when its two basis reflection coefficients are integral. -/
theorem isIntegralReflection_binaryModel_iff_of_primitive
    (a : Kˣ) (c : K) {z : Fin 2 → K}
    (hz : (QuadraticSpace.binaryModel a c).IsAnisotropic z)
    (hzMem : z ∈ binaryModelLattice (K := K))
    (hzPrimitive : z ∉ Lattice.rescale (uniformizerUnit K)
      (binaryModelLattice (K := K))) :
    Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) hz ↔
      2 * (z 0 + c * z 1) /
          (QuadraticSpace.binaryModel a c).quadratic z ∈ IntegerRing K ∧
        2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
          (QuadraticSpace.binaryModel a c).quadratic z ∈ IntegerRing K := by
  constructor
  · intro hIntegral
    have hfirst := hIntegral QuadraticSpace.binaryModelFirst
      (binaryModelFirst_mem a c)
    have hsecond := hIntegral QuadraticSpace.binaryModelSecond
      (binaryModelSecond_mem a c)
    constructor
    · apply Lattice.mem_integerRing_of_smul_mem_of_not_mem_uniformizer_rescale
        (binaryModelLattice (K := K)) hzMem hzPrimitive
      have hdiff := (binaryModelLattice (K := K)).sub_mem
        (binaryModelFirst_mem a c) hfirst
      rw [QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.binaryModel_bilin_apply_first] at hdiff
      have heq :
          QuadraticSpace.binaryModelFirst -
              (QuadraticSpace.binaryModelFirst -
                (2 * (z 0 + c * z 1) /
                  (QuadraticSpace.binaryModel a c).quadratic z) • z) =
            (2 * (z 0 + c * z 1) /
              (QuadraticSpace.binaryModel a c).quadratic z) • z := by
        abel
      rwa [heq] at hdiff
    · apply Lattice.mem_integerRing_of_smul_mem_of_not_mem_uniformizer_rescale
        (binaryModelLattice (K := K)) hzMem hzPrimitive
      have hdiff := (binaryModelLattice (K := K)).sub_mem
        (binaryModelSecond_mem a c) hsecond
      rw [QuadraticSpace.reflectionLinearEquiv_apply,
        QuadraticSpace.binaryModel_bilin_apply_second] at hdiff
      have heq :
          QuadraticSpace.binaryModelSecond -
              (QuadraticSpace.binaryModelSecond -
                (2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
                  (QuadraticSpace.binaryModel a c).quadratic z) • z) =
            (2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
              (QuadraticSpace.binaryModel a c).quadratic z) • z := by
        abel
      rwa [heq] at hdiff
  · rintro ⟨hfirst, hsecond⟩
    apply Lattice.isIntegralReflection_of_coefficient_mem_integerRing
      hz hzMem
    intro y hy
    have hyCoords := (mem_binaryModelLattice_iff y).1 hy
    have hyDecompose :
        y = y 0 • QuadraticSpace.binaryModelFirst +
          y 1 • QuadraticSpace.binaryModelSecond := by
      ext i
      fin_cases i <;>
        simp [QuadraticSpace.binaryModelFirst,
          QuadraticSpace.binaryModelSecond]
    have hcoefficient :
        2 * (QuadraticSpace.binaryModel a c).bilin z y /
            (QuadraticSpace.binaryModel a c).quadratic z =
          y 0 * (2 * (z 0 + c * z 1) /
            (QuadraticSpace.binaryModel a c).quadratic z) +
          y 1 * (2 * (c * z 0 + (c ^ 2 + (a : K)) * z 1) /
            (QuadraticSpace.binaryModel a c).quadratic z) := by
      rw [QuadraticSpace.binaryModel_bilin_apply]
      field_simp [hz]
      ring
    rw [hcoefficient]
    exact (IntegerRing K).add_mem _ _
      ((IntegerRing K).mul_mem _ _ (hyCoords 0) hfirst)
      ((IntegerRing K).mul_mem _ _ (hyCoords 1) hsecond)

/-- The proper spinor image of an admissible explicit binary model is exactly
the coordinate set of primitive integral-reflection values. -/
theorem spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.spinorNormImage
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) =
      binaryPrimitiveReflectionClassSet a c := by
  let hfirst := binaryModelFirst_isAnisotropic a c
  let hfirstIntegral : Lattice.IsIntegralReflection
      (q := QuadraticSpace.binaryModel a c)
      (L := binaryModelLattice (K := K)) hfirst :=
    (binaryModelFirst_isNormGenerator a c htwo hdiag).isIntegralReflection
      hfirst
  rw [Lattice.spinorNormImage_eq_fixed_mul_primitiveReflectionClasses
    (q := QuadraticSpace.binaryModel a c)
    (L := binaryModelLattice (K := K)) (by simp) hfirst hfirstIntegral]
  ext A
  constructor
  · rintro ⟨z, hz, hzMem, hzPrimitive, hzIntegral, hclass⟩
    have hcoefficients :=
      (isIntegralReflection_binaryModel_iff_of_primitive
        a c hz hzMem hzPrimitive).1 hzIntegral
    refine ⟨z, hz, hzMem, hzPrimitive, hcoefficients.1,
      hcoefficients.2, ?_⟩
    have hfirstClass :
        Lattice.reflectionSpinorClass (q := QuadraticSpace.binaryModel a c)
            hfirst = 1 := by
      unfold Lattice.reflectionSpinorClass
      have hunit :
          Units.mk0
              ((QuadraticSpace.binaryModel a c).quadratic
                QuadraticSpace.binaryModelFirst) hfirst = (1 : Kˣ) := by
        apply Units.ext
        simp
      rw [hunit]
      rfl
    rw [hfirstClass, one_mul] at hclass
    exact hclass
  · rintro ⟨z, hz, hzMem, hzPrimitive, hfirstCoefficient,
      hsecondCoefficient, hclass⟩
    have hzIntegral : Lattice.IsIntegralReflection
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) hz :=
      (isIntegralReflection_binaryModel_iff_of_primitive
        a c hz hzMem hzPrimitive).2
          ⟨hfirstCoefficient, hsecondCoefficient⟩
    refine ⟨z, hz, hzMem, hzPrimitive, hzIntegral, ?_⟩
    have hfirstClass :
        Lattice.reflectionSpinorClass (q := QuadraticSpace.binaryModel a c)
            hfirst = 1 := by
      unfold Lattice.reflectionSpinorClass
      have hunit :
          Units.mk0
              ((QuadraticSpace.binaryModel a c).quadratic
                QuadraticSpace.binaryModelFirst) hfirst = (1 : Kˣ) := by
        apply Units.ext
        simp
      rw [hunit]
      rfl
    rw [hfirstClass, one_mul]
    exact hclass

/-- The proper spinor image of an arbitrary binary BONG is the explicit set
of square classes represented by primitive integral-reflection vectors in its
unscaled standard binary model. -/
theorem spinorNormImage_eq_primitiveReflectionClassSet
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    Lattice.spinorNormImage (q := q) (L := L) =
      binaryPrimitiveReflectionClassSet b.binaryParameter
        b.binaryModelCoefficient := by
  rw [b.spinorNormImage_eq_binaryModel]
  exact spinorNormImage_binaryModel_eq_primitiveReflectionClassSet
    b.binaryParameter b.binaryModelCoefficient
    b.binaryModelCoefficient_isAdmissibleWitness.1
    b.binaryModelCoefficient_isAdmissibleWitness.2

end BONG

end Bong
