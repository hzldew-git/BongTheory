/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDefectAdaptedValues

/-!
# Defect-adapted shear vectors in an arbitrary binary BONG

The defect-adapted coefficient supplied by Beli's paragraph 3.9 is initially
stated in a standard binary model.  This file constructs the corresponding
integral vector in an arbitrary binary BONG and records its exact mixed and
quadratic values.  It is the geometric input used in the proof of Lemma 7.3.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The second basis vector after changing the normalized binary shear from
`b.binaryModelCoefficient` to `c`. -/
noncomputable def binaryAdaptedShearVector
    (b : BONG V q L 2) (c : K) : Fin 2 → K :=
  (c - b.binaryModelCoefficient) •
      QuadraticSpace.binaryModelFirst +
    QuadraticSpace.binaryModelSecond

theorem binaryAdaptedShearVector_mem
    (b : BONG V q L 2) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K) :
    b.binaryAdaptedShearVector c ∈ binaryModelLattice (K := K) := by
  rw [mem_binaryModelLattice_iff_coordinates]
  have hc₀ := b.binaryModelCoefficient_isAdmissibleWitness
  have hsub : c - b.binaryModelCoefficient ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing b.binaryParameter c
      b.binaryModelCoefficient htwo hdiag hc₀.1 hc₀.2
  intro i
  fin_cases i
  · simpa [binaryAdaptedShearVector,
      QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond] using hsub
  · simp [binaryAdaptedShearVector,
      QuadraticSpace.binaryModelFirst,
      QuadraticSpace.binaryModelSecond]

@[simp]
theorem normalizedBinaryModel_bilin_first_binaryAdaptedShearVector
    (b : BONG V q L 2) (c : K) :
    b.normalizedBinaryModelSpace.bilin
        QuadraticSpace.binaryModelFirst
        (b.binaryAdaptedShearVector c) =
      (b.valueUnit 0 : K) * c := by
  simp [binaryAdaptedShearVector, normalizedBinaryModelSpace]

@[simp]
theorem normalizedBinaryModel_quadratic_binaryAdaptedShearVector
    (b : BONG V q L 2) (c : K) :
    b.normalizedBinaryModelSpace.quadratic
        (b.binaryAdaptedShearVector c) =
      (b.valueUnit 0 : K) *
        (c ^ 2 + (b.binaryParameter : K)) := by
  rw [normalizedBinaryModelSpace,
    QuadraticSpace.rescaleUnit_quadratic,
    QuadraticSpace.binaryModel_quadratic_apply]
  simp [binaryAdaptedShearVector,
    QuadraticSpace.binaryModelFirst,
    QuadraticSpace.binaryModelSecond]
  left
  ring

/-- The defect-adapted shear vector transported into the original binary
lattice. -/
noncomputable def binaryAdaptedShearAmbientVector
    (b : BONG V q L 2) (c : K) : V :=
  b.normalizedBinaryModelLatticeIsometry.toLinearEquiv
    (b.binaryAdaptedShearVector c)

theorem binaryAdaptedShearAmbientVector_mem
    (b : BONG V q L 2) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (b.binaryParameter : K) ∈ IntegerRing K) :
    b.binaryAdaptedShearAmbientVector c ∈ L := by
  apply (b.normalizedBinaryModelLatticeIsometry.map_mem
    (b.binaryAdaptedShearVector c)).1
  exact b.binaryAdaptedShearVector_mem c htwo hdiag

@[simp]
theorem bilin_head_binaryAdaptedShearAmbientVector
    (b : BONG V q L 2) (c : K) :
    q.bilin b.head (b.binaryAdaptedShearAmbientVector c) =
      (b.valueUnit 0 : K) * c := by
  let f := b.normalizedBinaryModelLatticeIsometry
  rw [← b.normalizedBinaryModelLatticeIsometry_apply_first]
  exact (f.map_bilin QuadraticSpace.binaryModelFirst
    (b.binaryAdaptedShearVector c)).trans
      (b.normalizedBinaryModel_bilin_first_binaryAdaptedShearVector c)

@[simp]
theorem quadratic_binaryAdaptedShearAmbientVector
    (b : BONG V q L 2) (c : K) :
    q.quadratic (b.binaryAdaptedShearAmbientVector c) =
      (b.valueUnit 0 : K) *
        (c ^ 2 + (b.binaryParameter : K)) := by
  let f := b.normalizedBinaryModelLatticeIsometry
  exact (f.map_quadratic (b.binaryAdaptedShearVector c)).trans
    (b.normalizedBinaryModel_quadratic_binaryAdaptedShearVector c)

end BONG

end Bong
