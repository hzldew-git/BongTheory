/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPSmithNormalForm
import Bong.Lattice.AdjoinVector
import Bong.Lattice.BasisUnits

/-!
# A primitive generator for an index-uniformizer inclusion

Smith normal form supplies a basis of the larger lattice in which the smaller
lattice is obtained by multiplying one coordinate by the uniformizer.  This
file packages the corresponding primitive vector of the smaller lattice and
proves that dividing it by the uniformizer generates the larger lattice.

This is the algebraic first paragraph in the proof of Beli (2019), Lemma 5.1.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The coordinatewise units that divide only coordinate `i` by the selected
uniformizer. -/
noncomputable def coordinateInverseScaleUnits
    (i : Fin (finrank K V)) : Fin (finrank K V) → Kˣ :=
  Function.update (fun _ ↦ 1) i (uniformizerUnit K)⁻¹

/-- Divide one vector of a field basis by the selected uniformizer. -/
noncomputable def coordinateInverseScaleBasis
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    Basis (Fin (finrank K V)) K V :=
  b.unitsSMul (coordinateInverseScaleUnits (K := K) i)

@[simp]
theorem coordinateInverseScaleBasis_apply_same
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    coordinateInverseScaleBasis b i i =
      (((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i := by
  rw [coordinateInverseScaleBasis, Basis.unitsSMul_apply]
  simp [coordinateInverseScaleUnits, Function.update, Units.smul_def]

@[simp]
theorem coordinateInverseScaleBasis_apply_of_ne
    (b : Basis (Fin (finrank K V)) K V) {i j : Fin (finrank K V)}
    (hji : j ≠ i) :
    coordinateInverseScaleBasis b i j = b j := by
  rw [coordinateInverseScaleBasis, Basis.unitsSMul_apply]
  simp [coordinateInverseScaleUnits, Function.update, hji]

/-- Scaling back the coordinate that was divided by the uniformizer recovers
the original basis. -/
theorem coordinateScaleBasis_inverse_eq
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    coordinateScaleBasis (coordinateInverseScaleBasis b i) i = b := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    rw [coordinateScaleBasis_apply_same,
      coordinateInverseScaleBasis_apply_same, ← mul_smul]
    simp [uniformizer_ne_zero K]
  · rw [coordinateScaleBasis_apply_of_ne _ hji,
      coordinateInverseScaleBasis_apply_of_ne _ hji]

/-- The original basis lattice is contained in the lattice obtained by
dividing one basis vector by the uniformizer. -/
theorem basisLattice_le_coordinateInverseScaleBasis
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    basisLattice b ≤ basisLattice (coordinateInverseScaleBasis b i) := by
  have h := basisLattice_coordinateScaleBasis_le
    (coordinateInverseScaleBasis b i) i
  rw [coordinateScaleBasis_inverse_eq] at h
  exact h

/-- Dividing one basis coordinate by the uniformizer lowers the volume order
by two. -/
theorem volumeOrder_basisLattice_coordinateInverseScaleBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    volumeOrder q (basisLattice (coordinateInverseScaleBasis b i)) =
      volumeOrder q (basisLattice b) - 2 := by
  have h := volumeOrder_basisLattice_coordinateScaleBasis q
    (coordinateInverseScaleBasis b i) i
  rw [coordinateScaleBasis_inverse_eq] at h
  omega

/-- Multiplying the inverse-scaled basis lattice by the uniformizer places it
inside the original basis lattice. -/
theorem rescale_uniformizer_coordinateInverseScaleBasis_le
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    rescale (uniformizerUnit K)
        (basisLattice (coordinateInverseScaleBasis b i)) ≤
      basisLattice b := by
  rw [rescale_basisLattice]
  change Submodule.span (IntegerRing K)
      (Set.range (uniformizerUnit K • coordinateInverseScaleBasis b i)) ≤
    Submodule.span (IntegerRing K) (Set.range b)
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Basis.smul_apply]
  by_cases hji : j = i
  · subst j
    rw [coordinateInverseScaleBasis_apply_same]
    change uniformizer K •
      ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i) ∈
        Submodule.span (IntegerRing K) (Set.range b)
    rw [← mul_smul]
    have hi : b i ∈ Set.range b := ⟨i, rfl⟩
    simpa [uniformizer_ne_zero K] using
      (Submodule.subset_span (R := IntegerRing K) hi)
  · rw [coordinateInverseScaleBasis_apply_of_ne _ hji]
    change uniformizer K • b j ∈
      Submodule.span (IntegerRing K) (Set.range b)
    have hmem := (Submodule.span (IntegerRing K) (Set.range b)).smul_mem
      (uniformizerInteger K) (Submodule.subset_span ⟨j, rfl⟩)
    change uniformizer K • b j ∈
      Submodule.span (IntegerRing K) (Set.range b) at hmem
    exact hmem

/-- The primitive vector in the smaller lattice attached to an
index-`\mathfrak p` inclusion. -/
structure Beli2019IndexPGeneratorData
    (q : QuadraticSpace K V) (M N : Lattice K V) : Type (max u v) where
  /-- A primitive vector of the smaller lattice. -/
  vector : V
  mem : vector ∈ N
  primitive : vector ∉ rescale (uniformizerUnit K) N
  /-- Dividing the vector by the uniformizer generates the larger lattice. -/
  enlarged_eq :
    adjoinVector N ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • vector) = M

private theorem coordinateScaleBasis_vector_primitive
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    coordinateScaleBasis b i i ∉
      rescale (uniformizerUnit K)
        (basisLattice (coordinateScaleBasis b i)) := by
  intro hscaled
  rw [mem_rescale_iff] at hscaled
  obtain ⟨y, hy, hyEq⟩ := hscaled
  have hyEqB : uniformizer K • y = uniformizer K • b i := by
    simpa only [coe_uniformizerUnit, coordinateScaleBasis_apply_same] using hyEq
  have hyB : y = b i := by
    exact smul_right_injective V (uniformizer_ne_zero K) hyEqB
  have hcoordinate :=
    (mem_basisLattice_iff_repr_mem_integerRing
      (coordinateScaleBasis b i) y).1 hy i
  rw [hyB, coordinateScaleBasis, Basis.repr_unitsSMul] at hcoordinate
  have hintegral : (((uniformizerUnit K)⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    simpa [coordinateScaleUnits, Function.update, Units.smul_def] using hcoordinate
  exact (uniformizer_inv_not_mem_integerRing (K := K)) (by
    simpa using hintegral)

private theorem adjoin_coordinateScaleBasis_head
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    adjoinVector (basisLattice (coordinateScaleBasis b i)) (b i) =
      basisLattice b := by
  classical
  apply Lattice.ext
  apply le_antisymm
  · apply adjoinVector_le
      (basisLattice_coordinateScaleBasis_le b i)
    exact Submodule.subset_span ⟨i, rfl⟩
  · change Submodule.span (IntegerRing K) (Set.range b) ≤
      (adjoinVector
        (basisLattice (coordinateScaleBasis b i)) (b i)).toSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      exact mem_adjoinVector _ _
    · apply le_adjoinVector _ _
      rw [← coordinateScaleBasis_apply_of_ne b hji]
      exact Submodule.subset_span ⟨j, rfl⟩

/-- Dividing one basis vector by the uniformizer gives exactly the lattice
obtained by adjoining that divided vector. -/
theorem adjoin_basisLattice_uniformizerInv_head
    (b : Basis (Fin (finrank K V)) K V) (i : Fin (finrank K V)) :
    adjoinVector (basisLattice b)
        ((((uniformizerUnit K)⁻¹ : Kˣ) : K) • b i) =
      basisLattice (coordinateInverseScaleBasis b i) := by
  let c := coordinateInverseScaleBasis b i
  have h := adjoin_coordinateScaleBasis_head c i
  rw [coordinateScaleBasis_inverse_eq] at h
  simpa [c] using h

/-- Every literal index-`\mathfrak p` inclusion admits the primitive generator
used in Beli (2019), Lemma 5.1. -/
noncomputable def beli2019IndexPGeneratorData
    (q : QuadraticSpace K V) (M N : Lattice K V)
    (inclusion : Beli2019IndexPInclusion q M N) :
    Beli2019IndexPGeneratorData q M N := by
  classical
  let hexists := indexPInclusion_exists_coordinateScaleBasis q M N inclusion
  let b := Classical.choose hexists
  let i := Classical.choose (Classical.choose_spec hexists)
  have hM : basisLattice b = M :=
    (Classical.choose_spec (Classical.choose_spec hexists)).1
  have hN : basisLattice (coordinateScaleBasis b i) = N :=
    (Classical.choose_spec (Classical.choose_spec hexists)).2
  let c := coordinateScaleBasis b i
  let x := c i
  have hxN : x ∈ N := by
    rw [← hN]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxPrimitive : x ∉ rescale (uniformizerUnit K) N := by
    rw [← hN]
    exact coordinateScaleBasis_vector_primitive b i
  have hinvX : (((uniformizerUnit K)⁻¹ : Kˣ) : K) • x = b i := by
    change (((uniformizerUnit K)⁻¹ : Kˣ) : K) •
      coordinateScaleBasis b i i = b i
    rw [coordinateScaleBasis_apply_same]
    rw [← mul_smul]
    have hmul : (((uniformizerUnit K)⁻¹ : Kˣ) : K) * uniformizer K = 1 := by
      simp [uniformizer_ne_zero K]
    rw [hmul, one_smul]
  refine ⟨x, hxN, hxPrimitive, ?_⟩
  rw [hinvX, ← hN, ← hM]
  exact adjoin_coordinateScaleBasis_head b i

end Lattice

end Bong
