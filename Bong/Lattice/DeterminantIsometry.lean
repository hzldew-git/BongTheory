/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.Isometry

/-!
# Refined determinant classes under integral isometry

The volume-order invariant forgets the unit square class of a Gram
determinant.  O'Meara's classification theorem needs the stronger statement:
an integral quadratic isometry preserves the determinant modulo squares of
valuation units.  We first express the determinant class using an arbitrary
finite integral basis and then apply this to a basis transported by an
isometry.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- The Gram determinant in an arbitrary finite basis is nonzero. -/
theorem det_toMatrix_ne_zero_of_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) :
    (LinearMap.BilinForm.toMatrix b q.bilin).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp q.nondegenerate

/-- The nonzero Gram determinant attached to an arbitrary finite basis. -/
noncomputable def gramUnitOfBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) : Kˣ :=
  Units.mk0 (LinearMap.BilinForm.toMatrix b q.bilin).det
    (det_toMatrix_ne_zero_of_basis q b)

@[simp]
theorem coe_gramUnitOfBasis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) :
    (gramUnitOfBasis q b : K) =
      (LinearMap.BilinForm.toMatrix b q.bilin).det :=
  rfl

/-- Reindexing a finite basis does not change its Gram determinant unit. -/
theorem gramUnitOfBasis_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (q : QuadraticSpace K V) (b : Basis ι K V) (e : ι ≃ κ) :
    gramUnitOfBasis q (b.reindex e) = gramUnitOfBasis q b := by
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix (b.reindex e) q.bilin).det =
    (LinearMap.BilinForm.toMatrix b q.bilin).det
  have hmatrix :
      LinearMap.BilinForm.toMatrix (b.reindex e) q.bilin =
        Matrix.reindex e e (LinearMap.BilinForm.toMatrix b q.bilin) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [hmatrix, Matrix.det_reindex_self]

/-- The refined class of the Gram determinant in any integral basis is the
chosen refined determinant class of its basis lattice. -/
theorem unitSquareClass_gramUnitOfBasis_eq_determinantClass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : QuadraticSpace K V) (b : Basis ι K V) :
    unitSquareClass K (gramUnitOfBasis q b) =
      determinantClass q (basisLattice b) := by
  let e : ι ≃ Fin (finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let bFin : Basis (Fin (finrank K V)) K V := b.reindex e
  have hunit : gramUnitOfBasis q bFin = gramUnitOfBasis q b :=
    gramUnitOfBasis_reindex q b e
  have hlattice : basisLattice bFin = basisLattice b :=
    basisLattice_reindex b e
  calc
    unitSquareClass K (gramUnitOfBasis q b) =
        unitSquareClass K (gramUnitOfBasis q bFin) :=
      congrArg (unitSquareClass K) hunit.symm
    _ = determinantClass q (basisLattice bFin) := by
      exact unitSquareClass_basisGramUnit_eq_determinantClass q bFin
    _ = determinantClass q (basisLattice b) := by rw [hlattice]

/-- Taking the lattice spanned by a mapped basis is the same as mapping its
basis lattice. -/
theorem map_basisLattice_eq_basisLattice_map
    {ι : Type*} [Finite ι]
    (b : Basis ι K V) (e : V ≃ₗ[K] W) :
    map e (basisLattice b) = basisLattice (b.map e) := by
  apply Lattice.ext
  ext y
  change y ∈ map e (basisLattice b) ↔ y ∈ basisLattice (b.map e)
  rw [mem_map_iff,
    mem_basisLattice_iff_repr_mem_integerRing,
    mem_basisLattice_iff_repr_mem_integerRing,
    Basis.map_repr]
  rfl

/-- Transporting a basis by a quadratic isometry preserves its Gram
determinant unit literally. -/
theorem gramUnitOfBasis_map_isometry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) (b : Basis ι K V) :
    gramUnitOfBasis r (b.map f.toLinearEquiv) =
      gramUnitOfBasis q b := by
  apply Units.ext
  change
    (LinearMap.BilinForm.toMatrix (b.map f.toLinearEquiv) r.bilin).det =
      (LinearMap.BilinForm.toMatrix b q.bilin).det
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, f.map_bilin]

/-- Integral quadratic isometries preserve Beli's refined determinant
class, not merely its valuation. -/
theorem determinantClass_eq_of_isometry
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) :
    determinantClass q L = determinantClass r M := by
  classical
  let b := L.standardAmbientBasis
  let c := b.map f.toLinearEquiv
  have hb : basisLattice b = L := basisLattice_standardAmbientBasis L
  have hc : basisLattice c = M := by
    calc
      basisLattice c = map f.toLinearEquiv (basisLattice b) :=
        (map_basisLattice_eq_basisLattice_map b f.toLinearEquiv).symm
      _ = map f.toLinearEquiv L := by rw [hb]
      _ = M := f.map_eq
  calc
    determinantClass q L =
        unitSquareClass K (gramUnitOfBasis q b) := by
      rw [← hb]
      exact (unitSquareClass_gramUnitOfBasis_eq_determinantClass q b).symm
    _ = unitSquareClass K (gramUnitOfBasis r c) := by
      rw [gramUnitOfBasis_map_isometry f b]
    _ = determinantClass r M := by
      rw [← hc]
      exact unitSquareClass_gramUnitOfBasis_eq_determinantClass r c

end Lattice

end Bong
