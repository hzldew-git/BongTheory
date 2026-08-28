/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisUnits
import Bong.Lattice.Isometry

/-!
# Lattice isometries from Gram matrices

Two field bases with the same Gram entries determine an isometry of their
integral basis lattices.  We also record that extending any integral lattice
basis to the fraction field recovers the original lattice.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- Extending an arbitrary finite integral basis gives an ambient basis whose
integral span is the original lattice. -/
theorem basisLattice_extendOfIsLattice {i : Type z} [Finite i]
    (L : Lattice K V) (b : Basis i (IntegerRing K) L.toSubmodule) :
    basisLattice (b.extendOfIsLattice K) = L := by
  letI := Fintype.ofFinite i
  apply Lattice.ext
  change Submodule.span (IntegerRing K)
      (Set.range (b.extendOfIsLattice K)) = L.toSubmodule
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [Basis.extendOfIsLattice_apply] using (b i).property
  · intro x hx
    have hx' : (⟨x, hx⟩ : L.toSubmodule) ∈
        Submodule.span (IntegerRing K) (Set.range b) := by
      rw [b.span_eq]
      trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hx' ⊢
    rcases hx' with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [Basis.extendOfIsLattice_apply] using congrArg Subtype.val hf

/-- Equal Gram matrices in two bases induce an isometry of the corresponding
integral basis lattices. -/
theorem basisLattice_isIsometric_of_gram_eq {i : Type z} [Finite i]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (b : Basis i K V) (c : Basis i K W)
    (hgram : ∀ m n, r.bilin (c m) (c n) = q.bilin (b m) (b n)) :
    IsIsometric q r (basisLattice b) (basisLattice c) := by
  let f : V ≃ₗ[K] W := b.equiv c (Equiv.refl i)
  refine ⟨{
    toLinearEquiv := f
    map_bilin := ?_
    map_mem := ?_
  }⟩
  · intro x y
    have hforms : r.bilin.comp f.toLinearMap f.toLinearMap = q.bilin := by
      apply LinearMap.BilinForm.ext_basis b
      intro m n
      rw [LinearMap.BilinForm.comp_apply]
      simpa [f] using hgram m n
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  · intro x
    rw [mem_basisLattice_iff_repr_mem_integerRing,
      mem_basisLattice_iff_repr_mem_integerRing]
    have hrepr : c.repr (f x) = b.repr x := by
      simp [f, Basis.equiv]
    rw [hrepr]

end Lattice

end Bong
