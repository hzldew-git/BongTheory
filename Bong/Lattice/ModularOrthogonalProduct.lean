/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009QuadraticRepresentation
import Bong.Lattice.ModularIsometry
import Bong.Lattice.Product

/-!
# Orthogonal products of modular lattices

The orthogonal product of two lattices modular at the same parameter is
modular at that parameter.  This is the local algebra used to amalgamate
successive equal-scale terms in O'Meara's Jordan-splitting construction.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Integral duality commutes with the concrete orthogonal product. -/
theorem dualLattice_orthogonalProduct_basic :
    dualLattice (q.orthogonalSum r) (product L M) =
      product (dualLattice q L) (dualLattice r M) := by
  apply Lattice.ext
  apply Submodule.ext
  intro z
  change z ∈ dualLattice (q.orthogonalSum r) (product L M) ↔
    z ∈ product (dualLattice q L) (dualLattice r M)
  rw [mem_dualLattice_iff, mem_product_iff]
  constructor
  · intro hz
    constructor
    · rw [mem_dualLattice_iff]
      intro x hx
      have h := hz (x, 0) (inl_mem_product_iff.mpr hx)
      simpa [QuadraticSpace.orthogonalSum_bilin_apply] using h
    · rw [mem_dualLattice_iff]
      intro y hy
      have h := hz (0, y) (inr_mem_product_iff.mpr hy)
      simpa [QuadraticSpace.orthogonalSum_bilin_apply] using h
  · rintro ⟨hzLeft, hzRight⟩ y hy
    rw [mem_dualLattice_iff] at hzLeft hzRight
    have hleft := hzLeft y.1 (fst_mem_of_mem_product hy)
    have hright := hzRight y.2 (snd_mem_of_mem_product hy)
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    exact (IntegerRing K).add_mem _ _ hleft hright

/-- Lattice products commute with a common scalar rescaling. -/
theorem product_rescale (a : Kˣ) :
    product (rescale a L) (rescale a M) = rescale a (product L M) := by
  apply Lattice.ext
  apply Submodule.ext
  intro z
  change z ∈ product (rescale a L) (rescale a M) ↔
    z ∈ rescale a (product L M)
  rw [mem_product_iff, mem_rescale_iff, mem_rescale_iff, mem_rescale_iff]
  constructor
  · rintro ⟨⟨x, hx, hzx⟩, ⟨y, hy, hzy⟩⟩
    refine ⟨(x, y), mem_product_iff.mpr ⟨hx, hy⟩, ?_⟩
    apply Prod.ext
    · exact hzx
    · exact hzy
  · rintro ⟨z, hz, hscaled⟩
    have hz' := mem_product_iff.mp hz
    constructor
    · refine ⟨z.1, hz'.1, ?_⟩
      exact congrArg Prod.fst hscaled
    · refine ⟨z.2, hz'.2, ?_⟩
      exact congrArg Prod.snd hscaled

/-- The orthogonal product of two `a`-modular lattices is `a`-modular. -/
theorem IsModular.orthogonalProduct {a : Kˣ}
    (hL : IsModular q L a) (hM : IsModular r M a) :
    IsModular (q.orthogonalSum r) (product L M) a := by
  rw [IsModular, dualLattice_orthogonalProduct_basic, hL, hM,
    product_rescale]

/-- The left factor of a modular orthogonal product is modular at the same
parameter. -/
theorem IsModular.left_of_orthogonalProduct {a : Kˣ}
    (h : IsModular (q.orthogonalSum r) (product L M) a) :
    IsModular q L a := by
  rw [IsModular, dualLattice_orthogonalProduct_basic,
    ← product_rescale] at h
  rw [IsModular]
  apply Lattice.ext
  apply Submodule.ext
  intro x
  calc
    x ∈ dualLattice q L ↔
        (x, 0) ∈ product (dualLattice q L) (dualLattice r M) :=
      inl_mem_product_iff.symm
    _ ↔ (x, 0) ∈ product (Lattice.rescale a⁻¹ L)
        (Lattice.rescale a⁻¹ M) := by
      rw [h]
    _ ↔ x ∈ Lattice.rescale a⁻¹ L := inl_mem_product_iff

/-- The right factor of a modular orthogonal product is modular at the same
parameter. -/
theorem IsModular.right_of_orthogonalProduct {a : Kˣ}
    (h : IsModular (q.orthogonalSum r) (product L M) a) :
    IsModular r M a := by
  rw [IsModular, dualLattice_orthogonalProduct_basic,
    ← product_rescale] at h
  rw [IsModular]
  apply Lattice.ext
  apply Submodule.ext
  intro y
  calc
    y ∈ dualLattice r M ↔
        (0, y) ∈ product (dualLattice q L) (dualLattice r M) :=
      inr_mem_product_iff.symm
    _ ↔ (0, y) ∈ product (Lattice.rescale a⁻¹ L)
        (Lattice.rescale a⁻¹ M) := by
      rw [h]
    _ ↔ y ∈ Lattice.rescale a⁻¹ M := inr_mem_product_iff

end Lattice

end Bong
