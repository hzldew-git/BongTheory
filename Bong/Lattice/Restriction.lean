/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Ideals

/-!
# Restricting full lattices to spanning subspaces

The inverse image of an integral lattice under a subspace inclusion is a full
lattice whenever that inverse image spans the subspace.  This small interface
is used to realize finite BONG prefixes inside their coordinate subspaces.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The pullback of a lattice to a subspace known to be integrally spanning. -/
noncomputable def comapSubtype (L : Lattice K V) (P : Submodule K V)
    (hspan : Submodule.span K
      ({x : P | (x : V) ∈ L} : Set P) = ⊤) : Lattice K P where
  toSubmodule := L.toSubmodule.comap
    (P.subtype.restrictScalars (IntegerRing K))
  fg := by
    let f := P.subtype.restrictScalars (IntegerRing K)
    apply Submodule.fg_of_fg_map_injective f Subtype.val_injective
    apply L.fg.of_le
    rintro y ⟨x, hx, rfl⟩
    exact hx
  span_eq_top := hspan

@[simp]
theorem mem_comapSubtype_iff (L : Lattice K V) (P : Submodule K V)
    (hspan : Submodule.span K
      ({x : P | (x : V) ∈ L} : Set P) = ⊤) (x : P) :
    x ∈ comapSubtype L P hspan ↔ (x : V) ∈ L :=
  Iff.rfl

/-- Restricting a lattice cannot enlarge its norm ideal. -/
theorem normIdeal_comapSubtype_le (q : QuadraticSpace K V)
    (L : Lattice K V) (P : Submodule K V)
    (nondegenerate : (q.bilin.restrict P).Nondegenerate)
    (hspan : Submodule.span K
      ({x : P | (x : V) ∈ L} : Set P) = ⊤) :
    normIdeal (q.restrict P nondegenerate) (comapSubtype L P hspan) ≤
      normIdeal q L := by
  rw [normIdeal, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact quadratic_mem_normIdeal_of_mem q L x.property

/-- A norm generator remains one after restricting to a spanning subspace. -/
theorem isNormGenerator_comapSubtype (q : QuadraticSpace K V)
    (L : Lattice K V) (P : Submodule K V)
    (nondegenerate : (q.bilin.restrict P).Nondegenerate)
    (hspan : Submodule.span K
      ({x : P | (x : V) ∈ L} : Set P) = ⊤)
    (x : P) (generator : IsNormGenerator q L (x : V)) :
    IsNormGenerator (q.restrict P nondegenerate)
      (comapSubtype L P hspan) x := by
  refine ⟨generator.mem, le_antisymm ?_ ?_⟩
  · exact (normIdeal_comapSubtype_le q L P nondegenerate hspan).trans_eq
      generator.normIdeal_eq
  · rw [principalIdeal, Submodule.span_le]
    rintro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact quadratic_mem_normIdeal_of_mem
      (q.restrict P nondegenerate) (comapSubtype L P hspan) generator.mem

end Lattice

end Bong
