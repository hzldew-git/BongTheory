/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Products of full lattices

The product of two full lattices is the full lattice whose integral module is
the product of the two integral modules.  This is the underlying lattice used
for coordinate models of orthogonal sums.
-/

namespace Bong

open Dyadic

namespace Lattice

variable {K : Type*} {V : Type*} {W : Type*}
  [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The product of two full lattices. -/
noncomputable def product (L : Lattice K V) (M : Lattice K W) :
    Lattice K (V × W) where
  toSubmodule := L.toSubmodule.prod M.toSubmodule
  fg := L.fg.prod M.fg
  span_eq_top := by
    have hset :
        ((L.toSubmodule.prod M.toSubmodule :
            Submodule (IntegerRing K) (V × W)) : Set (V × W)) =
          (L.toSubmodule : Set V) ×ˢ (M.toSubmodule : Set W) := by
      ext z
      simp
    rw [hset, Submodule.span_prod_eq (R := K)
        (s := (L.toSubmodule : Set V))
        (t := (M.toSubmodule : Set W)) L.zero_mem M.zero_mem,
      L.span_eq_top, M.span_eq_top, Submodule.prod_top]

@[simp]
theorem product_toSubmodule (L : Lattice K V) (M : Lattice K W) :
    (product L M).toSubmodule = L.toSubmodule.prod M.toSubmodule :=
  rfl

@[simp]
theorem mem_product_iff {L : Lattice K V} {M : Lattice K W}
    {z : V × W} :
    z ∈ product L M ↔ z.1 ∈ L ∧ z.2 ∈ M := by
  rfl

@[simp]
theorem fst_mem_of_mem_product {L : Lattice K V} {M : Lattice K W}
    {z : V × W} (hz : z ∈ product L M) : z.1 ∈ L :=
  (mem_product_iff.mp hz).1

@[simp]
theorem snd_mem_of_mem_product {L : Lattice K V} {M : Lattice K W}
    {z : V × W} (hz : z ∈ product L M) : z.2 ∈ M :=
  (mem_product_iff.mp hz).2

@[simp]
theorem inl_mem_product_iff {L : Lattice K V} {M : Lattice K W}
    {x : V} :
    (x, 0) ∈ product L M ↔ x ∈ L := by
  simp [mem_product_iff]

@[simp]
theorem inr_mem_product_iff {L : Lattice K V} {M : Lattice K W}
    {y : W} :
    (0, y) ∈ product L M ↔ y ∈ M := by
  simp [mem_product_iff]

end Lattice

end Bong
