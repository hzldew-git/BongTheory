/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Basic

/-!
# Sums of full lattices

The sum of two full lattices is again a full lattice.  This file bundles the
submodule supremum and records its elementary order and membership API.
-/

namespace Bong

open Dyadic

namespace Lattice

variable {K : Type*} {V : Type*} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [AddCommGroup V] [Module K V]

/-- The sum `L + M` of two full lattices. -/
noncomputable def sup (L M : Lattice K V) : Lattice K V where
  toSubmodule := L.toSubmodule ⊔ M.toSubmodule
  fg := L.fg.sup M.fg
  span_eq_top := by
    apply top_unique
    intro x _
    have hx : x ∈ Submodule.span K (L.toSubmodule : Set V) := by
      rw [L.span_eq_top]
      exact Submodule.mem_top
    exact Submodule.span_mono (fun _ hy ↦ Submodule.mem_sup_left hy) hx

@[simp]
theorem sup_toSubmodule (L M : Lattice K V) :
    (sup L M).toSubmodule = L.toSubmodule ⊔ M.toSubmodule :=
  rfl

/-- Membership in a lattice sum is an additive decomposition. -/
theorem mem_sup_iff {L M : Lattice K V} {z : V} :
    z ∈ sup L M ↔ ∃ x ∈ L, ∃ y ∈ M, x + y = z :=
  Submodule.mem_sup

/-- The left summand embeds in the lattice sum. -/
theorem le_sup_left (L M : Lattice K V) : L ≤ sup L M :=
  show L.toSubmodule ≤ L.toSubmodule ⊔ M.toSubmodule from _root_.le_sup_left

/-- The right summand embeds in the lattice sum. -/
theorem le_sup_right (L M : Lattice K V) : M ≤ sup L M :=
  show M.toSubmodule ≤ L.toSubmodule ⊔ M.toSubmodule from _root_.le_sup_right

/-- A lattice sum lies in every common upper bound. -/
theorem sup_le {L M N : Lattice K V} (hL : L ≤ N) (hM : M ≤ N) : sup L M ≤ N :=
  show L.toSubmodule ⊔ M.toSubmodule ≤ N.toSubmodule from _root_.sup_le hL hM

/-- Adding a sublattice does not change a lattice. -/
theorem sup_eq_left_of_le {L M : Lattice K V} (h : M ≤ L) : sup L M = L := by
  apply ext
  exact sup_eq_left.mpr h

/-- Lattice sum is commutative. -/
theorem sup_comm (L M : Lattice K V) : sup L M = sup M L := by
  apply ext
  exact _root_.sup_comm _ _

end Lattice

end Bong
