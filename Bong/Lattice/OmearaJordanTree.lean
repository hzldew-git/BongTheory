/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.MinimalScaleComponent
import Bong.Lattice.NestedSublattice
import Bong.Lattice.NormGenerator

/-!
# O'Meara's recursive Jordan extraction

This file formalizes the recursive part of O'Meara, Section 91C, used in
Beli's Jordan calculations.  At every positive-dimensional stage, a unary or
binary modular lattice at the ambient scale is split off by O'Meara 82:15a.
The construction then recurses on the integral orthogonal complement, whose
dimension is strictly smaller.

Equal-scale consecutive nodes have not yet been amalgamated here.  The tree
records the exact successive splittings from which the usual strictly scaled
Jordan components are obtained.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace MinimalScaleComponentData

/-- A minimal-scale component has positive rank. -/
theorem component_finrank_pos (D : MinimalScaleComponentData q L) :
    0 < finrank K D.component.carrier := by
  rcases D.rank_one_or_two with h | h
  · omega
  · omega

/-- The chosen modular parameter generates the scale of the component. -/
theorem component_scaleIdeal_eq (D : MinimalScaleComponentData q L) :
    scaleIdeal D.component.space D.component.lattice =
      principalIdeal (K := K) (D.scaleGenerator : K) :=
  D.modular.scaleIdeal_eq_principal D.component_finrank_pos

/-- The two containments in the extraction show that the chosen parameter
generates the scale ideal of the whole lattice, not just of the component. -/
theorem ambientScaleIdeal_eq (D : MinimalScaleComponentData q L) :
    scaleIdeal q L = principalIdeal (K := K) (D.scaleGenerator : K) := by
  apply le_antisymm D.ambientScale_le
  rw [← D.component_scaleIdeal_eq]
  exact D.component.scaleIdeal_le_of_ambientSubmodule_le D.contained

/-- Mixed pairings with a minimal-scale component lie in its modular scale. -/
theorem mixedPairing (D : MinimalScaleComponentData q L) :
    ∀ (y : D.component.carrier), y ∈ D.component.lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈
          principalIdeal (K := K) (D.scaleGenerator : K) := by
  intro y hy x hx
  exact D.ambientScale_le (bilin_mem_scaleIdeal_of_mem q L
    (D.contained ⟨y, hy, rfl⟩) hx)

/-- The canonical integral orthogonal complement supplied by O'Meara 82:15a. -/
noncomputable def orthogonalComponent
    (D : MinimalScaleComponentData q L) : QuadraticSublattice q := by
  letI : Module.Finite K V := L.moduleFinite
  exact D.component.orthogonalSublattice D.contained D.modular D.mixedPairing

/-- The canonical two-block splitting attached to a minimal-scale component. -/
noncomputable def canonicalSplitting
    (D : MinimalScaleComponentData q L) :
    OrthogonalDecomposition q L 2 := by
  letI : Module.Finite K V := L.moduleFinite
  exact omearaModularSplitting D.component D.contained D.modular D.mixedPairing

@[simp]
theorem canonicalSplitting_zero (D : MinimalScaleComponentData q L) :
    D.canonicalSplitting.component 0 = D.component :=
  rfl

@[simp]
theorem canonicalSplitting_one (D : MinimalScaleComponentData q L) :
    D.canonicalSplitting.component 1 = D.orthogonalComponent :=
  rfl

/-- Removing the nonzero unary or binary component strictly lowers rank. -/
theorem orthogonalComponent_finrank_lt [FiniteDimensional K V]
    (D : MinimalScaleComponentData q L) :
    finrank K D.orthogonalComponent.carrier < finrank K V := by
  change finrank K (q.bilin.orthogonal D.component.carrier) < finrank K V
  rw [q.bilin.finrank_orthogonal q.nondegenerate]
  have hambient : 0 < finrank K V :=
    lt_of_lt_of_le D.component_finrank_pos (Submodule.finrank_le _)
  exact Nat.sub_lt hambient D.component_finrank_pos

end MinimalScaleComponentData

/-- The successive unary/binary modular splittings in O'Meara 91C.

The family is dependent because every tail lives in the preceding
component's orthogonal complement.  Each node also records a norm generator
of its positive-rank modular component, as required by Jordan-coordinate
calculations. -/
inductive OmearaJordanTree :
    (V : Type v) → [AddCommGroup V] → [Module K V] →
      QuadraticSpace K V → Lattice K V → Type (max (u + 1) (v + 1))
  | nil {V : Type v} [AddCommGroup V] [Module K V]
      (q : QuadraticSpace K V) (L : Lattice K V)
      (exhausted : Subsingleton V) :
      OmearaJordanTree V q L
  | node {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V}
      (head : MinimalScaleComponentData q L)
      (normVector : head.component.carrier)
      (normGenerator : IsNormGenerator head.component.space
        head.component.lattice normVector)
      (anisotropic : head.component.space.IsAnisotropic normVector)
      (tail : OmearaJordanTree head.orthogonalComponent.carrier
        head.orthogonalComponent.space head.orthogonalComponent.lattice) :
      OmearaJordanTree V q L

/-- O'Meara 91C, recursive form: every regular lattice admits successive
unary/binary modular splittings, terminating at the zero space. -/
noncomputable def omearaJordanTree
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) :
    OmearaJordanTree W q L := by
  letI : Module.Finite K W := L.moduleFinite
  by_cases hzero : finrank K W = 0
  · exact .nil q L (Module.finrank_zero_iff.mp hzero)
  · have hpos : 0 < finrank K W := Nat.pos_of_ne_zero hzero
    let hexists := exists_isScaleGenerator_of_finrank_pos q L hpos
    let x := Classical.choose hexists
    let y := Classical.choose (Classical.choose_spec hexists)
    have hgenerator : IsScaleGenerator q L x y :=
      (Classical.choose_spec (Classical.choose_spec hexists)).1
    have hxy : q.bilin x y ≠ 0 :=
      (Classical.choose_spec (Classical.choose_spec hexists)).2
    let D := minimalScaleComponentDataOfScaleGenerator hgenerator hxy
    let hnormExists := exists_isNormGenerator_of_finrank_pos
      D.component.space D.component.lattice D.component_finrank_pos
    let z := Classical.choose hnormExists
    have hnorm : IsNormGenerator D.component.space D.component.lattice z :=
      (Classical.choose_spec hnormExists).1
    have hz : D.component.space.IsAnisotropic z :=
      (Classical.choose_spec hnormExists).2
    let tail := omearaJordanTree D.orthogonalComponent.space
      D.orthogonalComponent.lattice
    exact .node D z hnorm hz tail
termination_by finrank K W
decreasing_by
  letI : Module.Finite K W := L.moduleFinite
  exact D.orthogonalComponent_finrank_lt

end Lattice

end Bong
