/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Modular

/-!
# Jordan decompositions of quadratic lattices

Jordan components are generally proper subspaces of the ambient quadratic
space, so they cannot be represented by `Lattice K V`, whose definition is
full in `V`.  A `QuadraticSublattice` therefore stores its own nondegenerate
carrier subspace and a full lattice in that carrier.

This file gives basis-free structures for orthogonal and Jordan
decompositions, including chosen scale and norm generators.  It also states
Beli's property A in its original Jordan-coordinate form.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- A full lattice in a nondegenerate quadratic subspace of `V`. -/
structure QuadraticSublattice (q : QuadraticSpace K V) where
  /-- The carrier subspace in the ambient quadratic space. -/
  carrier : Submodule K V
  /-- The restricted form is nondegenerate. -/
  nondegenerate : (q.bilin.restrict carrier).Nondegenerate
  /-- The integral lattice, full in its own carrier. -/
  lattice : Lattice K carrier

namespace QuadraticSublattice

variable {q : QuadraticSpace K V}

/-- The quadratic space obtained by restricting to the carrier. -/
def space (C : QuadraticSublattice q) : QuadraticSpace K C.carrier :=
  q.restrict C.carrier C.nondegenerate

/-- The component lattice mapped into the ambient vector space. -/
noncomputable def ambientSubmodule (C : QuadraticSublattice q) :
    Submodule (IntegerRing K) V :=
  C.lattice.toSubmodule.map
    ((Submodule.subtype C.carrier).restrictScalars (IntegerRing K))

@[simp]
theorem mem_ambientSubmodule_iff (C : QuadraticSublattice q) (x : V) :
    x ∈ C.ambientSubmodule ↔
      ∃ y : C.carrier, y ∈ C.lattice ∧ (y : V) = x :=
  Iff.rfl

end QuadraticSublattice

/-- An integral orthogonal decomposition of a full lattice. -/
structure OrthogonalDecomposition (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat) where
  /-- The nondegenerate lattice components. -/
  component : Fin t → QuadraticSublattice q
  /-- Distinct carrier subspaces are orthogonal. -/
  orthogonal : ∀ (i j : Fin t), i ≠ j →
    ∀ (x : (component i).carrier) (y : (component j).carrier),
      q.bilin (x : V) (y : V) = 0
  /-- The integral sum of the components is the original lattice. -/
  sum_eq : (⨆ i, (component i).ambientSubmodule) = L.toSubmodule

namespace OrthogonalDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- Every component of an orthogonal decomposition is an integral sublattice
of the ambient lattice. -/
theorem component_ambientSubmodule_le
    (D : OrthogonalDecomposition q L t) (i : Fin t) :
    (D.component i).ambientSubmodule ≤ L.toSubmodule := by
  rw [← D.sum_eq]
  exact le_iSup (fun j ↦ (D.component j).ambientSubmodule) i

end OrthogonalDecomposition

/-- A Jordan decomposition with increasing modular scales. -/
structure JordanDecomposition (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat) extends OrthogonalDecomposition q L t where
  /-- A chosen generator of the scale of each component. -/
  scaleGenerator : Fin t → Kˣ
  /-- A chosen generator of the norm of each component. -/
  normGenerator : Fin t → Kˣ
  /-- Each component is modular at its chosen scale. -/
  modular : ∀ i, IsModular (component i).space (component i).lattice
    (scaleGenerator i)
  /-- The chosen scale element really generates the scale ideal. -/
  scaleIdeal_eq : ∀ i,
    scaleIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (scaleGenerator i : K)
  /-- The chosen norm element really generates the norm ideal. -/
  normIdeal_eq : ∀ i,
    normIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (normGenerator i : K)
  /-- Jordan scales strictly increase in valuation order. -/
  scaleOrder_strict : ∀ {i j : Fin t}, i < j →
    ordUnit K (scaleGenerator i) < ordUnit K (scaleGenerator j)

namespace JordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The rank of the `i`th Jordan component. -/
noncomputable def componentRank (J : JordanDecomposition q L t)
    (i : Fin t) : Nat :=
  finrank K (J.component i).carrier

/--
Property A for a Jordan decomposition: every component has rank at most two,
and the norm gaps lie strictly between zero and twice the scale gaps.
-/
noncomputable def HasPropertyA (J : JordanDecomposition q L t) : Prop :=
  (∀ i, J.componentRank i = 1 ∨ J.componentRank i = 2) ∧
    ∀ {i j : Fin t}, i < j →
      0 < ordUnit K (J.normGenerator j) - ordUnit K (J.normGenerator i) ∧
      ordUnit K (J.normGenerator j) - ordUnit K (J.normGenerator i) <
        2 * (ordUnit K (J.scaleGenerator j) -
          ordUnit K (J.scaleGenerator i))

end JordanDecomposition

/-- Beli's lattice property A, witnessed by a Jordan decomposition. -/
noncomputable def HasJordanPropertyA (q : QuadraticSpace K V)
    (L : Lattice K V) : Prop :=
  ∃ (t : Nat) (J : JordanDecomposition q L t), J.HasPropertyA

end Lattice

end Bong
