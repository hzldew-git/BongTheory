/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41ProductModel

/-!
# Componentwise assembly for finite orthogonal decompositions

This file records the finite-product gluing step used repeatedly in the
Jordan-chain argument behind O'Meara 93:28.  A family of integral isometries
between corresponding orthogonal components first gives an isometry between
the coordinate products.  Conjugating by the product presentations of the
two decompositions then gives an isometry of the ambient lattices.
-/

namespace Bong

open Dyadic
open Module

namespace BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Coordinatewise product of a nonempty finite family of integral
isometries. -/
noncomputable def blockProductLatticeIsometry
    {n : Nat}
    {C : Fin (n + 1) → Type v} {D : Fin (n + 1) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (rs : ∀ i, QuadraticSpace K (D i))
    (Ls : ∀ i, Lattice K (C i))
    (Ms : ∀ i, Lattice K (D i))
    (f : ∀ i, Lattice.Isometry (qs i) (rs i) (Ls i) (Ms i)) :
    Lattice.Isometry
      (blockOrthogonalForm n C qs)
      (blockOrthogonalForm n D rs)
      (blockProductLattice n C Ls)
      (blockProductLattice n D Ms) where
  toLinearEquiv := LinearEquiv.piCongrRight (fun i ↦ (f i).toLinearEquiv)
  map_bilin x y := by
    rw [blockOrthogonalForm_bilin_apply,
      blockOrthogonalForm_bilin_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (f i).map_bilin (x i) (y i)
  map_mem x := by
    rw [mem_blockProductLattice_iff,
      mem_blockProductLattice_iff]
    simp only [LinearEquiv.piCongrRight_apply]
    exact forall_congr' (fun i ↦ (f i).map_mem (x i))

@[simp]
theorem blockProductLatticeIsometry_apply
    {n : Nat}
    {C : Fin (n + 1) → Type v} {D : Fin (n + 1) → Type w}
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (rs : ∀ i, QuadraticSpace K (D i))
    (Ls : ∀ i, Lattice K (C i))
    (Ms : ∀ i, Lattice K (D i))
    (f : ∀ i, Lattice.Isometry (qs i) (rs i) (Ls i) (Ms i))
    (x : BlockProductSpace n C) (i : Fin (n + 1)) :
    (blockProductLatticeIsometry qs rs Ls Ms f).toLinearEquiv x i =
      (f i).toLinearEquiv (x i) :=
  rfl

/-- Integral isometries between corresponding components of two finite
orthogonal decompositions assemble to an integral isometry of their ambient
lattices. -/
noncomputable def orthogonalDecompositionComponentwiseIsometry
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (P : Lattice.OrthogonalDecomposition q L (n + 1))
    (Q : Lattice.OrthogonalDecomposition r M (n + 1))
    (f : ∀ i, Lattice.Isometry
      (P.component i).space (Q.component i).space
      (P.component i).lattice (Q.component i).lattice) :
    Lattice.Isometry q r L M :=
  (orthogonalDecompositionProductIsometry P).symm |>.trans
    ((blockProductLatticeIsometry
      (fun i ↦ (P.component i).space)
      (fun i ↦ (Q.component i).space)
      (fun i ↦ (P.component i).lattice)
      (fun i ↦ (Q.component i).lattice) f).trans
        (orthogonalDecompositionProductIsometry Q))

end BONG

end Bong
