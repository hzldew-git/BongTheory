/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicModularStep

/-!
# Modular lattices on finite hyperbolic towers

This file iterates O'Meara 82:16 on an explicitly parenthesized hyperbolic
tower.  It is the decomposition part of Corollary 93:14a: after adjoining
`n` hyperbolic planes to an arbitrary tail space, every `a`-modular lattice
is integrally isometric to an orthogonal product of planes
`a A(alpha_i,0)` and an `a`-modular lattice on the original tail.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

/-- The carrier obtained by adjoining `n` outer hyperbolic planes to `W`. -/
def HyperbolicExtension (K : Type u) (W : Type u) : Nat → Type u
  | 0 => W
  | n + 1 => (Fin 2 → K) × HyperbolicExtension K W n

@[instance] abbrev hyperbolicExtensionAddCommGroup
    {K : Type u} [AddCommGroup K] {W : Type u} [AddCommGroup W]
    (n : Nat) : AddCommGroup (HyperbolicExtension K W n) :=
  Nat.rec (motive := fun m => AddCommGroup (HyperbolicExtension K W m))
    (show AddCommGroup W from inferInstance)
    (fun _ ih => @Prod.instAddCommGroup _ _ inferInstance ih) n

@[instance] abbrev hyperbolicExtensionModule
    {K : Type u} [Field K] {W : Type u} [AddCommGroup W] [Module K W]
    (n : Nat) : Module K (HyperbolicExtension K W n) :=
  Nat.rec
    (motive := fun m =>
      @Module K (HyperbolicExtension K W m) _
        (hyperbolicExtensionAddCommGroup m).toAddCommMonoid)
    (show Module K W from inferInstance)
    (fun _ ih => @Prod.instModule K _ _ _ _ _ inferInstance ih) n

/-- Repackage a linear equivalence on the unfolded successor product as a
linear equivalence on `HyperbolicExtension`.  The carrier operations are
definitionally the same; this small bridge prevents Lean from comparing the
native product instances with the recursive instances through large
quadratic-space expressions. -/
noncomputable def hyperbolicExtensionSuccLinearEquiv
    {K : Type u} [Field K] {W : Type u} [AddCommGroup W] [Module K W]
    (n : Nat)
    (e : ((Fin 2 → K) × HyperbolicExtension K W n) ≃ₗ[K]
      ((Fin 2 → K) × HyperbolicExtension K W n)) :
    HyperbolicExtension K W (n + 1) ≃ₗ[K]
      HyperbolicExtension K W (n + 1) where
  toFun := fun x => e x
  invFun := fun x => e.symm x
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := e.map_smul

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- The quadratic space obtained by adjoining `n` standard hyperbolic
planes to `r`. -/
noncomputable def hyperbolicExtensionForm (r : QuadraticSpace K W) :
    (n : Nat) → QuadraticSpace K (HyperbolicExtension K W n)
  | 0 => r
  | n + 1 =>
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (hyperbolicExtensionForm r n)

/-- The corresponding product lattice, ending in the chosen tail lattice. -/
noncomputable def hyperbolicExtensionLattice (M : Lattice K W) :
    (n : Nat) → Lattice K (HyperbolicExtension K W n)
  | 0 => M
  | n + 1 =>
      product (hyperbolicPlaneLattice (K := K))
        (hyperbolicExtensionLattice M n)

/-- Replace the standard hyperbolic planes by the scaled O'Meara planes
`a A(alpha_i,0)`. -/
noncomputable def omearaPlaneExtensionForm (r : QuadraticSpace K W) (a : Kˣ) :
    (n : Nat) → (Fin n → K) →
      QuadraticSpace K (HyperbolicExtension K W n)
  | 0, _ => r
  | n + 1, alpha =>
      ((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
        (omearaPlaneExtensionForm r a n (Fin.tail alpha))

/-- Data produced by iterating the primitive-isotropic splitting. -/
structure HyperbolicModularDecomposition
    (r : QuadraticSpace K W) (a : Kˣ) (n : Nat)
    (L : Lattice K (HyperbolicExtension K W n)) where
  coefficient : Fin n → K
  tailLattice : Lattice K W
  tailModular : IsModular r tailLattice a
  isometry : Isometry
    (omearaPlaneExtensionForm r a n coefficient)
    (hyperbolicExtensionForm r n)
    (hyperbolicExtensionLattice tailLattice n) L

/-- Iterated O'Meara 82:16: every modular lattice on a finite hyperbolic
extension has a complete `a A(alpha_i,0)` decomposition over a modular
tail. -/
noncomputable def hyperbolicModularDecomposition
    (r : QuadraticSpace K W) (a : Kˣ) :
    (n : Nat) → (L : Lattice K (HyperbolicExtension K W n)) →
      IsModular (hyperbolicExtensionForm r n) L a →
        HyperbolicModularDecomposition r a n L
  | 0, L, hmodular =>
      { coefficient := fun i => Fin.elim0 i
        tailLattice := L
        tailModular := hmodular
        isometry := Isometry.refl r L }
  | n + 1, L, hmodular => by
      let tailForm := hyperbolicExtensionForm r n
      let E := hyperbolicModularLineData tailForm L a hmodular
      let tailLattice := E.hyperbolicTailLattice hmodular
      let tailModular := E.hyperbolicTailLattice_modular hmodular
      let D := hyperbolicModularDecomposition r a n tailLattice tailModular
      let headForm :=
        (QuadraticSpace.omearaPlane
          E.pairingData.planeCoefficient).rescaleUnit a
      let headIdentity : Isometry headForm headForm
          (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)) :=
        Isometry.refl headForm (hyperbolicPlaneLattice (K := K))
      let recursiveIsometry :=
        headIdentity.orthogonalProductBasic D.isometry
      let stepIsometry := E.hyperbolicModularStepIsometry hmodular
      exact
        { coefficient := Fin.cons E.pairingData.planeCoefficient D.coefficient
          tailLattice := D.tailLattice
          tailModular := D.tailModular
          isometry := recursiveIsometry.trans stepIsometry }

end Lattice

end Bong
