/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicTowerDecomposition
import Bong.Lattice.OmearaNormGroupShift

/-!
# Normalizing an O'Meara plane tower

This is the normalization step in O'Meara 93:14a.  If all displayed plane
coefficients lie in the norm group of the base scale truncation, successive
applications of 93:13 replace every `A(alpha_i,0)` by `A(0,0)`.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- Removing a common form scale by the unit `1` does not change a lattice
quadratic space. -/
noncomputable def rescaleUnitOneLatticeIsometry
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry (q.rescaleUnit (1 : Kˣ)) q L L where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro x y
    simp [QuadraticSpace.rescaleUnit_bilin_apply]
  map_mem _ := Iff.rfl

/-- The base truncation norm group embeds into every standard hyperbolic
extension of the tail. -/
theorem normGroupSet_baseTruncation_subset_hyperbolicExtension
    (r : QuadraticSpace K W) (M : Lattice K W) (s : Kˣ) :
    ∀ n : Nat,
      normGroupSet r (omearaScaleTruncation r M s) ⊆
        normGroupSet (hyperbolicExtensionForm r n)
          (omearaScaleTruncation (hyperbolicExtensionForm r n)
            (hyperbolicExtensionLattice M n) s)
  | 0 => by
      intro beta hbeta
      exact hbeta
  | n + 1 => by
      intro beta hbeta
      have htail :=
        normGroupSet_baseTruncation_subset_hyperbolicExtension r M s n hbeta
      have hstep :=
        normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
          (hyperbolicPlaneLattice (K := K))
          (hyperbolicExtensionForm r n)
          (hyperbolicExtensionLattice M n) s htail
      change beta ∈ normGroupSet
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
          (hyperbolicExtensionForm r n))
        (omearaScaleTruncation
          ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
            (hyperbolicExtensionForm r n))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)) s)
      exact hstep

/-- Normalize the head of an O'Meara plane tower after its tail has already
been normalized.  Keeping this step separate prevents the two module
instances on the definitionally equal successor carrier from being unfolded
through the whole recursion. -/
noncomputable def normalizeOmearaPlaneExtensionSucc
    (r : QuadraticSpace K W) (M : Lattice K W) (n : Nat)
    (alpha : Fin (n + 1) → K)
    (normalizeTail : Isometry
      (omearaPlaneExtensionForm r (1 : Kˣ) n (Fin.tail alpha))
      (hyperbolicExtensionForm r n)
      (hyperbolicExtensionLattice M n)
      (hyperbolicExtensionLattice M n))
    (hhead : alpha 0 ∈
      normGroupSet r (omearaScaleTruncation r M (1 : Kˣ))) :
    Isometry
      (omearaPlaneExtensionForm r (1 : Kˣ) (n + 1) alpha)
      (hyperbolicExtensionForm r (n + 1))
      (hyperbolicExtensionLattice M (n + 1))
      (hyperbolicExtensionLattice M (n + 1)) := by
      let headForm :=
        (QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit (1 : Kˣ)
      let headIdentity : Isometry headForm headForm
          (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)) :=
        Isometry.refl headForm (hyperbolicPlaneLattice (K := K))
      let normalizeAllTail :=
        headIdentity.orthogonalProductBasic normalizeTail
      have hheadComplement :=
        normGroupSet_baseTruncation_subset_hyperbolicExtension
          r M (1 : Kˣ) n hhead
      let normalizeHead := omeara9313
        (hyperbolicExtensionForm r n)
        (hyperbolicExtensionLattice M n) (1 : Kˣ) 0 (alpha 0)
        hheadComplement
      let normalizeHead' : Isometry
          (headForm.orthogonalSum (hyperbolicExtensionForm r n))
          (((QuadraticSpace.omearaPlane 0).rescaleUnit
              (1 : Kˣ)).orthogonalSum (hyperbolicExtensionForm r n))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)) := by
        simpa [headForm] using normalizeHead
      let zeroPlane := hyperbolicToOmearaPlaneLatticeIsometry
        (K := K) 0 0 (by ring) (by simp)
      let unscaleZero :=
        (rescaleUnitOneLatticeIsometry
          (QuadraticSpace.omearaPlane (K := K) 0)
          (hyperbolicPlaneLattice (K := K))).trans zeroPlane.symm
      let identifyZero := unscaleZero.orthogonalProductBasic
        (Isometry.refl (hyperbolicExtensionForm r n)
          (hyperbolicExtensionLattice M n))
      let combined :=
        normalizeAllTail.trans (normalizeHead'.trans identifyZero)
      change Isometry
        (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit
            (1 : Kˣ)).orthogonalSum
          (omearaPlaneExtensionForm r (1 : Kˣ) n (Fin.tail alpha)))
        ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
          (hyperbolicExtensionForm r n))
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicExtensionLattice M n))
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicExtensionLattice M n))
      exact combined

/-- Successive 93:13 transformations normalize a finite unimodular O'Meara
plane tower to the standard hyperbolic tower. -/
noncomputable def normalizeOmearaPlaneExtension
    (r : QuadraticSpace K W) (M : Lattice K W) :
    (n : Nat) → (alpha : Fin n → K) →
      (∀ i, alpha i ∈ normGroupSet r (omearaScaleTruncation r M (1 : Kˣ))) →
      Isometry
        (omearaPlaneExtensionForm r (1 : Kˣ) n alpha)
        (hyperbolicExtensionForm r n)
        (hyperbolicExtensionLattice M n)
        (hyperbolicExtensionLattice M n)
  | 0, _, _ => Isometry.refl r M
  | n + 1, alpha, halpha =>
      normalizeOmearaPlaneExtensionSucc r M n alpha
        (normalizeOmearaPlaneExtension r M n (Fin.tail alpha)
          (fun i => halpha i.succ))
        (halpha 0)

end Lattice

end Bong
