/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicSummandCancellation

/-!
# Universe-polymorphic displayed O'Meara towers

The original finite-tower implementation stores the complement as the base
of a recursively nested carrier.  That representation requires the field and
the complement to live in the same universe.  For classification theorems the
two vector-space carriers are genuinely universe-polymorphic.

This file keeps the finite O'Meara tower on its coordinate carrier and adjoins
an arbitrary complement only as one displayed orthogonal factor.  Repeated
associativity, Example 93:13, and Theorem 93:14 then give normalization and
cancellation without any universe restriction on the complement.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The unique integral isometry between two full lattices on the zero
carrier. -/
noncomputable def zeroCarrierLatticeIsometry
    (Z Z' : Lattice K (Fin 0 → K)) :
    Isometry (zeroCoordinateQuadraticSpace (K := K))
      (zeroCoordinateQuadraticSpace (K := K)) Z Z' where
  toLinearEquiv := LinearEquiv.refl K (Fin 0 → K)
  map_bilin _ _ := rfl
  map_mem := by
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact iff_of_true Z.zero_mem Z'.zero_mem

/-- Lift the zero-carrier isometry through a common finite tower of scaled
zero-coefficient O'Meara planes. -/
noncomputable def scaledZeroOmearaTowerLatticeIsometry (a : Kˣ)
    (Z Z' : Lattice K (Fin 0 → K)) :
    (n : Nat) →
      Isometry
        (omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0))
        (omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0))
        (hyperbolicExtensionLattice Z n)
        (hyperbolicExtensionLattice Z' n)
  | 0 => zeroCarrierLatticeIsometry Z Z'
  | n + 1 =>
      (Isometry.refl
        ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a)
        (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
          (scaledZeroOmearaTowerLatticeIsometry a Z Z' n)

/-- The norm group of the complement's scale truncation embeds into the
same truncation after adjoining a displayed finite O'Meara tower. -/
theorem normGroupSet_baseTruncation_subset_displayedOmearaTower
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (Z : Lattice K (Fin 0 → K)) (a s : Kˣ)
    (n : Nat) (alpha : Fin n → K) :
    normGroupSet q (omearaScaleTruncation q L s) ⊆
      normGroupSet
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n alpha).orthogonalSum q)
        (omearaScaleTruncation
          ((omearaPlaneExtensionForm
            (zeroCoordinateQuadraticSpace (K := K)) a n alpha).orthogonalSum q)
          (product (hyperbolicExtensionLattice Z n) L) s) :=
  normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
    (omearaPlaneExtensionForm
      (zeroCoordinateQuadraticSpace (K := K)) a n alpha)
    (hyperbolicExtensionLattice Z n) q L s

/-- Normalize a displayed finite tower `a A(alpha_i,0)` to the common tower
`a A(0,0)`, leaving an arbitrary-universe complement fixed. -/
noncomputable def normalizeDisplayedScaledOmearaTower
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (Z : Lattice K (Fin 0 → K)) (a : Kˣ) :
    (n : Nat) → (alpha : Fin n → K) →
      (∀ i, (a : K) * alpha i ∈
        normGroupSet q (omearaScaleTruncation q L a)) →
      Isometry
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n alpha).orthogonalSum q)
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0)).orthogonalSum q)
        (product (hyperbolicExtensionLattice Z n) L)
        (product (hyperbolicExtensionLattice Z n) L)
  | 0, _, _ =>
      Isometry.refl
        ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum q)
        (product Z L)
  | n + 1, alpha, hcoefficient => by
      let tailSource := omearaPlaneExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) a n (Fin.tail alpha)
      let tailTarget := omearaPlaneExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0)
      let tailLattice := hyperbolicExtensionLattice Z n
      let headSource :=
        (QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a
      let headTarget :=
        (QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a
      let sourceAssoc : Isometry
          ((headSource.orthogonalSum tailSource).orthogonalSum q)
          (headSource.orthogonalSum (tailSource.orthogonalSum q))
          (product (product (hyperbolicPlaneLattice (K := K)) tailLattice) L)
          (product (hyperbolicPlaneLattice (K := K))
            (product tailLattice L)) :=
        orthogonalProductAssoc
      let targetAssoc : Isometry
          ((headTarget.orthogonalSum tailTarget).orthogonalSum q)
          (headTarget.orthogonalSum (tailTarget.orthogonalSum q))
          (product (product (hyperbolicPlaneLattice (K := K)) tailLattice) L)
          (product (hyperbolicPlaneLattice (K := K))
            (product tailLattice L)) :=
        orthogonalProductAssoc
      let normalizeTail := normalizeDisplayedScaledOmearaTower
        q L Z a n (Fin.tail alpha) (fun i ↦ hcoefficient i.succ)
      let keepHead := Isometry.orthogonalProductBasic
        (Isometry.refl headSource (hyperbolicPlaneLattice (K := K)))
        normalizeTail
      have hheadComplement : (a : K) * alpha 0 ∈
          normGroupSet (tailTarget.orthogonalSum q)
            (omearaScaleTruncation (tailTarget.orthogonalSum q)
              (product tailLattice L) a) :=
        normGroupSet_baseTruncation_subset_displayedOmearaTower
          q L Z a a n (fun _ ↦ 0) (hcoefficient 0)
      let normalizeHead := omeara9313
        (tailTarget.orthogonalSum q) (product tailLattice L)
        a 0 ((a : K) * alpha 0) hheadComplement
      have hshift :
          0 + (a⁻¹ : Kˣ) * ((a : K) * alpha 0) = alpha 0 := by
        rw [zero_add, Units.val_inv_eq_inv_val]
        field_simp [Units.ne_zero a]
      let normalizeHead' : Isometry
          (headSource.orthogonalSum (tailTarget.orthogonalSum q))
          (headTarget.orthogonalSum (tailTarget.orthogonalSum q))
          (product (hyperbolicPlaneLattice (K := K))
            (product tailLattice L))
          (product (hyperbolicPlaneLattice (K := K))
            (product tailLattice L)) := by
        simpa only [headSource, headTarget, hshift] using normalizeHead
      let associated := sourceAssoc.trans
        (keepHead.trans (normalizeHead'.trans targetAssoc.symm))
      change Isometry
        ((((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
          tailSource).orthogonalSum q)
        ((((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a).orthogonalSum
          tailTarget).orthogonalSum q)
        (product (product (hyperbolicPlaneLattice (K := K)) tailLattice) L)
        (product (product (hyperbolicPlaneLattice (K := K)) tailLattice) L)
      exact associated

/-- Cancel a displayed common tower of scaled zero-coefficient O'Meara
planes.  The two complements and their carriers may live in unrelated
universes. -/
noncomputable def cancelDisplayedScaledZeroOmearaTower (a : Kˣ)
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    (Z Z' : Lattice K (Fin 0 → K)) :
    (n : Nat) →
      {q : QuadraticSpace K V} → {r : QuadraticSpace K W} →
      {L : Lattice K V} → {M : Lattice K W} →
      Isometry
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0)).orthogonalSum q)
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0)).orthogonalSum r)
        (product (hyperbolicExtensionLattice Z n) L)
        (product (hyperbolicExtensionLattice Z' n) M) →
      Isometry q r L M
  | 0, q, r, L, M, f => by
      change Isometry
        ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum q)
        ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum r)
        (product Z L) (product Z' M) at f
      let sourceZero : Isometry
          ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum q) q
          (product Z L) L :=
        zeroLeftOrthogonalProductIsometry (K := K) Z q L
      let targetZero : Isometry
          ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum r) r
          (product Z' M) M :=
        zeroLeftOrthogonalProductIsometry (K := K) Z' r M
      exact sourceZero.symm.trans (f.trans targetZero)
  | n + 1, q, r, L, M, f => by
      let head := (QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a
      let tail := omearaPlaneExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) a n (fun _ ↦ 0)
      let sourceAssoc : Isometry
          ((head.orthogonalSum tail).orthogonalSum q)
          (head.orthogonalSum (tail.orthogonalSum q))
          (product
            (product (hyperbolicPlaneLattice (K := K))
              (hyperbolicExtensionLattice Z n)) L)
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicExtensionLattice Z n) L)) :=
        orthogonalProductAssoc
      let targetAssoc : Isometry
          ((head.orthogonalSum tail).orthogonalSum r)
          (head.orthogonalSum (tail.orthogonalSum r))
          (product
            (product (hyperbolicPlaneLattice (K := K))
              (hyperbolicExtensionLattice Z' n)) M)
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicExtensionLattice Z' n) M)) :=
        orthogonalProductAssoc
      let nested := sourceAssoc.symm.trans (f.trans targetAssoc)
      let tailIsometry := omeara9314_scaled_of_isometric_summand
        a (scaledZeroOmearaPlaneLatticeIsometry a)
          (scaledZeroOmearaPlaneLatticeIsometry a) nested
      exact cancelDisplayedScaledZeroOmearaTower a Z Z' n tailIsometry

end Lattice

end Bong
