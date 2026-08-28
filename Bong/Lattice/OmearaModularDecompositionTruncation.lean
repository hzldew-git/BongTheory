/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaModularScaleTruncation
import Bong.Lattice.ModularParameter

/-!
# Scale truncation from an unordered modular decomposition

The calculation of `L^r` is componentwise and uses only modularity; the
strict ordering in a Jordan decomposition is irrelevant.  O'Meara 93:21
temporarily moves one component to the front, so this unordered form avoids
introducing artificial ordering hypotheses during that construction.
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

/-- O'Meara's unit-indexed notation for a scale truncation agrees with the
intrinsic order-indexed construction. -/
theorem omearaScaleTruncation_eq_scaleTruncation (s : Kˣ) :
    omearaScaleTruncation q L s = scaleTruncation q L (ordUnit K s) := by
  unfold omearaScaleTruncation scaleTruncation
  rw [dualLattice_rescaleQuadraticUnit, inv_inv]
  congr 1
  apply rescale_eq_of_principalIdeal_eq
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).2
  rw [scaleTruncationUnit, ordUnit_uniformizerPowerUnit]

/-- Scale truncation commutes with a concrete orthogonal product. -/
theorem scaleTruncation_orthogonalProduct (k : Int) :
    scaleTruncation (q.orthogonalSum r) (product L M) k =
      product (scaleTruncation q L k) (scaleTruncation r M k) := by
  unfold scaleTruncation
  rw [dualLattice_orthogonalProduct_basic, ← product_rescale]
  apply Lattice.ext
  ext z
  change
    (z ∈ product L M ∧
        z ∈ product
          (rescale (scaleTruncationUnit (K := K) k) (dualLattice q L))
          (rescale (scaleTruncationUnit (K := K) k) (dualLattice r M))) ↔
      z ∈ product
        (inf L (rescale (scaleTruncationUnit (K := K) k) (dualLattice q L)))
        (inf M (rescale (scaleTruncationUnit (K := K) k) (dualLattice r M)))
  rw [mem_product_iff, mem_product_iff, mem_product_iff]
  change ((z.1 ∈ L ∧ z.2 ∈ M) ∧
      (z.1 ∈ rescale (scaleTruncationUnit (K := K) k) (dualLattice q L) ∧
        z.2 ∈ rescale (scaleTruncationUnit (K := K) k) (dualLattice r M))) ↔
    ((z.1 ∈ L ∧ z.1 ∈ rescale
        (scaleTruncationUnit (K := K) k) (dualLattice q L)) ∧
      (z.2 ∈ M ∧ z.2 ∈ rescale
        (scaleTruncationUnit (K := K) k) (dualLattice r M)))
  tauto

/-- Unit-indexed scale truncation also commutes with orthogonal products. -/
theorem omearaScaleTruncation_orthogonalProduct (s : Kˣ) :
    omearaScaleTruncation (q.orthogonalSum r) (product L M) s =
      product (omearaScaleTruncation q L s)
        (omearaScaleTruncation r M s) := by
  rw [omearaScaleTruncation_eq_scaleTruncation,
    omearaScaleTruncation_eq_scaleTruncation,
    omearaScaleTruncation_eq_scaleTruncation,
    scaleTruncation_orthogonalProduct]

end Lattice

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- Component factor for scale truncation relative to an arbitrary family
of modular scale generators. -/
noncomputable def modularScaleTruncationFactor
    (s : Fin t → Kˣ) (r : Int) (i : Fin t) : Kˣ :=
  positivePartUnit
    (scaleTruncationUnit (K := K) r * (s i)⁻¹)

@[simp]
theorem ordUnit_modularScaleTruncationFactor
    (s : Fin t → Kˣ) (r : Int) (i : Fin t) :
    ordUnit K (modularScaleTruncationFactor s r i) =
      max 0 (r - ordUnit K (s i)) := by
  rw [modularScaleTruncationFactor, ordUnit_positivePartUnit,
    ordUnit_mul, ordUnit_inv]
  change max 0
      (ordUnit K (scaleTruncationUnit (K := K) r) - ordUnit K (s i)) = _
  rw [scaleTruncationUnit, ordUnit_uniformizerPowerUnit]

/-- Any finite orthogonal decomposition into modular components computes the
intrinsic scale truncation componentwise. -/
theorem scaleTruncation_eq_componentwiseRescaleLattice_of_modular
    (D : OrthogonalDecomposition q L t) (s : Fin t → Kˣ)
    (hmodular : ∀ i, IsModular (D.component i).space
      (D.component i).lattice (s i)) (r : Int) :
    scaleTruncation q L r =
      D.componentwiseRescaleLattice
        (modularScaleTruncationFactor s r) := by
  let f : Fin t → Kˣ := fun i ↦
    scaleTruncationUnit (K := K) r * (s i)⁻¹
  have hdual :
      rescale (scaleTruncationUnit (K := K) r) (dualLattice q L) =
        D.componentwiseRescaleLattice f := by
    exact D.rescale_dualLattice_eq_componentwiseRescaleLattice
      s hmodular (scaleTruncationUnit (K := K) r)
  rw [scaleTruncation, hdual]
  rw (occs := .pos [1]) [← D.basisLattice_componentAmbientBasis]
  change inf (basisLattice D.componentAmbientBasis)
      (basisLattice (D.componentAmbientBasis.unitsSMul
        (fun z ↦ f z.1))) =
    basisLattice (D.componentAmbientBasis.unitsSMul
      (fun z ↦ modularScaleTruncationFactor s r z.1))
  simpa only [modularScaleTruncationFactor, f] using
    inf_basisLattice_unitsSMul D.componentAmbientBasis (fun z ↦ f z.1)

/-- The componentwise calculation bundled as an exact orthogonal
decomposition of the scale truncation. -/
noncomputable def modularScaleTruncationDecomposition
    (D : OrthogonalDecomposition q L t) (s : Fin t → Kˣ)
    (hmodular : ∀ i, IsModular (D.component i).space
      (D.component i).lattice (s i)) (r : Int) :
    OrthogonalDecomposition q (scaleTruncation q L r) t where
  component := fun i ↦
    (D.component i).rescaleLattice
      (modularScaleTruncationFactor s r i)
  orthogonal := D.orthogonal
  sum_eq := by
    rw [D.scaleTruncation_eq_componentwiseRescaleLattice_of_modular
      s hmodular r]
    exact (D.componentwiseRescale
      (modularScaleTruncationFactor s r)).sum_eq

@[simp]
theorem modularScaleTruncationFactor_self
    (s : Fin t → Kˣ) (i : Fin t) :
    modularScaleTruncationFactor s (ordUnit K (s i)) i = 1 := by
  simp [modularScaleTruncationFactor, positivePartUnit,
    scaleTruncationUnit, ordUnit_mul, ordUnit_inv]

/-- At the scale of one chosen modular component, that component occurs
literally (with no lattice rescaling) in the unordered scale-truncation
decomposition. -/
@[simp]
theorem modularScaleTruncationDecomposition_component_self
    (D : OrthogonalDecomposition q L t) (s : Fin t → Kˣ)
    (hmodular : ∀ i, IsModular (D.component i).space
      (D.component i).lattice (s i)) (i : Fin t) :
    (D.modularScaleTruncationDecomposition s hmodular
        (ordUnit K (s i))).component i = D.component i := by
  change (D.component i).rescaleLattice
      (modularScaleTruncationFactor s (ordUnit K (s i)) i) =
    D.component i
  rw [modularScaleTruncationFactor_self]
  cases hC : D.component i with
  | mk carrier nondegenerate lattice =>
      simp [QuadraticSublattice.rescaleLattice, Lattice.rescale_one]

end Lattice.OrthogonalDecomposition

end Bong
