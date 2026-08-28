/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicTowerNormalization
import Bong.Bong.Beli2009WeightIdealIsometry

/-!
# Normalizing scaled O'Meara plane towers

This is the scale-sensitive normalization used in O'Meara 93:14a.  A
coefficient `alpha_i` in `a A(alpha_i,0)` contributes the quadratic value
`a * alpha_i`; if that value belongs to the norm group of the complement's
`a O`-scale truncation, Example 93:13 replaces the plane by `a A(0,0)`.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {W : Type u} [AddCommGroup W] [Module K W]

/-- The first standard vector in an O'Meara plane. -/
def omearaPlaneFirstVector : Fin 2 → K := ![1, 0]

/-- The first standard vector in the `i`-th plane of a nested tower. -/
def omearaPlaneExtensionFirstVector :
    (n : Nat) → Fin n → HyperbolicExtension K W n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      Fin.cases
        (omearaPlaneFirstVector, 0)
        (fun j => (0, omearaPlaneExtensionFirstVector n j)) i

/-- Every selected first plane vector belongs to the standard tower
lattice, independently of the tail lattice. -/
theorem omearaPlaneExtensionFirstVector_mem
    (M : Lattice K W) :
    ∀ (n : Nat) (i : Fin n),
      omearaPlaneExtensionFirstVector (K := K) (W := W) n i ∈
        hyperbolicExtensionLattice M n
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change (omearaPlaneFirstVector, (0 : HyperbolicExtension K W n)) ∈
          product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)
        rw [mem_product_iff]
        constructor
        · rw [mem_omearaPlaneLattice_iff]
          simp [omearaPlaneFirstVector]
        · exact (hyperbolicExtensionLattice M n).zero_mem
      · change ((0 : Fin 2 → K),
            omearaPlaneExtensionFirstVector (K := K) (W := W) n j) ∈
          product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)
        rw [mem_product_iff]
        exact ⟨(hyperbolicPlaneLattice (K := K)).zero_mem,
          omearaPlaneExtensionFirstVector_mem M n j⟩

/-- The selected first vector has the displayed scaled coefficient as its
quadratic value. -/
theorem omearaPlaneExtensionFirstVector_quadratic
    (r : QuadraticSpace K W) (a : Kˣ) :
    ∀ (n : Nat) (alpha : Fin n → K) (i : Fin n),
      (omearaPlaneExtensionForm r a n alpha).quadratic
          (omearaPlaneExtensionFirstVector (K := K) (W := W) n i) =
        (a : K) * alpha i
  | 0, _, i => Fin.elim0 i
  | n + 1, alpha, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change
          (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm r a n (Fin.tail alpha))).quadratic
              (omearaPlaneFirstVector,
                (0 : HyperbolicExtension K W n)) =
            (a : K) * alpha 0
        rw [QuadraticSpace.orthogonalSum_quadratic_apply,
          QuadraticSpace.rescaleUnit_quadratic,
          QuadraticSpace.quadratic_zero, add_zero]
        simp [omearaPlaneFirstVector, QuadraticSpace.quadratic,
          QuadraticSpace.omearaPlane_bilin_apply]
      · change
          (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm r a n (Fin.tail alpha))).quadratic
              ((0 : Fin 2 → K),
                omearaPlaneExtensionFirstVector (K := K) (W := W) n j) =
            (a : K) * alpha j.succ
        rw [QuadraticSpace.orthogonalSum_quadratic_apply,
          QuadraticSpace.quadratic_zero, zero_add]
        exact omearaPlaneExtensionFirstVector_quadratic
          r a n (Fin.tail alpha) j

/-- The base truncation norm group embeds into an arbitrary finite tower of
scaled O'Meara planes. -/
theorem normGroupSet_baseTruncation_subset_omearaPlaneExtension
    (r : QuadraticSpace K W) (M : Lattice K W) (a s : Kˣ) :
    ∀ (n : Nat) (alpha : Fin n → K),
      normGroupSet r (omearaScaleTruncation r M s) ⊆
        normGroupSet (omearaPlaneExtensionForm r a n alpha)
          (omearaScaleTruncation (omearaPlaneExtensionForm r a n alpha)
            (hyperbolicExtensionLattice M n) s)
  | 0, _ => by
      intro beta hbeta
      exact hbeta
  | n + 1, alpha => by
      intro beta hbeta
      have htail :=
        normGroupSet_baseTruncation_subset_omearaPlaneExtension
          r M a s n (Fin.tail alpha) hbeta
      have hstep :=
        normGroupSet_omearaScaleTruncation_subset_orthogonalProduct_right
          ((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a)
          (hyperbolicPlaneLattice (K := K))
          (omearaPlaneExtensionForm r a n (Fin.tail alpha))
          (hyperbolicExtensionLattice M n) s htail
      change beta ∈ normGroupSet
        (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
          (omearaPlaneExtensionForm r a n (Fin.tail alpha)))
        (omearaScaleTruncation
          (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm r a n (Fin.tail alpha)))
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice M n)) s)
      exact hstep

/-- Normalize one head plane after the remaining scaled tower has already
been normalized. -/
noncomputable def normalizeScaledOmearaPlaneExtensionSucc
    (r : QuadraticSpace K W) (M : Lattice K W) (a : Kˣ) (n : Nat)
    (alpha : Fin (n + 1) → K)
    (normalizeTail : Isometry
      (omearaPlaneExtensionForm r a n (Fin.tail alpha))
      (omearaPlaneExtensionForm r a n (fun _ => 0))
      (hyperbolicExtensionLattice M n)
      (hyperbolicExtensionLattice M n))
    (hhead : (a : K) * alpha 0 ∈
      normGroupSet r (omearaScaleTruncation r M a)) :
    Isometry
      (omearaPlaneExtensionForm r a (n + 1) alpha)
      (omearaPlaneExtensionForm r a (n + 1) (fun _ => 0))
      (hyperbolicExtensionLattice M (n + 1))
      (hyperbolicExtensionLattice M (n + 1)) := by
  let headForm :=
    (QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a
  let headIdentity : Isometry headForm headForm
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    Isometry.refl headForm (hyperbolicPlaneLattice (K := K))
  let normalizeAllTail :=
    headIdentity.orthogonalProductBasic normalizeTail
  have hheadComplement :=
    normGroupSet_baseTruncation_subset_omearaPlaneExtension
      r M a a n (fun _ => 0) hhead
  let normalizeHead := omeara9313
    (omearaPlaneExtensionForm r a n (fun _ => 0))
    (hyperbolicExtensionLattice M n) a 0 ((a : K) * alpha 0)
    hheadComplement
  have hcoefficient :
      0 + (a⁻¹ : Kˣ) * ((a : K) * alpha 0) = alpha 0 := by
    rw [zero_add, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero a]
  let normalizeHead' : Isometry
      (headForm.orthogonalSum
        (omearaPlaneExtensionForm r a n (fun _ => 0)))
      (((QuadraticSpace.omearaPlane 0).rescaleUnit a).orthogonalSum
        (omearaPlaneExtensionForm r a n (fun _ => 0)))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicExtensionLattice M n))
      (product (hyperbolicPlaneLattice (K := K))
        (hyperbolicExtensionLattice M n)) := by
    simpa only [headForm, hcoefficient] using normalizeHead
  let combined := normalizeAllTail.trans normalizeHead'
  change Isometry
    (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
      (omearaPlaneExtensionForm r a n (Fin.tail alpha)))
    (((QuadraticSpace.omearaPlane 0).rescaleUnit a).orthogonalSum
      (omearaPlaneExtensionForm r a n (fun _ => 0)))
    (product (hyperbolicPlaneLattice (K := K))
      (hyperbolicExtensionLattice M n))
    (product (hyperbolicPlaneLattice (K := K))
      (hyperbolicExtensionLattice M n))
  exact combined

/-- Successive applications of O'Meara 93:13 replace a finite tower
`a A(alpha_i,0)` by the common tower `a A(0,0)`. -/
noncomputable def normalizeScaledOmearaPlaneExtension
    (r : QuadraticSpace K W) (M : Lattice K W) (a : Kˣ) :
    (n : Nat) → (alpha : Fin n → K) →
      (∀ i, (a : K) * alpha i ∈
        normGroupSet r (omearaScaleTruncation r M a)) →
      Isometry
        (omearaPlaneExtensionForm r a n alpha)
        (omearaPlaneExtensionForm r a n (fun _ => 0))
        (hyperbolicExtensionLattice M n)
        (hyperbolicExtensionLattice M n)
  | 0, _, _ => Isometry.refl r M
  | n + 1, alpha, halpha =>
      normalizeScaledOmearaPlaneExtensionSucc r M a n alpha
        (normalizeScaledOmearaPlaneExtension r M a n (Fin.tail alpha)
          (fun i => halpha i.succ))
        (halpha 0)

/-- Every coefficient displayed by the modular decomposition contributes
its scaled first-vector value to the norm group of the decomposed lattice. -/
theorem HyperbolicModularDecomposition.coefficient_mem_sourceNormGroup
    {r : QuadraticSpace K W} {a : Kˣ} {n : Nat}
    {L : Lattice K (HyperbolicExtension K W n)}
    (D : HyperbolicModularDecomposition r a n L) (i : Fin n) :
    (a : K) * D.coefficient i ∈
      normGroupSet (omearaPlaneExtensionForm r a n D.coefficient)
        (hyperbolicExtensionLattice D.tailLattice n) := by
  let x := omearaPlaneExtensionFirstVector (K := K) (W := W) n i
  refine ⟨x, omearaPlaneExtensionFirstVector_mem D.tailLattice n i,
    0, (twoScaleIdeal _ _).zero_mem, ?_⟩
  rw [add_zero]
  exact (omearaPlaneExtensionFirstVector_quadratic
    r a n D.coefficient i).symm

/-- The displayed coefficients also belong to the norm group of the
original modular lattice, by transport through the decomposition isometry. -/
theorem HyperbolicModularDecomposition.coefficient_mem_targetNormGroup
    {r : QuadraticSpace K W} {a : Kˣ} {n : Nat}
    {L : Lattice K (HyperbolicExtension K W n)}
    (D : HyperbolicModularDecomposition r a n L) (i : Fin n) :
    (a : K) * D.coefficient i ∈
      normGroupSet (hyperbolicExtensionForm r n) L := by
  have hnorm :
      normGroupSet (hyperbolicExtensionForm r n) L =
        normGroupSet (omearaPlaneExtensionForm r a n D.coefficient)
          (hyperbolicExtensionLattice D.tailLattice n) := by
    calc
      normGroupSet (hyperbolicExtensionForm r n) L =
          normGroupSet (hyperbolicExtensionForm r n)
            (map D.isometry.toLinearEquiv
              (hyperbolicExtensionLattice D.tailLattice n)) := by
            rw [D.isometry.map_eq]
      _ = normGroupSet (omearaPlaneExtensionForm r a n D.coefficient)
          (hyperbolicExtensionLattice D.tailLattice n) :=
        normGroupSet_map_isometry D.isometry.toQuadraticSpaceIsometry
          (hyperbolicExtensionLattice D.tailLattice n)
  rw [hnorm]
  exact D.coefficient_mem_sourceNormGroup i

/-- O'Meara 82:16 followed by 93:13: a modular lattice on a hyperbolic
extension is isometric to a common tower of `a A(0,0)` over its modular tail,
provided the summand norm group is contained in the tail truncation norm
group. -/
noncomputable def HyperbolicModularDecomposition.normalizedIsometry
    {r : QuadraticSpace K W} {a : Kˣ} {n : Nat}
    {L : Lattice K (HyperbolicExtension K W n)}
    (D : HyperbolicModularDecomposition r a n L)
    (hgroup : normGroupSet (hyperbolicExtensionForm r n) L ⊆
      normGroupSet r
        (omearaScaleTruncation r D.tailLattice a)) :
    Isometry
      (omearaPlaneExtensionForm r a n (fun _ => 0))
      (hyperbolicExtensionForm r n)
      (hyperbolicExtensionLattice D.tailLattice n) L := by
  let normalized := normalizeScaledOmearaPlaneExtension
    r D.tailLattice a n D.coefficient
      (fun i => hgroup (D.coefficient_mem_targetNormGroup i))
  exact normalized.symm.trans D.isometry

end Lattice

end Bong
