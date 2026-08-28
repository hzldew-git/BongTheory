/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaStableModularCancellation

/-!
# O'Meara 93:14a for abstract orthogonal splittings

This file supplies the reassociation bridge from the explicit nested
hyperbolic model to an arbitrary displayed splitting `J ⊥ K`.  Combined with
the 82:16 decomposition and the scaled 93:13 normalization, it gives the
literal cancellation conclusion of Corollary 93:14a.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The unique quadratic space on the zero-dimensional coordinate space. -/
def zeroCoordinateQuadraticSpace : QuadraticSpace K (Fin 0 → K) where
  bilin := 0
  isSymm := ⟨by simp⟩
  nondegenerate := by
    constructor <;> intro x _
    · funext i
      exact Fin.elim0 i
    · funext i
      exact Fin.elim0 i

/-- Remove a zero-dimensional lattice factor from the left of an orthogonal
product.  The zero lattice may be any full lattice on the zero carrier. -/
noncomputable def zeroLeftOrthogonalProductIsometry
    {V : Type v} [AddCommGroup V] [Module K V]
    (Z : Lattice K (Fin 0 → K))
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry
      ((zeroCoordinateQuadraticSpace (K := K)).orthogonalSum q) q
      (product Z L) L where
  toLinearEquiv :=
    { toFun := fun x => x.2
      invFun := fun y => (0, y)
      left_inv := by
        intro x
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      right_inv := by intro; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  map_bilin := by
    intro x y
    rw [QuadraticSpace.orthogonalSum_bilin_apply]
    change q.bilin x.2 y.2 = 0 + q.bilin x.2 y.2
    simp
  map_mem := by
    intro x
    rw [mem_product_iff]
    have hx : x.1 = 0 := Subsingleton.elim _ _
    change x.1 ∈ Z ∧ x.2 ∈ L ↔ x.2 ∈ L
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [hx]; exact Z.zero_mem, h⟩

/-- Reassociate a nested O'Meara plane tower with an external complement:
`(A_1 ⊥ ... ⊥ A_n) ⊥ K` becomes `A_1 ⊥ ... ⊥ A_n ⊥ K`. -/
noncomputable def omearaPlaneExtensionAppendIsometry
    {V : Type u} [AddCommGroup V] [Module K V]
    (Z : Lattice K (Fin 0 → K))
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) :
    (n : Nat) → (alpha : Fin n → K) →
      Isometry
        ((omearaPlaneExtensionForm
          (zeroCoordinateQuadraticSpace (K := K)) a n alpha).orthogonalSum q)
        (omearaPlaneExtensionForm q a n alpha)
        (product (hyperbolicExtensionLattice Z n) L)
        (hyperbolicExtensionLattice L n)
  | 0, _ => zeroLeftOrthogonalProductIsometry Z q L
  | n + 1, alpha => by
      let head := (QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a
      let tail := omearaPlaneExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) a n (Fin.tail alpha)
      let reassociate : Isometry
          ((head.orthogonalSum tail).orthogonalSum q)
          (head.orthogonalSum (tail.orthogonalSum q))
          (product
            (product (hyperbolicPlaneLattice (K := K))
              (hyperbolicExtensionLattice Z n)) L)
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicExtensionLattice Z n) L)) :=
        orthogonalProductAssoc
      let recursive := omearaPlaneExtensionAppendIsometry
        Z q L a n (Fin.tail alpha)
      let headIdentity : Isometry head head
          (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)) :=
        Isometry.refl head (hyperbolicPlaneLattice (K := K))
      let combined := reassociate.trans
        (headIdentity.orthogonalProductBasic recursive)
      change Isometry
        (((((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
            (omearaPlaneExtensionForm
              (zeroCoordinateQuadraticSpace (K := K)) a n
                (Fin.tail alpha))).orthogonalSum q))
        (((QuadraticSpace.omearaPlane (alpha 0)).rescaleUnit a).orthogonalSum
          (omearaPlaneExtensionForm q a n (Fin.tail alpha)))
        (product
          (product (hyperbolicPlaneLattice (K := K))
            (hyperbolicExtensionLattice Z n)) L)
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicExtensionLattice L n))
      exact combined

/-- Transport the norm group through an integral lattice isometry. -/
theorem normGroupSet_eq_of_latticeIsometry
    {V : Type v} {W : Type w} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) :
    normGroupSet r M = normGroupSet q L := by
  calc
    normGroupSet r M = normGroupSet r (map f.toLinearEquiv L) := by
      rw [f.map_eq]
    _ = normGroupSet q L :=
      normGroupSet_map_isometry f.toQuadraticSpaceIsometry L

/-- O'Meara 93:14a for two arbitrary displayed orthogonal splittings.

`Jmodel` and `Jmodel'` are the two modular summands transported to explicit
hyperbolic coordinate spaces.  Their modular decompositions are constructed
by 82:16; `summand` and `summand'` identify those coordinate models with the
abstract displayed summands.  The remaining hypotheses are exactly the two
published norm-group containments. -/
noncomputable def omeara9314a_abstract
    {U U' V W : Type u}
    [AddCommGroup U] [Module K U]
    [AddCommGroup U'] [Module K U']
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K U} {p' : QuadraticSpace K U'}
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {J : Lattice K U} {J' : Lattice K U'}
    {L : Lattice K V} {M : Lattice K W}
    {n : Nat} (a : Kˣ)
    (Jmodel : Lattice K
      (HyperbolicExtension K (Fin 0 → K) n))
    (Jmodel' : Lattice K
      (HyperbolicExtension K (Fin 0 → K) n))
    (hJmodel : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      Jmodel a)
    (hJmodel' : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      Jmodel' a)
    (summand : Isometry
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      p Jmodel J)
    (summand' : Isometry
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      p' Jmodel' J')
    (hgroup : normGroupSet p J ⊆
      normGroupSet q (omearaScaleTruncation q L a))
    (hgroup' : normGroupSet p' J' ⊆
      normGroupSet r (omearaScaleTruncation r M a))
    (total : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)
      (product J L) (product J' M)) :
    Isometry q r L M := by
  let D := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) a n Jmodel hJmodel
  let E := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) a n Jmodel' hJmodel'
  let sourceSummand := D.isometry.trans summand
  let targetSummand := E.isometry.trans summand'
  let sourceAppend := omearaPlaneExtensionAppendIsometry
    D.tailLattice q L a n D.coefficient
  let targetAppend := omearaPlaneExtensionAppendIsometry
    E.tailLattice r M a n E.coefficient
  let sourceDisplayed := sourceAppend.symm.trans
    (sourceSummand.orthogonalProductBasic (Isometry.refl q L))
  let targetDisplayed := targetAppend.symm.trans
    (targetSummand.orthogonalProductBasic (Isometry.refl r M))
  have hsourceCoefficient : ∀ i, (a : K) * D.coefficient i ∈
      normGroupSet q (omearaScaleTruncation q L a) := by
    intro i
    apply hgroup
    rw [normGroupSet_eq_of_latticeIsometry summand]
    exact D.coefficient_mem_targetNormGroup i
  have htargetCoefficient : ∀ i, (a : K) * E.coefficient i ∈
      normGroupSet r (omearaScaleTruncation r M a) := by
    intro i
    apply hgroup'
    rw [normGroupSet_eq_of_latticeIsometry summand']
    exact E.coefficient_mem_targetNormGroup i
  let normalizeSource := normalizeScaledOmearaPlaneExtension
    q L a n D.coefficient hsourceCoefficient
  let normalizeTarget := normalizeScaledOmearaPlaneExtension
    r M a n E.coefficient htargetCoefficient
  let sourceZero := normalizeSource.symm.trans sourceDisplayed
  let targetZero := normalizeTarget.symm.trans targetDisplayed
  let commonZeroTower := sourceZero.trans (total.trans targetZero.symm)
  exact cancelScaledZeroOmearaPlaneExtension a n commonZeroTower

end Lattice

end Bong
