/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaTwoHyperbolicPlaneSplitting
import Bong.Lattice.JordanRemoveComponent
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.OmearaSaturationCriterion
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Lattice.HyperbolicLatticeModular

/-!
# Geometry of one saturation step

For a selected Jordan component of rank at least seven, O'Meara 93:18(v)
splits two scaled hyperbolic planes.  This file displays the full lattice as

`H_s ⊥ H_s ⊥ (C ⊥ R)`

and proves that every element of the fundamental norm group at scale `s`
already belongs to the scale-truncation norm group of `C ⊥ R`.  The two
hyperbolic norm-group contributions lie in `2s O`, which is absorbed by the
positive-rank `s`-modular lattice `C`.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- A modular lattice at the indexing parameter is unchanged by the
order-indexed scale truncation. -/
theorem scaleTruncation_eq_of_isModular
    (hL : IsModular q L s) :
    scaleTruncation q L (ordUnit K s) = L := by
  rw [← omearaScaleTruncation_eq_scaleTruncation,
    omearaScaleTruncation_eq_of_isModular hL]

/-- The norm group of a scaled hyperbolic plane is absorbed by any
positive-rank modular lattice at the same scale. -/
theorem normGroupSet_scaledHyperbolic_subset_of_modular
    (hL : IsModular q L s) (hpos : 0 < finrank K V) :
    normGroupSet (QuadraticSpace.hyperbolicPlane s)
        (hyperbolicPlaneLattice (K := K)) ⊆
      normGroupSet q L := by
  have htwo : twoScaleIdeal q L =
      principalIdeal (K := K) (2 * (s : K)) := by
    rw [twoScaleIdeal, hL.scaleIdeal_eq_principal hpos,
      twiceIdeal_principalIdeal]
  intro z hz
  have hzIdeal : z ∈ principalIdeal (K := K) (2 * (s : K)) := by
    rw [← normIdeal_hyperbolicPlaneLattice s]
    exact normGroupSet_subset_normIdeal
      (QuadraticSpace.hyperbolicPlane s)
      (hyperbolicPlaneLattice (K := K)) hz
  apply twoScaleIdeal_subset_normGroupSet q L
  rw [htwo]
  exact hzIdeal

variable {W X : Type v} [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]
  {c : QuadraticSpace K W} {C : Lattice K W}
  {r : QuadraticSpace K X} {R : Lattice K X}

/-- At the scale of a positive-rank modular factor, two displayed scaled
hyperbolic planes contribute no new elements to the norm group of the scale
truncation.  This is the absorption calculation in O'Meara 93:21. -/
theorem normGroupSet_two_scaledHyperbolic_scaleTruncation_subset_base
    (hC : IsModular c C s) (hCpos : 0 < finrank K W) :
    normGroupSet
        ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
            (c.orthogonalSum r)))
        (scaleTruncation
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
            ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
              (c.orthogonalSum r)))
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicPlaneLattice (K := K)) (product C R)))
          (ordUnit K s)) ⊆
      normGroupSet (c.orthogonalSum r)
        (scaleTruncation (c.orthogonalSum r) (product C R)
          (ordUnit K s)) := by
  have hH := hyperbolicPlaneLattice_isModular (K := K) s
  have hsource :
      scaleTruncation
          ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
            ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
              (c.orthogonalSum r)))
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicPlaneLattice (K := K)) (product C R)))
          (ordUnit K s) =
        product (hyperbolicPlaneLattice (K := K))
          (product (hyperbolicPlaneLattice (K := K))
            (scaleTruncation (c.orthogonalSum r) (product C R)
              (ordUnit K s))) := by
    rw [scaleTruncation_orthogonalProduct,
      scaleTruncation_eq_of_isModular hH,
      scaleTruncation_orthogonalProduct,
      scaleTruncation_eq_of_isModular hH]
  have hbase :
      scaleTruncation (c.orthogonalSum r) (product C R) (ordUnit K s) =
        product C (scaleTruncation r R (ordUnit K s)) := by
    rw [scaleTruncation_orthogonalProduct,
      scaleTruncation_eq_of_isModular hC]
  intro z hz
  rw [hsource, mem_normGroupSet_orthogonalProduct_iff] at hz
  rcases hz with ⟨h₁, hh₁, z₁, hz₁, rfl⟩
  rw [mem_normGroupSet_orthogonalProduct_iff] at hz₁
  rcases hz₁ with ⟨h₂, hh₂, b, hb, rfl⟩
  have hh₁C : h₁ ∈ normGroupSet c C :=
    normGroupSet_scaledHyperbolic_subset_of_modular hC hCpos hh₁
  have hh₂C : h₂ ∈ normGroupSet c C :=
    normGroupSet_scaledHyperbolic_subset_of_modular hC hCpos hh₂
  have liftC : ∀ {x : K}, x ∈ normGroupSet c C →
      x ∈ normGroupSet (c.orthogonalSum r)
        (scaleTruncation (c.orthogonalSum r) (product C R)
          (ordUnit K s)) := by
    intro x hx
    rw [hbase, mem_normGroupSet_orthogonalProduct_iff]
    exact ⟨x, hx, 0, zero_mem_normGroupSet r
      (scaleTruncation r R (ordUnit K s)), by simp⟩
  exact add_mem_normGroupSet (c.orthogonalSum r)
    (scaleTruncation (c.orthogonalSum r) (product C R) (ordUnit K s))
    (liftC hh₁C)
    (add_mem_normGroupSet (c.orthogonalSum r)
      (scaleTruncation (c.orthogonalSum r) (product C R) (ordUnit K s))
      (liftC hh₂C) hb)

namespace OmearaTwoHyperbolicPlaneData

/-- The selected modular component, displayed as two canonical scaled
hyperbolic planes followed by the modular complement. -/
noncomputable def displayedIsometry
    (S : OmearaTwoHyperbolicPlaneData q L s) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
          (S.decomposition.component 2).space))
      q
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (S.decomposition.component 2).lattice))
      L := by
  let D := S.decomposition
  let U := D.suffixQuadraticSublattice 1
  let T := D.tailDecomposition
  let secondToTail : Isometry
      (QuadraticSpace.hyperbolicPlane s) (T.component 0).space
      (hyperbolicPlaneLattice (K := K)) (T.component 0).lattice :=
    S.secondHyperbolic.symm.trans (D.tailComponentIsometry 0)
  let complementToTail : Isometry
      (D.component 2).space (T.component 1).space
      (D.component 2).lattice (T.component 1).lattice := by
    change Isometry
      (D.component 2).space (D.tailComponent (1 : Fin 2)).space
      (D.component 2).lattice (D.tailComponent (1 : Fin 2)).lattice
    have hindex : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    let g := D.tailComponentIsometry (1 : Fin 2)
    rw [hindex] at g
    exact g
  let tailDisplayed : Isometry
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum
        (D.component 2).space)
      U.space
      (product (hyperbolicPlaneLattice (K := K))
        (D.component 2).lattice)
      U.lattice :=
    (secondToTail.orthogonalProductBasic complementToTail).trans
      T.pairProductLatticeIsometry
  let firstToHead : Isometry
      (QuadraticSpace.hyperbolicPlane s) (D.component 0).space
      (hyperbolicPlaneLattice (K := K)) (D.component 0).lattice :=
    S.firstHyperbolic.symm
  exact (firstToHead.orthogonalProductBasic tailDisplayed).trans
    D.headTailDecomposition.pairProductLatticeIsometry

end OmearaTwoHyperbolicPlaneData

namespace JordanDecomposition

variable {n : Nat} (J : JordanDecomposition q L (n + 2))
  (i : Fin (n + 2))

/-- After splitting the selected component twice, the base left after the
two displayed planes is `C ⊥ R`. -/
noncomputable def saturationBase
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    QuadraticSpace K
      ((S.decomposition.component 2).carrier ×
        (J.selectedRemainder i).carrier) :=
  (S.decomposition.component 2).space.orthogonalSum
    (J.selectedRemainder i).space

noncomputable def saturationBaseLattice
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    Lattice K
      ((S.decomposition.component 2).carrier ×
        (J.selectedRemainder i).carrier) :=
  product (S.decomposition.component 2).lattice
    (J.selectedRemainder i).lattice

/-- The full lattice displayed as two scaled hyperbolic planes over the
base `C ⊥ R`. -/
noncomputable def saturationDisplayedIsometry
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i)) :
    Isometry
      ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
          (J.saturationBase i S)))
      q
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (J.saturationBaseLattice i S)))
      L := by
  let E := J.selectedFirstOrthogonalDecomposition i
  let R := J.selectedRemainder i
  let selected : Isometry
      ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
          (S.decomposition.component 2).space))
      (E.component 0).space
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (S.decomposition.component 2).lattice))
      (E.component 0).lattice := by
    have hhead : E.component 0 = J.component i :=
      J.selectedFirst_component_zero i
    rw [hhead]
    exact S.displayedIsometry
  let keepR := Isometry.refl R.space R.lattice
  let grouped := selected.orthogonalProductBasic keepR
  let associateInner :=
    (Isometry.refl (QuadraticSpace.hyperbolicPlane (J.scaleGenerator i))
      (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
        (orthogonalProductAssoc.symm : Isometry
          ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
            ((S.decomposition.component 2).space.orthogonalSum R.space))
          (((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
            (S.decomposition.component 2).space).orthogonalSum R.space)
          (product (hyperbolicPlaneLattice (K := K))
            (product (S.decomposition.component 2).lattice R.lattice))
          (product
            (product (hyperbolicPlaneLattice (K := K))
              (S.decomposition.component 2).lattice) R.lattice))
  let associateOuter : Isometry
      ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
        (((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
          (S.decomposition.component 2).space).orthogonalSum R.space))
      (((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
          (S.decomposition.component 2).space)).orthogonalSum R.space)
      (product (hyperbolicPlaneLattice (K := K))
        (product
          (product (hyperbolicPlaneLattice (K := K))
            (S.decomposition.component 2).lattice) R.lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (product (hyperbolicPlaneLattice (K := K))
            (S.decomposition.component 2).lattice)) R.lattice) :=
    orthogonalProductAssoc.symm
  exact associateInner.trans <| associateOuter.trans <|
    grouped.trans E.headTailDecomposition.pairProductLatticeIsometry

/-- Every element of the selected fundamental norm group is already
represented by the scale truncation of the base left after splitting two
hyperbolic planes. -/
theorem fundamentalNormGroup_subset_saturationBaseTruncation
    (S : OmearaTwoHyperbolicPlaneData
      (J.component i).space (J.component i).lattice
        (J.scaleGenerator i))
    (hrank : 7 ≤ J.componentRank i) :
    J.fundamentalNormGroup i ⊆
      normGroupSet (J.saturationBase i S)
        (omearaScaleTruncation (J.saturationBase i S)
          (J.saturationBaseLattice i S) (J.scaleGenerator i)) := by
  let C := S.decomposition.component 2
  let R := J.selectedRemainder i
  let B := J.saturationBase i S
  let BL := J.saturationBaseLattice i S
  let F := J.saturationDisplayedIsometry i S
  have hCpos : 0 < finrank K C.carrier := by
    rw [S.complement_finrank]
    change 7 ≤ finrank K (J.component i).carrier at hrank
    omega
  intro z hz
  change z ∈ normGroupSet q
    (scaleTruncation q L (ordUnit K (J.scaleGenerator i))) at hz
  have hzDisplayed : z ∈ normGroupSet
      ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum B))
      (scaleTruncation
        ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
          ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum B))
        (product (hyperbolicPlaneLattice (K := K))
          (product (hyperbolicPlaneLattice (K := K)) BL))
        (ordUnit K (J.scaleGenerator i))) := by
    rw [← normGroupSet_scaleTruncation_eq_of_isometry F
      (ordUnit K (J.scaleGenerator i))]
    exact hz
  rw [omearaScaleTruncation_eq_scaleTruncation]
  exact normGroupSet_two_scaledHyperbolic_scaleTruncation_subset_base
    S.complement_modular hCpos hzDisplayed

end JordanDecomposition

end Lattice

end Bong
