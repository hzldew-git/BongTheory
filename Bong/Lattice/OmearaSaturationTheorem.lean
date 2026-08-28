/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaPairedHyperbolicCancellation

/-!
# O'Meara 93:21: existence of saturated Jordan splittings

This file completes the rank-three stabilization argument in O'Meara 93:21.
Every component is enlarged by two scaled hyperbolic planes, the enlarged
splitting is saturated by the already proved rank-seven construction, and
93:18(v) splits the planes back off.  The componentwise planes are gathered
into a common finite tower and cancelled by 93:14, so the resulting
complements form a saturated splitting of the original lattice.
-/

namespace Bong

open Dyadic Module

namespace Lattice
namespace JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {n : Nat} (J : JordanDecomposition q L (n + 2))
  (hrank : ∀ i, 3 ≤ J.componentRank i)

/-- Gather the stabilized original components into the common paired
hyperbolic tower. -/
noncomputable def saturationOriginalGatherIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        J.saturationStableCarrier J.saturationStableForm)
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm (n + 1)
          (fun i ↦ (J.component i).carrier)
          (fun i ↦ (J.component i).space))
        (n + 2) J.scaleGenerator)
      (BONG.blockProductLattice (n + 1)
        J.saturationStableCarrier J.saturationStableLattice)
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice (n + 1)
          (fun i ↦ (J.component i).carrier)
          (fun i ↦ (J.component i).lattice))
        (n + 2)) := by
  exact gatherPairedHyperbolicBlockProduct
    (fun i ↦ (J.component i).carrier)
    (fun i ↦ (J.component i).space)
    (fun i ↦ (J.component i).lattice)
    J.scaleGenerator

/-- Gather the stabilized complement components into the same kind of
paired hyperbolic tower. -/
noncomputable def saturationComplementGatherIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (J.saturationComplementStableCarrier hrank)
        (J.saturationComplementStableForm hrank))
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm (n + 1)
          (J.saturationComplementCarrier hrank)
          (J.saturationComplementForm hrank))
        (n + 2) J.scaleGenerator)
      (BONG.blockProductLattice (n + 1)
        (J.saturationComplementStableCarrier hrank)
        (J.saturationComplementStableLattice hrank))
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice (n + 1)
          (J.saturationComplementCarrier hrank)
          (J.saturationComplementLattice hrank))
        (n + 2)) := by
  exact gatherPairedHyperbolicBlockProduct
    (J.saturationComplementCarrier hrank)
    (J.saturationComplementForm hrank)
    (J.saturationComplementLattice hrank)
    J.scaleGenerator

/-- After gathering, the componentwise 93:18 splittings identify the two
paired towers. -/
noncomputable def saturationPairedTowerIsometry :
    Isometry
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm (n + 1)
          (J.saturationComplementCarrier hrank)
          (J.saturationComplementForm hrank))
        (n + 2) J.scaleGenerator)
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm (n + 1)
          (fun i ↦ (J.component i).carrier)
          (fun i ↦ (J.component i).space))
        (n + 2) J.scaleGenerator)
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice (n + 1)
          (J.saturationComplementCarrier hrank)
          (J.saturationComplementLattice hrank))
        (n + 2))
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice (n + 1)
          (fun i ↦ (J.component i).carrier)
          (fun i ↦ (J.component i).lattice))
        (n + 2)) :=
  (J.saturationComplementGatherIsometry hrank).symm |>.trans <|
    (J.saturationComplementStableTotalIsometry hrank).trans
      J.saturationOriginalGatherIsometry

/-- Iterated 93:14 cancels all common scaled hyperbolic planes, leaving an
isometry from the complement product to the original component product. -/
noncomputable def saturationComplementProductIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementForm hrank))
      (BONG.blockOrthogonalForm (n + 1)
        (fun i ↦ (J.component i).carrier)
        (fun i ↦ (J.component i).space))
      (BONG.blockProductLattice (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementLattice hrank))
      (BONG.blockProductLattice (n + 1)
        (fun i ↦ (J.component i).carrier)
        (fun i ↦ (J.component i).lattice)) :=
  cancelPairedHyperbolicExtension (n + 2) J.scaleGenerator
    (J.saturationPairedTowerIsometry hrank)

/-- The product of complements is integrally isometric to the original
quadratic lattice. -/
noncomputable def saturationComplementAmbientIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementForm hrank))
      q
      (BONG.blockProductLattice (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementLattice hrank))
      L :=
  (J.saturationComplementProductIsometry hrank).trans <|
    BONG.orthogonalDecompositionProductIsometry
      J.toOrthogonalDecomposition

/-- The saturated complement splitting transported back to the original
lattice. -/
noncomputable def saturatedJordanOfComponentRanksAtLeastThree :
    JordanDecomposition q L (n + 2) :=
  (J.saturationComplementJordan hrank).mapIsometry
    (J.saturationComplementAmbientIsometry hrank)

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastThree_scaleGenerator
    (i : Fin (n + 2)) :
    (J.saturatedJordanOfComponentRanksAtLeastThree hrank).scaleGenerator i =
      J.scaleGenerator i :=
  rfl

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastThree_componentRank
    (i : Fin (n + 2)) :
    (J.saturatedJordanOfComponentRanksAtLeastThree hrank).componentRank i =
      J.componentRank i := by
  rw [saturatedJordanOfComponentRanksAtLeastThree,
    mapIsometry_componentRank,
    J.saturationComplementJordan_componentRank]

/-- O'Meara 93:21 in the nontrivial multi-component case. -/
theorem saturatedJordanOfComponentRanksAtLeastThree_isSaturated :
    (J.saturatedJordanOfComponentRanksAtLeastThree hrank).IsSaturated := by
  intro i
  let C := J.saturationComplementJordan hrank
  let f := J.saturationComplementAmbientIsometry hrank
  let componentMap := (C.component i).mapLatticeIsometry f
  calc
    normGroupSet
        ((J.saturatedJordanOfComponentRanksAtLeastThree hrank).component i).space
        ((J.saturatedJordanOfComponentRanksAtLeastThree hrank).component i).lattice =
        normGroupSet (C.component i).space (C.component i).lattice :=
      normGroupSet_eq_of_latticeIsometry componentMap
    _ = J.fundamentalNormGroup i :=
      J.saturationComplementJordan_component_normGroup hrank i
    _ = (J.saturatedJordanOfComponentRanksAtLeastThree hrank).fundamentalNormGroup i := by
      unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
      rfl

/-! ## The one-component boundary and uniform nonempty statement -/

/-- Every one-component Jordan decomposition is already saturated. -/
theorem isSaturated_fin_one
    {q : QuadraticSpace K V} {L : Lattice K V}
    (J : JordanDecomposition q L 1) : J.IsSaturated := by
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  let D := J.scaleTruncationDecomposition
    (ordUnit K (J.scaleGenerator 0))
  have h := normGroupSet_eq_of_latticeIsometry
    D.singleComponentLatticeIsometry
  have hcomponent : D.component 0 = J.component 0 := by
    exact J.scaleTruncationDecomposition_component_self 0
  rw [hcomponent] at h
  exact h.symm

/-- A saturated splitting for every nonempty Jordan decomposition whose
components have rank at least three.  This is the uniform form of O'Meara
93:21 used by the classification theorem. -/
noncomputable def saturatedJordanOfComponentRanksAtLeastThreeNonempty
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (hrank : ∀ i, 3 ≤ J.componentRank i) :
    JordanDecomposition q L (m + 1) :=
  match m with
  | 0 => J
  | n + 1 => J.saturatedJordanOfComponentRanksAtLeastThree hrank

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastThreeNonempty_scaleGenerator
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (m + 1)) :
    (J.saturatedJordanOfComponentRanksAtLeastThreeNonempty hrank).scaleGenerator i =
      J.scaleGenerator i := by
  cases m with
  | zero => rfl
  | succ n => rfl

@[simp]
theorem saturatedJordanOfComponentRanksAtLeastThreeNonempty_componentRank
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (hrank : ∀ i, 3 ≤ J.componentRank i) (i : Fin (m + 1)) :
    (J.saturatedJordanOfComponentRanksAtLeastThreeNonempty hrank).componentRank i =
      J.componentRank i := by
  cases m with
  | zero => rfl
  | succ n =>
      exact J.saturatedJordanOfComponentRanksAtLeastThree_componentRank hrank i

theorem saturatedJordanOfComponentRanksAtLeastThreeNonempty_isSaturated
    {m : Nat} (J : JordanDecomposition q L (m + 1))
    (hrank : ∀ i, 3 ≤ J.componentRank i) :
    (J.saturatedJordanOfComponentRanksAtLeastThreeNonempty hrank).IsSaturated := by
  cases m with
  | zero => exact isSaturated_fin_one J
  | succ n =>
      exact J.saturatedJordanOfComponentRanksAtLeastThree_isSaturated hrank

end JordanDecomposition
end Lattice
end Bong
