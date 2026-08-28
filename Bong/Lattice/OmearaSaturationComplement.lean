/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationStabilization

/-!
# Complements after O'Meara saturation

After saturating the twice-hyperbolically stabilized Jordan splitting,
O'Meara 93:18(v) splits the two standard hyperbolic planes back off every
component.  The remaining complements have the original component ranks,
scales, and fundamental norm groups.  This file packages those complements
as a Jordan decomposition and assembles all displayed component splittings
into one integral isometry.
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

/-- The saturated stabilized Jordan splitting used in the cancellation
step. -/
noncomputable abbrev saturationAmbientJordan :=
  J.saturatedStabilizedJordan hrank

/-- Every saturated stabilized component has enough rank for two
applications of O'Meara 93:18(v). -/
theorem saturationAmbient_componentRank_atLeastSeven
    (i : Fin (n + 2)) :
    7 ≤ (J.saturationAmbientJordan hrank).componentRank i := by
  rw [saturationAmbientJordan,
    J.saturatedStabilizedJordan_componentRank hrank]
  have hi := hrank i
  omega

/-- The modularity parameter of a saturated stabilized component is the
original Jordan scale. -/
theorem saturationAmbient_modular_at_originalScale
    (i : Fin (n + 2)) :
    IsModular
      ((J.saturationAmbientJordan hrank).component i).space
      ((J.saturationAmbientJordan hrank).component i).lattice
      (J.scaleGenerator i) := by
  rw [← J.saturatedStabilizedJordan_scaleGenerator hrank i]
  exact (J.saturationAmbientJordan hrank).modular i

/-- Split the two standard hyperbolic planes from one saturated stabilized
component. -/
noncomputable def saturationComplementSplit (i : Fin (n + 2)) :
    OmearaTwoHyperbolicPlaneData
      ((J.saturationAmbientJordan hrank).component i).space
      ((J.saturationAmbientJordan hrank).component i).lattice
      (J.scaleGenerator i) :=
  omearaTwoHyperbolicPlaneData
    (J.saturationAmbient_modular_at_originalScale hrank i)
    (J.saturationAmbient_componentRank_atLeastSeven hrank i)

/-- The carrier of the complement left after removing both planes. -/
noncomputable abbrev saturationComplementCarrier
    (i : Fin (n + 2)) : Type (max u v) :=
  ((J.saturationComplementSplit hrank i).decomposition.component 2).carrier

/-- The quadratic form of the complement left after removing both planes. -/
noncomputable def saturationComplementForm (i : Fin (n + 2)) :
    QuadraticSpace K (J.saturationComplementCarrier hrank i) :=
  ((J.saturationComplementSplit hrank i).decomposition.component 2).space

/-- The integral complement left after removing both planes. -/
noncomputable def saturationComplementLattice (i : Fin (n + 2)) :
    Lattice K (J.saturationComplementCarrier hrank i) :=
  ((J.saturationComplementSplit hrank i).decomposition.component 2).lattice

/-- The complement is modular at the original component scale. -/
theorem saturationComplement_modular (i : Fin (n + 2)) :
    IsModular (J.saturationComplementForm hrank i)
      (J.saturationComplementLattice hrank i) (J.scaleGenerator i) :=
  (J.saturationComplementSplit hrank i).complement_modular

/-- Removing the two stabilization planes restores the original component
rank. -/
theorem saturationComplement_finrank (i : Fin (n + 2)) :
    finrank K (J.saturationComplementCarrier hrank i) =
      J.componentRank i := by
  have h := (J.saturationComplementSplit hrank i).complement_finrank
  change finrank K (J.saturationComplementCarrier hrank i) =
      (J.saturationAmbientJordan hrank).componentRank i - 4 at h
  rw [J.saturatedStabilizedJordan_componentRank hrank] at h
  have hi := hrank i
  omega

/-- The complement has the original fundamental norm group. -/
theorem saturationComplement_normGroup_eq_fundamental
    (i : Fin (n + 2)) :
    normGroupSet (J.saturationComplementForm hrank i)
        (J.saturationComplementLattice hrank i) =
      J.fundamentalNormGroup i := by
  let S := J.saturationComplementSplit hrank i
  have hpos : 0 < finrank K (J.saturationComplementCarrier hrank i) := by
    rw [J.saturationComplement_finrank hrank i]
    have hi := hrank i
    omega
  calc
    normGroupSet (J.saturationComplementForm hrank i)
        (J.saturationComplementLattice hrank i) =
        normGroupSet
          ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
            ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
              (J.saturationComplementForm hrank i)))
          (product (hyperbolicPlaneLattice (K := K))
            (product (hyperbolicPlaneLattice (K := K))
              (J.saturationComplementLattice hrank i))) :=
      (normGroupSet_two_scaledHyperbolic_eq_modular
        (J.saturationComplement_modular hrank i) hpos).symm
    _ = normGroupSet
        ((J.saturationAmbientJordan hrank).component i).space
        ((J.saturationAmbientJordan hrank).component i).lattice :=
      (normGroupSet_eq_of_latticeIsometry S.displayedIsometry).symm
    _ = (J.saturationAmbientJordan hrank).fundamentalNormGroup i :=
      J.saturatedStabilizedJordan_isSaturated hrank i
    _ = J.fundamentalNormGroup i :=
      J.saturatedStabilizedJordan_fundamentalNormGroup hrank i

/-- A chosen anisotropic norm generator of a saturation complement. -/
noncomputable def saturationComplementNormGeneratorVector
    (i : Fin (n + 2)) : J.saturationComplementCarrier hrank i :=
  Classical.choose <|
    exists_isNormGenerator_of_finrank_pos
      (J.saturationComplementForm hrank i)
      (J.saturationComplementLattice hrank i)
      (by
        rw [J.saturationComplement_finrank hrank i]
        have hi := hrank i
        omega)

theorem saturationComplementNormGeneratorVector_spec
    (i : Fin (n + 2)) :
    IsNormGenerator (J.saturationComplementForm hrank i)
        (J.saturationComplementLattice hrank i)
        (J.saturationComplementNormGeneratorVector hrank i) ∧
      (J.saturationComplementForm hrank i).IsAnisotropic
        (J.saturationComplementNormGeneratorVector hrank i) :=
  Classical.choose_spec <|
    exists_isNormGenerator_of_finrank_pos
      (J.saturationComplementForm hrank i)
      (J.saturationComplementLattice hrank i)
      (by
        rw [J.saturationComplement_finrank hrank i]
        have hi := hrank i
        omega)

/-- The chosen scalar norm generator of a saturation complement. -/
noncomputable def saturationComplementNormGenerator
    (i : Fin (n + 2)) : Kˣ :=
  Units.mk0
    ((J.saturationComplementForm hrank i).quadratic
      (J.saturationComplementNormGeneratorVector hrank i))
    (J.saturationComplementNormGeneratorVector_spec hrank i).2

theorem saturationComplement_normIdeal_eq (i : Fin (n + 2)) :
    normIdeal (J.saturationComplementForm hrank i)
        (J.saturationComplementLattice hrank i) =
      principalIdeal (K := K)
        (J.saturationComplementNormGenerator hrank i : K) :=
  (J.saturationComplementNormGeneratorVector_spec hrank i).1.normIdeal_eq

theorem saturationComplement_scaleIdeal_eq (i : Fin (n + 2)) :
    scaleIdeal (J.saturationComplementForm hrank i)
        (J.saturationComplementLattice hrank i) =
      principalIdeal (K := K) (J.scaleGenerator i : K) :=
  (J.saturationComplement_modular hrank i).scaleIdeal_eq_principal
    (by
      rw [J.saturationComplement_finrank hrank i]
      have hi := hrank i
      omega)

/-- Assemble the complements into a Jordan splitting on their coordinate
product. -/
noncomputable def saturationComplementJordan :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementForm hrank))
      (BONG.blockProductLattice (n + 1)
        (J.saturationComplementCarrier hrank)
        (J.saturationComplementLattice hrank))
      (n + 2) :=
  BONG.blockProductJordanDecomposition
    (J.saturationComplementCarrier hrank)
    (J.saturationComplementForm hrank)
    (J.saturationComplementLattice hrank)
    J.scaleGenerator (J.saturationComplementNormGenerator hrank)
    (J.saturationComplement_modular hrank)
    (J.saturationComplement_scaleIdeal_eq hrank)
    (J.saturationComplement_normIdeal_eq hrank)
    (fun _ _ hij ↦ J.scaleOrder_strict hij)

@[simp]
theorem saturationComplementJordan_scaleGenerator
    (i : Fin (n + 2)) :
    (J.saturationComplementJordan hrank).scaleGenerator i =
      J.scaleGenerator i :=
  rfl

@[simp]
theorem saturationComplementJordan_componentRank
    (i : Fin (n + 2)) :
    (J.saturationComplementJordan hrank).componentRank i =
      J.componentRank i := by
  rw [saturationComplementJordan,
    BONG.blockProductJordanDecomposition_componentRank,
    J.saturationComplement_finrank]

/-- The displayed complement component in the assembled Jordan splitting
has the original fundamental norm group. -/
theorem saturationComplementJordan_component_normGroup
    (i : Fin (n + 2)) :
    normGroupSet ((J.saturationComplementJordan hrank).component i).space
        ((J.saturationComplementJordan hrank).component i).lattice =
      J.fundamentalNormGroup i := by
  let f := BONG.blockProductComponentIsometry
    (J.saturationComplementCarrier hrank)
    (J.saturationComplementForm hrank)
    (J.saturationComplementLattice hrank) i
  calc
    normGroupSet ((J.saturationComplementJordan hrank).component i).space
        ((J.saturationComplementJordan hrank).component i).lattice =
        normGroupSet (J.saturationComplementForm hrank i)
          (J.saturationComplementLattice hrank i) :=
      normGroupSet_eq_of_latticeIsometry f
    _ = J.fundamentalNormGroup i :=
      J.saturationComplement_normGroup_eq_fundamental hrank i

/-- The componentwise source of all two-plane splittings. -/
noncomputable abbrev saturationComplementStableCarrier
    (i : Fin (n + 2)) : Type (max u v) :=
  (Fin 2 → K) ×
    ((Fin 2 → K) × J.saturationComplementCarrier hrank i)

noncomputable def saturationComplementStableForm (i : Fin (n + 2)) :
    QuadraticSpace K (J.saturationComplementStableCarrier hrank i) :=
  (QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
    ((QuadraticSpace.hyperbolicPlane (J.scaleGenerator i)).orthogonalSum
      (J.saturationComplementForm hrank i))

noncomputable def saturationComplementStableLattice (i : Fin (n + 2)) :
    Lattice K (J.saturationComplementStableCarrier hrank i) :=
  product (hyperbolicPlaneLattice (K := K))
    (product (hyperbolicPlaneLattice (K := K))
      (J.saturationComplementLattice hrank i))

/-- Each componentwise splitting isometry, with its source written in the
canonical two-plane coordinates. -/
noncomputable def saturationComplementStableComponentIsometry
    (i : Fin (n + 2)) :
    Isometry (J.saturationComplementStableForm hrank i)
      ((J.saturationAmbientJordan hrank).component i).space
      (J.saturationComplementStableLattice hrank i)
      ((J.saturationAmbientJordan hrank).component i).lattice :=
  (J.saturationComplementSplit hrank i).displayedIsometry

/-- Assemble all componentwise two-plane splittings into an isometry from
the stabilized complement product to the stabilized ambient lattice. -/
noncomputable def saturationComplementStableTotalIsometry :
    Isometry
      (BONG.blockOrthogonalForm (n + 1)
        (J.saturationComplementStableCarrier hrank)
        (J.saturationComplementStableForm hrank))
      (BONG.blockOrthogonalForm (n + 1)
        J.saturationStableCarrier J.saturationStableForm)
      (BONG.blockProductLattice (n + 1)
        (J.saturationComplementStableCarrier hrank)
        (J.saturationComplementStableLattice hrank))
      (BONG.blockProductLattice (n + 1)
        J.saturationStableCarrier J.saturationStableLattice) := by
  let componentProduct := BONG.blockProductLatticeIsometry
    (fun i ↦ J.saturationComplementStableForm hrank i)
    (fun i ↦ ((J.saturationAmbientJordan hrank).component i).space)
    (fun i ↦ J.saturationComplementStableLattice hrank i)
    (fun i ↦ ((J.saturationAmbientJordan hrank).component i).lattice)
    (J.saturationComplementStableComponentIsometry hrank)
  let ambientProduct := BONG.orthogonalDecompositionProductIsometry
    (J.saturationAmbientJordan hrank).toOrthogonalDecomposition
  exact componentProduct.trans ambientProduct

end JordanDecomposition
end Lattice
end Bong
