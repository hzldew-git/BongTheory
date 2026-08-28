/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaDisplayedTower
import Bong.Lattice.OmearaUnimodularNormClassification

/-!
# Universe-polymorphic O'Meara classification foundations

This file restates the stable proofs of O'Meara 93:14a and 93:16 using
displayed towers.  Unlike the original nested-carrier implementation, the
field, modular summands, and complements may live in independent universes.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- O'Meara 93:14a for arbitrary displayed orthogonal splittings, with no
universe restriction on either summand or complement. -/
noncomputable def omeara9314a_abstract_universe
    {U : Type v} {U' : Type w} {V : Type x} {W : Type y}
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
  let normalizeSource := normalizeDisplayedScaledOmearaTower
    q L D.tailLattice a n D.coefficient hsourceCoefficient
  let normalizeTarget := normalizeDisplayedScaledOmearaTower
    r M E.tailLattice a n E.coefficient htargetCoefficient
  let sourceDisplayed := sourceSummand.orthogonalProductBasic
    (Isometry.refl q L)
  let targetDisplayed := targetSummand.orthogonalProductBasic
    (Isometry.refl r M)
  let sourceZero := normalizeSource.symm.trans sourceDisplayed
  let targetZero := normalizeTarget.symm.trans targetDisplayed
  let commonZero := sourceZero.trans (total.trans targetZero.symm)
  exact cancelDisplayedScaledZeroOmearaTower
    a D.tailLattice E.tailLattice n commonZero

/-- Stable normalization for two modular lattices on the same finite
hyperbolic tower after adjoining an arbitrary-universe complement. -/
noncomputable def stableHyperbolicModularProductIsometry_universe
    {X : Type v} [AddCommGroup X] [Module K X]
    {n : Nat}
    {J₁ J₂ : Lattice K
      (HyperbolicExtension K (Fin 0 → K) n)}
    (hJ₁ : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      J₁ (1 : Kˣ))
    (hJ₂ : IsModular
      (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
      J₂ (1 : Kˣ))
    (q : QuadraticSpace K X) (L : Lattice K X)
    (hgroup₁ : normGroupSet
        (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
        J₁ ⊆
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)))
    (hgroup₂ : normGroupSet
        (hyperbolicExtensionForm (zeroCoordinateQuadraticSpace (K := K)) n)
        J₂ ⊆
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ))) :
    Isometry
      ((hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n).orthogonalSum q)
      ((hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n).orthogonalSum q)
      (product J₁ L) (product J₂ L) := by
  let D₁ := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) (1 : Kˣ) n J₁ hJ₁
  let D₂ := hyperbolicModularDecomposition
    (zeroCoordinateQuadraticSpace (K := K)) (1 : Kˣ) n J₂ hJ₂
  have hcoefficient₁ : ∀ i, ((1 : Kˣ) : K) * D₁.coefficient i ∈
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)) := by
    intro i
    exact hgroup₁ (D₁.coefficient_mem_targetNormGroup i)
  have hcoefficient₂ : ∀ i, ((1 : Kˣ) : K) * D₂.coefficient i ∈
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)) := by
    intro i
    exact hgroup₂ (D₂.coefficient_mem_targetNormGroup i)
  let normalize₁ := normalizeDisplayedScaledOmearaTower
    q L D₁.tailLattice (1 : Kˣ) n D₁.coefficient hcoefficient₁
  let normalize₂ := normalizeDisplayedScaledOmearaTower
    q L D₂.tailLattice (1 : Kˣ) n D₂.coefficient hcoefficient₂
  let displayed₁ := D₁.isometry.orthogonalProductBasic (Isometry.refl q L)
  let displayed₂ := D₂.isometry.orthogonalProductBasic (Isometry.refl q L)
  let zeroToJ₁ := normalize₁.symm.trans displayed₁
  let zeroToJ₂ := normalize₂.symm.trans displayed₂
  let zeroBridge :=
    (scaledZeroOmearaTowerLatticeIsometry
      (1 : Kˣ) D₁.tailLattice D₂.tailLattice n).orthogonalProductBasic
        (Isometry.refl q L)
  exact zeroToJ₁.symm.trans (zeroBridge.trans zeroToJ₂)

section Omeara9316Universe

variable {X : Type v} [AddCommGroup X] [Module K X]
  {p : QuadraticSpace K X} {A B : Lattice K X}

/-- Universe-polymorphic O'Meara 93:16: unimodular lattices on one quadratic
space are isometric exactly when their norm groups agree. -/
noncomputable def omeara9316_of_normGroupSet_eq_universe
    (hA : IsUnimodular p A) (hB : IsUnimodular p B)
    (hgroup : normGroupSet p A = normGroupSet p B) :
    Isometry p p A B := by
  letI : FiniteDimensional K X :=
    A.ambientBasis.finiteDimensional_of_finite
  let negative := p.rescaleUnit (-1 : Kˣ)
  let hyperbolic := hyperbolicExtensionForm
    (zeroCoordinateQuadraticSpace (K := K)) (finrank K X)
  have hnegativeA : IsUnimodular negative A := by
    exact (isUnimodular_rescaleUnit_neg_one_iff p A).mpr hA
  have hnegativeB : IsUnimodular negative B := by
    exact (isUnimodular_rescaleUnit_neg_one_iff p B).mpr hB

  let middleA : Lattice K (X × X) := product A A
  let middleB : Lattice K (X × X) := product A B
  let middleAmbient := negative.orthogonalSum p
  let middleToHyperbolic : QuadraticSpace.Isometry middleAmbient hyperbolic :=
    negativeQuadraticHyperbolicIsometry p
  let middleModelA := map middleToHyperbolic.toLinearEquiv middleA
  let middleModelB := map middleToHyperbolic.toLinearEquiv middleB
  let middleAIsometry := Isometry.toMap middleAmbient middleToHyperbolic middleA
  let middleBIsometry := Isometry.toMap middleAmbient middleToHyperbolic middleB
  have hmiddleA : IsUnimodular middleAmbient middleA :=
    hnegativeA.orthogonalProduct hA
  have hmiddleB : IsUnimodular middleAmbient middleB :=
    hnegativeA.orthogonalProduct hB
  have hmiddleModelA : IsModular hyperbolic middleModelA (1 : Kˣ) :=
    hmiddleA.mapLatticeIsometry middleAIsometry
  have hmiddleModelB : IsModular hyperbolic middleModelB (1 : Kˣ) :=
    hmiddleB.mapLatticeIsometry middleBIsometry
  have hmiddleGroupA : normGroupSet hyperbolic middleModelA =
      normGroupSet p A := by
    calc
      normGroupSet hyperbolic middleModelA =
          normGroupSet middleAmbient middleA :=
        normGroupSet_eq_of_latticeIsometry middleAIsometry
      _ = normGroupSet p A :=
        normGroupSet_negativeMixedProduct (L := A) (N := A) rfl
  have hmiddleGroupB : normGroupSet hyperbolic middleModelB =
      normGroupSet p A := by
    calc
      normGroupSet hyperbolic middleModelB =
          normGroupSet middleAmbient middleB :=
        normGroupSet_eq_of_latticeIsometry middleBIsometry
      _ = normGroupSet p A :=
        normGroupSet_negativeMixedProduct (L := A) (N := B) hgroup
  have htruncA : omearaScaleTruncation p A (1 : Kˣ) = A :=
    omearaScaleTruncation_one_eq_of_unimodular hA
  have hmiddleContainA : normGroupSet hyperbolic middleModelA ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hmiddleGroupA, htruncA]
  have hmiddleContainB : normGroupSet hyperbolic middleModelB ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hmiddleGroupB, htruncA]
  let middleStable := stableHyperbolicModularProductIsometry_universe
    hmiddleModelA hmiddleModelB p A hmiddleContainA hmiddleContainB
  let middleAWithA := middleAIsometry.orthogonalProductBasic (Isometry.refl p A)
  let middleBWithA := middleBIsometry.orthogonalProductBasic (Isometry.refl p A)
  let stabilizedMiddle : Isometry
      (middleAmbient.orthogonalSum p) (middleAmbient.orthogonalSum p)
      (product middleA A) (product middleB A) :=
    middleAWithA.trans (middleStable.trans middleBWithA.symm)

  let commonSummand : Lattice K (X × X) := product A A
  let commonAmbient := p.orthogonalSum negative
  let commonToMiddle : Isometry
      (commonAmbient.orthogonalSum p) (middleAmbient.orthogonalSum p)
      (product commonSummand A) (product middleA A) :=
    (orthogonalProductSwap
      (q := p) (r := negative) (L := A) (M := A)).orthogonalProductBasic
        (Isometry.refl p A)
  let targetAssoc : Isometry
      (middleAmbient.orthogonalSum p)
      (negative.orthogonalSum (p.orthogonalSum p))
      (product middleB A) (product A (product B A)) :=
    orthogonalProductAssoc
  let targetInnerSwap : Isometry
      (negative.orthogonalSum (p.orthogonalSum p))
      (negative.orthogonalSum (p.orthogonalSum p))
      (product A (product B A)) (product A (product A B)) :=
    (Isometry.refl negative A).orthogonalProductBasic
      (orthogonalProductSwap (q := p) (r := p) (L := B) (M := A))
  let targetRotate : Isometry
      (negative.orthogonalSum (p.orthogonalSum p))
      ((p.orthogonalSum negative).orthogonalSum p)
      (product A (product A B)) (product (product A A) B) :=
    orthogonalProductRotateLeft
  let targetPermutation := targetAssoc.trans (targetInnerSwap.trans targetRotate)
  let total : Isometry
      (commonAmbient.orthogonalSum p) (commonAmbient.orthogonalSum p)
      (product commonSummand A) (product commonSummand B) :=
    commonToMiddle.trans (stabilizedMiddle.trans targetPermutation)

  let commonToHyperbolic : QuadraticSpace.Isometry commonAmbient hyperbolic :=
    quadraticNegativeHyperbolicIsometry p
  let commonModel := map commonToHyperbolic.toLinearEquiv commonSummand
  let commonIsometry := Isometry.toMap commonAmbient commonToHyperbolic commonSummand
  have hcommon : IsUnimodular commonAmbient commonSummand :=
    hA.orthogonalProduct hnegativeA
  have hcommonModel : IsModular hyperbolic commonModel (1 : Kˣ) :=
    hcommon.mapLatticeIsometry commonIsometry
  have hcommonGroup : normGroupSet commonAmbient commonSummand =
      normGroupSet p A := normGroupSet_quadraticNegativeProduct p A
  have hcancelA : normGroupSet commonAmbient commonSummand ⊆
      normGroupSet p (omearaScaleTruncation p A (1 : Kˣ)) := by
    rw [hcommonGroup, htruncA]
  have htruncB : omearaScaleTruncation p B (1 : Kˣ) = B :=
    omearaScaleTruncation_one_eq_of_unimodular hB
  have hcancelB : normGroupSet commonAmbient commonSummand ⊆
      normGroupSet p (omearaScaleTruncation p B (1 : Kˣ)) := by
    rw [hcommonGroup, htruncB, hgroup]
  exact omeara9314a_abstract_universe (1 : Kˣ)
    commonModel commonModel hcommonModel hcommonModel
    commonIsometry.symm commonIsometry.symm hcancelA hcancelB total

/-- Equivalence form of universe-polymorphic O'Meara 93:16. -/
theorem omeara9316_universe
    (hA : IsUnimodular p A) (hB : IsUnimodular p B) :
    IsIsometric p p A B ↔ normGroupSet p A = normGroupSet p B := by
  constructor
  · rintro ⟨f⟩
    exact (normGroupSet_eq_of_latticeIsometry f).symm
  · intro hgroup
    exact ⟨omeara9316_of_normGroupSet_eq_universe hA hB hgroup⟩

end Omeara9316Universe

end Lattice

end Bong
