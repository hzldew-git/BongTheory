/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturatedJordan
import Bong.Lattice.OmearaOddWeightPlane
import Bong.Bong.JordanScaleTruncation

/-!
# A generator criterion for saturated Jordan components

The proof of O'Meara 93:21 moves two scalar values into each sufficiently
large modular component: a fundamental norm generator and a generator of the
fundamental weight.  This file isolates the ideal-theoretic conclusion of
that operation.  Once both values occur in the component norm group, the
component norm group is the intrinsic fundamental norm group.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- A canonical nonzero generator of the selected weight ideal. -/
noncomputable def weightIdealGenerator
    (q : QuadraticSpace K V) (L : Lattice K V) : Kˣ :=
  uniformizerPowerUnit K (weightIdealOrder q L)

@[simp]
theorem ordUnit_weightIdealGenerator
    (q : QuadraticSpace K V) (L : Lattice K V) :
    ordUnit K (weightIdealGenerator q L) = weightIdealOrder q L := by
  simp [weightIdealGenerator]

theorem principalIdeal_weightIdealGenerator
    (q : QuadraticSpace K V) (L : Lattice K V) :
    principalIdeal (K := K) ((weightIdealGenerator q L : Kˣ) : K) =
      weightIdeal q L := by
  rw [principalIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
    ordUnit_weightIdealGenerator]

theorem weightIdealGenerator_mem_normGroupSet
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (ha : IsNormGeneratorValue q L a) :
    ((weightIdealGenerator q L : Kˣ) : K) ∈ normGroupSet q L := by
  apply weightIdeal_subset_normGroupSet a ha
  rw [← principalIdeal_weightIdealGenerator q L]
  exact generator_mem_principalIdeal _

/-- Monotonicity of the selected weight under inclusion of norm groups,
provided the two lattices have the same norm generator and doubled scale.
This is the precise ideal-theoretic form of the weight argument in 93:21. -/
theorem weightIdeal_mono_of_normGroupSet_subset
    (a : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hb : IsNormGeneratorValue r M a)
    (htwo : twoScaleIdeal q L = twoScaleIdeal r M)
    (hgroup : normGroupSet q L ⊆ normGroupSet r M) :
    weightIdeal q L ≤ weightIdeal r M := by
  rcases weightIdeal_eq_twoScale_or_odd a ha with hterminal | hodd
  · rw [hterminal, htwo]
    exact twoScaleIdeal_le_weightIdeal r M
  · rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
      powerIdeal_le_iff]
    let z : Kˣ := weightIdealGenerator q L
    have hzSource : (z : K) ∈ normGroupSet q L :=
      weightIdealGenerator_mem_normGroupSet q L a ha
    have hzTarget : (z : K) ∈ normGroupSet r M := hgroup hzSource
    have hoddz : Odd (ordUnit K a + ordUnit K z) := by
      simpa only [z, ordUnit_weightIdealGenerator] using hodd
    have hbound := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
      a z hb hzTarget hoddz
    simpa only [z, ordUnit_weightIdealGenerator] using hbound

namespace JordanDecomposition

variable {t : Nat} (J : JordanDecomposition q L t)

/-- The canonical generator of the intrinsic fundamental weight. -/
noncomputable def fundamentalWeightGenerator (i : Fin t) : Kˣ :=
  weightIdealGenerator q (J.fundamentalLattice i)

@[simp]
theorem fundamentalWeightGenerator_order (i : Fin t) :
    ordUnit K (J.fundamentalWeightGenerator i) =
      J.fundamentalWeightOrder i := by
  simp [fundamentalWeightGenerator, fundamentalWeightOrder]

theorem fundamentalWeightGenerator_principalIdeal (i : Fin t) :
    principalIdeal (K := K) ((J.fundamentalWeightGenerator i : Kˣ) : K) =
      J.fundamentalWeightIdeal i := by
  exact principalIdeal_weightIdealGenerator q (J.fundamentalLattice i)

theorem fundamentalWeightGenerator_mem (i : Fin t) :
    ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      J.fundamentalNormGroup i := by
  exact weightIdealGenerator_mem_normGroupSet q (J.fundamentalLattice i)
    (J.fundamentalNormGenerator i) (J.fundamentalNormGenerator_spec i)

/-- Every displayed Jordan component maps into the intrinsic scale layer at
its own scale. -/
theorem componentNormGroup_subset_fundamental (i : Fin t) :
    normGroupSet (J.component i).space (J.component i).lattice ⊆
      J.fundamentalNormGroup i := by
  let D := J.scaleTruncationDecomposition (J.fundamentalScaleOrder i)
  have hsubset := D.component_normGroupSet_subset i
  have hcomponent : D.component i = J.component i := by
    simpa only [D, fundamentalScaleOrder] using
      J.scaleTruncationDecomposition_component_self i
  rw [hcomponent] at hsubset
  exact hsubset

/-- The norm ideal of a displayed component is contained in the norm ideal
of its intrinsic scale layer. -/
theorem componentNormIdeal_le_fundamental (i : Fin t) :
    normIdeal (J.component i).space (J.component i).lattice ≤
      normIdeal q (J.fundamentalLattice i) := by
  let D := J.scaleTruncationDecomposition (J.fundamentalScaleOrder i)
  have hcomponent : D.component i = J.component i := by
    simpa only [D, fundamentalScaleOrder] using
      J.scaleTruncationDecomposition_component_self i
  have hcomponentIdeal :
      normIdeal (D.component i).space (D.component i).lattice ≤
        normIdeal q (scaleTruncation q L (J.fundamentalScaleOrder i)) := by
    rw [D.normIdeal_eq_iSup_component]
    exact le_iSup
      (fun j : Fin t ↦ normIdeal (D.component j).space
        (D.component j).lattice) i
  rw [hcomponent] at hcomponentIdeal
  exact hcomponentIdeal

/-- If the intrinsic norm generator occurs in the component norm group, it
is also a norm generator of that component. -/
theorem fundamentalNormGenerator_isComponentNormGenerator
    (i : Fin t)
    (hmem : ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet (J.component i).space (J.component i).lattice) :
    IsNormGeneratorValue (J.component i).space (J.component i).lattice
      (J.fundamentalNormGenerator i) := by
  have hcomponentIdeal := J.componentNormIdeal_le_fundamental i
  have hcomponentIdeal' :
      normIdeal (J.component i).space (J.component i).lattice ≤
        principalIdeal (K := K) ((J.fundamentalNormGenerator i : Kˣ) : K) :=
    hcomponentIdeal.trans_eq (J.fundamentalNormGenerator_spec i).2
  refine ⟨hmem, le_antisymm hcomponentIdeal' ?_⟩
  rw [principalIdeal, Submodule.span_singleton_le_iff_mem]
  exact normGroupSet_subset_normIdeal _ _ hmem

/-- The component and its intrinsic scale layer have the same doubled scale
ideal. -/
theorem componentTwoScaleIdeal_eq_fundamental (i : Fin t) :
    twoScaleIdeal (J.component i).space (J.component i).lattice =
      twoScaleIdeal q (J.fundamentalLattice i) := by
  unfold twoScaleIdeal
  congr 1
  rw [J.scaleIdeal_eq i]
  unfold fundamentalLattice fundamentalScaleOrder
  rw [J.scaleIdeal_scaleTruncation_at_component,
    principalIdeal_eq_powerIdeal]

/-- O'Meara 93:21's local conclusion: after the two selected fundamental
generators have been moved into one component, that component is saturated.
-/
theorem componentNormGroup_eq_fundamental_of_generators_mem
    (i : Fin t)
    (hnorm : ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
      normGroupSet (J.component i).space (J.component i).lattice)
    (hweight : ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
      normGroupSet (J.component i).space (J.component i).lattice) :
    normGroupSet (J.component i).space (J.component i).lattice =
      J.fundamentalNormGroup i := by
  let a := J.fundamentalNormGenerator i
  have haComponent := J.fundamentalNormGenerator_isComponentNormGenerator i hnorm
  have haFundamental := J.fundamentalNormGenerator_spec i
  have hsubset := J.componentNormGroup_subset_fundamental i
  have htwo := J.componentTwoScaleIdeal_eq_fundamental i
  have hweightLe :
      weightIdeal (J.component i).space (J.component i).lattice ≤
        J.fundamentalWeightIdeal i := by
    exact weightIdeal_mono_of_normGroupSet_subset a haComponent haFundamental
      htwo hsubset
  have hfundamentalWeightLe :
      J.fundamentalWeightIdeal i ≤
        weightIdeal (J.component i).space (J.component i).lattice := by
    rcases weightIdeal_eq_twoScale_or_odd a haFundamental with hterminal | hodd
    · change weightIdeal q (J.fundamentalLattice i) ≤
        weightIdeal (J.component i).space (J.component i).lattice
      rw [hterminal, ← htwo]
      exact twoScaleIdeal_le_weightIdeal _ _
    · rw [← J.fundamentalWeightGenerator_principalIdeal i,
        principalIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
        powerIdeal_le_iff]
      have hodd' : Odd (ordUnit K a + J.fundamentalWeightOrder i) := by
        exact hodd
      have hbound := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
        a (J.fundamentalWeightGenerator i) haComponent hweight (by
          simpa only [J.fundamentalWeightGenerator_order i] using hodd')
      simpa only [J.fundamentalWeightGenerator_order i] using hbound
  have hweightEq :
      weightIdeal (J.component i).space (J.component i).lattice =
        J.fundamentalWeightIdeal i :=
    le_antisymm hweightLe hfundamentalWeightLe
  have hweightEq' :
      weightIdeal (J.component i).space (J.component i).lattice =
        weightIdeal q (J.fundamentalLattice i) := hweightEq
  change normGroupSet (J.component i).space (J.component i).lattice =
    normGroupSet q (J.fundamentalLattice i)
  rw [normGroupSet_eq_integralSquareCoset_weightIdeal a haComponent,
    normGroupSet_eq_integralSquareCoset_weightIdeal a haFundamental,
    hweightEq']

/-- Componentwise generator absorption is exactly enough to prove that a
Jordan splitting is saturated. -/
theorem isSaturated_of_fundamentalGenerators_mem
    (hnorm : ∀ i : Fin t,
      ((J.fundamentalNormGenerator i : Kˣ) : K) ∈
        normGroupSet (J.component i).space (J.component i).lattice)
    (hweight : ∀ i : Fin t,
      ((J.fundamentalWeightGenerator i : Kˣ) : K) ∈
        normGroupSet (J.component i).space (J.component i).lattice) :
    J.IsSaturated := by
  intro i
  exact J.componentNormGroup_eq_fundamental_of_generators_mem i
    (hnorm i) (hweight i)

end JordanDecomposition

end Lattice

end Bong
