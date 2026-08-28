/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma51
import Bong.Bong.JordanEffectiveNorm
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.NormIdealOrder
import Bong.Lattice.RankOneNormScale
import Bong.Lattice.OmearaRawJordan
import Bong.Lattice.OrthogonalDecompositionCons

/-!
# Beli (2019), Section 5: the almost Jordan decompositions

Lemma 5.1 gives splittings `N = J ⊥ K` and `M = J' ⊥ K`.  Section 5 then
chooses one Jordan decomposition of the common complement `K` and inserts
`J` or `J'` at the appropriate scale.  The displayed decompositions are
called "almost Jordan" because an inserted block can have the same scale as
an adjacent component and must then be amalgamated.

This file carries out exactly that construction.  The common complement is
decomposed once by O'Meara's constructive raw Jordan theorem.  Each selected
block is prepended, the finite components are sorted by scale, and equal
scales are amalgamated by `WeakJordanDecomposition.jordanWitness`.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Beli2019Lemma51Data

/-- The common orthogonal complement in Lemma 5.1. -/
noncomputable def complement (D : Beli2019Lemma51Data q M N) :
    QuadraticSublattice q :=
  D.input.smallSplitting.component 1

/-- O'Meara's unamalgamated Jordan decomposition of the common complement.
The same object is used on the small and large sides. -/
noncomputable def complementRawJordan
    (D : Beli2019Lemma51Data q M N) :
    RawJordanDecomposition D.complement.space D.complement.lattice
      (omearaJordanTree D.complement.space D.complement.lattice).blockCount :=
  omearaRawJordanDecomposition D.complement.space D.complement.lattice

/-- The common complement as a weak Jordan decomposition. -/
noncomputable def complementWeakJordan
    (D : Beli2019Lemma51Data q M N) :
    WeakJordanDecomposition D.complement.space D.complement.lattice
      (omearaJordanTree D.complement.space D.complement.lattice).blockCount :=
  WeakJordanDecomposition.ofRaw D.complementRawJordan

/-- Equal scales in the raw decomposition of the complement are amalgamated
while retaining both strictness and the parity of every improper modular
component. -/
noncomputable def complementStrictParityWitness
    (D : Beli2019Lemma51Data q M N) :
    Σ s : Nat, {S : WeakJordanDecomposition
        D.complement.space D.complement.lattice s //
      StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i)) ∧
        S.HasImproperEvenRank} :=
  D.complementWeakJordan.strictParityWitness
    (WeakJordanDecomposition.hasImproperEvenRank_ofRaw
      D.complementRawJordan)

/-- The strict-scale part of the parity-preserving witness. -/
noncomputable def complementStrictWitness
    (D : Beli2019Lemma51Data q M N) :
    Σ s : Nat, {S : WeakJordanDecomposition
        D.complement.space D.complement.lattice s //
      StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i))} :=
  ⟨D.complementStrictParityWitness.1,
    ⟨D.complementStrictParityWitness.2.1,
      D.complementStrictParityWitness.2.2.1⟩⟩

/-- The chosen number of strict-scale components of the common complement. -/
noncomputable def complementComponentCount
    (D : Beli2019Lemma51Data q M N) : Nat :=
  D.complementStrictWitness.1

/-- The common complement with strictly increasing modular scales and
positive component ranks. -/
noncomputable def complementStrictWeak
    (D : Beli2019Lemma51Data q M N) :
    WeakJordanDecomposition D.complement.space D.complement.lattice
      D.complementComponentCount :=
  D.complementStrictWitness.2.1

/-- The complement scales are strictly increasing. -/
theorem complementStrictWeak_scaleOrder_strict
    (D : Beli2019Lemma51Data q M N) :
    StrictMono (fun i ↦
      ordUnit K (D.complementStrictWeak.scaleGenerator i)) :=
  D.complementStrictWitness.2.2

/-- Every improper strict component of the common complement has even
rank. -/
theorem complementStrictWeak_hasImproperEvenRank
    (D : Beli2019Lemma51Data q M N) :
    D.complementStrictWeak.HasImproperEvenRank := by
  exact D.complementStrictParityWitness.2.2.2

/-- The corresponding genuine Jordan decomposition of the common
complement. -/
noncomputable def complementJordan
    (D : Beli2019Lemma51Data q M N) :
    JordanDecomposition D.complement.space D.complement.lattice
      D.complementComponentCount :=
  D.complementStrictWeak.toJordan
    D.complementStrictWeak_scaleOrder_strict

/-- The unsorted modular decomposition `J ⊥ K₁ ⊥ ... ⊥ Kₜ` of the smaller
lattice. -/
noncomputable def smallModularDecomposition
    (D : Beli2019Lemma51Data q M N) :
    ModularDecomposition q N
      (D.complementComponentCount + 1) := by
  let W := D.complementStrictWeak
  let P := D.input.smallSplitting.prependNested W.toOrthogonalDecomposition
  exact {
    toOrthogonalDecomposition := P
    scaleGenerator := Fin.cases D.input.block.scaleGenerator W.scaleGenerator
    modular := by
      intro i
      cases i using Fin.cases with
      | zero => exact D.small_modular
      | succ i =>
          change IsModular
            (D.complement.liftNested (W.component i)).space
            (D.complement.liftNested (W.component i)).lattice _
          exact QuadraticSublattice.IsModular.liftNested D.complement _
            (W.modular i)
    component_finrank_pos := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change 0 < finrank K D.input.block.component.carrier
          rcases D.rank_one_or_two with h | h <;> omega
      | succ i =>
          change 0 < finrank K
            (D.complement.liftNested (W.component i)).carrier
          rw [D.complement.finrank_liftNested]
          exact W.component_finrank_pos i
  }

/-- The unsorted modular decomposition `J' ⊥ K₁ ⊥ ... ⊥ Kₜ` of the larger
lattice. -/
noncomputable def largeModularDecomposition
    (D : Beli2019Lemma51Data q M N) :
    ModularDecomposition q M
      (D.complementComponentCount + 1) := by
  let W := D.complementStrictWeak
  let P := D.input.largeSplitting.prependNestedOfEq D.complement
    D.common_complement W.toOrthogonalDecomposition
  exact {
    toOrthogonalDecomposition := P
    scaleGenerator :=
      Fin.cases D.input.block.enlargedScaleGenerator W.scaleGenerator
    modular := by
      intro i
      cases i using Fin.cases with
      | zero => exact D.large_modular
      | succ i =>
          change IsModular
            (D.complement.liftNested (W.component i)).space
            (D.complement.liftNested (W.component i)).lattice _
          exact QuadraticSublattice.IsModular.liftNested D.complement _
            (W.modular i)
    component_finrank_pos := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change 0 < finrank K D.input.enlargedComponent.carrier
          change 0 < finrank K D.input.block.component.carrier
          rcases D.rank_one_or_two with h | h <;> omega
      | succ i =>
          change 0 < finrank K
            (D.complement.liftNested (W.component i)).carrier
          rw [D.complement.finrank_liftNested]
          exact W.component_finrank_pos i
  }

/-- The scale sort used on the smaller side. -/
noncomputable def smallSort (D : Beli2019Lemma51Data q M N) :
    ModularDecomposition.SortedReindex D.smallModularDecomposition :=
  D.smallModularDecomposition.sortedReindex

/-- The tie-breaking permutation used on the larger side: the enlarged
selected block follows a common-complement block of the same scale. -/
noncomputable def largeTie (D : Beli2019Lemma51Data q M N) :
    Fin (D.complementComponentCount + 1) ≃
      Fin (D.complementComponentCount + 1) :=
  ModularDecomposition.distinguishedLastTie D.complementComponentCount

/-- The scale sort used on the larger side. -/
noncomputable def largeSort (D : Beli2019Lemma51Data q M N) :
    ModularDecomposition.SortedReindex D.largeModularDecomposition :=
  D.largeModularDecomposition.sortedReindexBy D.largeTie

/-- The position of the selected block in the smaller almost Jordan
decomposition. -/
noncomputable def smallSelectedPosition
    (D : Beli2019Lemma51Data q M N) :
    Fin (D.complementComponentCount + 1) :=
  D.smallSort.equiv.symm 0

/-- The position of the enlarged selected block in the larger almost
Jordan decomposition. -/
noncomputable def largeSelectedPosition
    (D : Beli2019Lemma51Data q M N) :
    Fin (D.complementComponentCount + 1) :=
  D.largeSort.equiv.symm 0

/-- The position of a common-complement component on the smaller side. -/
noncomputable def smallCommonPosition
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    Fin (D.complementComponentCount + 1) :=
  D.smallSort.equiv.symm i.succ

/-- The position of a common-complement component on the larger side. -/
noncomputable def largeCommonPosition
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    Fin (D.complementComponentCount + 1) :=
  D.largeSort.equiv.symm i.succ

/-- The scale-sorted almost Jordan decomposition of the smaller lattice. -/
noncomputable def smallAlmostJordan
    (D : Beli2019Lemma51Data q M N) :
    WeakJordanDecomposition q N
      (D.complementComponentCount + 1) :=
  D.smallModularDecomposition.sortedWeakJordan

/-- The scale-sorted almost Jordan decomposition of the larger lattice. -/
noncomputable def largeAlmostJordan
    (D : Beli2019Lemma51Data q M N) :
    WeakJordanDecomposition q M
      (D.complementComponentCount + 1) :=
  D.largeModularDecomposition.sortedWeakJordanBy
    D.largeTie

@[simp]
theorem smallAlmostJordan_component_selected
    (D : Beli2019Lemma51Data q M N) :
    D.smallAlmostJordan.component D.smallSelectedPosition =
      D.input.block.component := by
  rw [show D.smallSelectedPosition =
      D.smallModularDecomposition.sortedReindex.equiv.symm 0 by rfl]
  change D.smallModularDecomposition.sortedWeakJordan.component
      (D.smallModularDecomposition.sortedReindex.equiv.symm 0) = _
  rw [ModularDecomposition.sortedWeakJordan_component_at_old]
  rfl

@[simp]
theorem largeAlmostJordan_component_selected
    (D : Beli2019Lemma51Data q M N) :
    D.largeAlmostJordan.component D.largeSelectedPosition =
      D.input.enlargedComponent := by
  rw [show D.largeSelectedPosition =
      (D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm 0
      by rfl]
  change (D.largeModularDecomposition.sortedWeakJordanBy D.largeTie).component
      ((D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        0) = _
  rw [ModularDecomposition.sortedWeakJordanBy_component_at_old]
  rfl

@[simp]
theorem smallAlmostJordan_scaleGenerator_selected
    (D : Beli2019Lemma51Data q M N) :
    D.smallAlmostJordan.scaleGenerator D.smallSelectedPosition =
      D.input.block.scaleGenerator := by
  rw [show D.smallSelectedPosition =
      D.smallModularDecomposition.sortedReindex.equiv.symm 0 by rfl]
  change D.smallModularDecomposition.sortedWeakJordan.scaleGenerator
      (D.smallModularDecomposition.sortedReindex.equiv.symm 0) = _
  rw [ModularDecomposition.sortedWeakJordan_scaleGenerator_at_old]
  rfl

@[simp]
theorem largeAlmostJordan_scaleGenerator_selected
    (D : Beli2019Lemma51Data q M N) :
    D.largeAlmostJordan.scaleGenerator D.largeSelectedPosition =
      D.input.block.enlargedScaleGenerator := by
  rw [show D.largeSelectedPosition =
      (D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm 0
      by rfl]
  change (D.largeModularDecomposition.sortedWeakJordanBy D.largeTie).scaleGenerator
      ((D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        0) = _
  rw [ModularDecomposition.sortedWeakJordanBy_scaleGenerator_at_old]
  rfl

@[simp]
theorem smallAlmostJordan_component_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallAlmostJordan.component (D.smallCommonPosition i) =
      D.complement.liftNested (D.complementStrictWeak.component i) := by
  rw [show D.smallCommonPosition i =
      D.smallModularDecomposition.sortedReindex.equiv.symm i.succ by rfl]
  change D.smallModularDecomposition.sortedWeakJordan.component
      (D.smallModularDecomposition.sortedReindex.equiv.symm i.succ) = _
  rw [ModularDecomposition.sortedWeakJordan_component_at_old]
  rfl

@[simp]
theorem largeAlmostJordan_component_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeAlmostJordan.component (D.largeCommonPosition i) =
      D.complement.liftNested (D.complementStrictWeak.component i) := by
  rw [show D.largeCommonPosition i =
      (D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        i.succ by rfl]
  change (D.largeModularDecomposition.sortedWeakJordanBy D.largeTie).component
      ((D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        i.succ) = _
  rw [ModularDecomposition.sortedWeakJordanBy_component_at_old]
  rfl

@[simp]
theorem smallAlmostJordan_scaleGenerator_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallAlmostJordan.scaleGenerator (D.smallCommonPosition i) =
      D.complementStrictWeak.scaleGenerator i := by
  rw [show D.smallCommonPosition i =
      D.smallModularDecomposition.sortedReindex.equiv.symm i.succ by rfl]
  change D.smallModularDecomposition.sortedWeakJordan.scaleGenerator
      (D.smallModularDecomposition.sortedReindex.equiv.symm i.succ) = _
  rw [ModularDecomposition.sortedWeakJordan_scaleGenerator_at_old]
  rfl

@[simp]
theorem largeAlmostJordan_scaleGenerator_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeAlmostJordan.scaleGenerator (D.largeCommonPosition i) =
      D.complementStrictWeak.scaleGenerator i := by
  rw [show D.largeCommonPosition i =
      (D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        i.succ by rfl]
  change (D.largeModularDecomposition.sortedWeakJordanBy D.largeTie).scaleGenerator
      ((D.largeModularDecomposition.sortedReindexBy D.largeTie).equiv.symm
        i.succ) = _
  rw [ModularDecomposition.sortedWeakJordanBy_scaleGenerator_at_old]
  rfl

@[simp]
theorem smallAlmostJordan_finrank_selected
    (D : Beli2019Lemma51Data q M N) :
    finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier =
      finrank K D.input.block.component.carrier := by
  rw [D.smallAlmostJordan_component_selected]

@[simp]
theorem largeAlmostJordan_finrank_selected
    (D : Beli2019Lemma51Data q M N) :
    finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier =
      finrank K D.input.block.component.carrier := by
  rw [D.largeAlmostJordan_component_selected]
  rfl

@[simp]
theorem smallAlmostJordan_finrank_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    finrank K
        (D.smallAlmostJordan.component (D.smallCommonPosition i)).carrier =
      finrank K (D.complementStrictWeak.component i).carrier := by
  rw [D.smallAlmostJordan_component_common,
    D.complement.finrank_liftNested]

@[simp]
theorem largeAlmostJordan_finrank_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    finrank K
        (D.largeAlmostJordan.component (D.largeCommonPosition i)).carrier =
      finrank K (D.complementStrictWeak.component i).carrier := by
  rw [D.largeAlmostJordan_component_common,
    D.complement.finrank_liftNested]

/-- The chosen norm generators on the two copies of a common-complement
component have the same order.  The choices need not be definitionally the
same; equality follows from their common principal norm ideal. -/
theorem common_normOrder_eq
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    ordUnit K (D.smallAlmostJordan.normGeneratorUnit
        (D.smallCommonPosition i)) =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        (D.largeCommonPosition i)) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    principalIdeal (K := K)
        (D.smallAlmostJordan.normGeneratorUnit
          (D.smallCommonPosition i) : K) =
        normIdeal
          (D.smallAlmostJordan.component
            (D.smallCommonPosition i)).space
          (D.smallAlmostJordan.component
            (D.smallCommonPosition i)).lattice :=
      (D.smallAlmostJordan.normIdeal_eq_normGeneratorUnit
        (D.smallCommonPosition i)).symm
    _ = normIdeal
          (D.complement.liftNested
            (D.complementStrictWeak.component i)).space
          (D.complement.liftNested
            (D.complementStrictWeak.component i)).lattice := by
      rw [D.smallAlmostJordan_component_common]
    _ = normIdeal
          (D.largeAlmostJordan.component
            (D.largeCommonPosition i)).space
          (D.largeAlmostJordan.component
            (D.largeCommonPosition i)).lattice := by
      rw [D.largeAlmostJordan_component_common]
    _ = principalIdeal (K := K)
        (D.largeAlmostJordan.normGeneratorUnit
          (D.largeCommonPosition i) : K) :=
      D.largeAlmostJordan.normIdeal_eq_normGeneratorUnit
        (D.largeCommonPosition i)

/-- The norm-generator order of a common component is unchanged when the
component is lifted from the common orthogonal complement and inserted into
the larger almost-Jordan decomposition. -/
theorem largeAlmostJordan_normOrder_common_eq_complement
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        (D.largeCommonPosition i)) =
      ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    principalIdeal (K := K)
        (D.largeAlmostJordan.normGeneratorUnit
          (D.largeCommonPosition i) : K) =
        normIdeal
          (D.largeAlmostJordan.component
            (D.largeCommonPosition i)).space
          (D.largeAlmostJordan.component
            (D.largeCommonPosition i)).lattice :=
      (D.largeAlmostJordan.normIdeal_eq_normGeneratorUnit
        (D.largeCommonPosition i)).symm
    _ = normIdeal
          (D.complement.liftNested
            (D.complementStrictWeak.component i)).space
          (D.complement.liftNested
            (D.complementStrictWeak.component i)).lattice := by
      rw [D.largeAlmostJordan_component_common]
    _ = normIdeal
          (D.complementStrictWeak.component i).space
          (D.complementStrictWeak.component i).lattice :=
      normIdeal_map_isometry
        (D.complement.liftNestedIsometry
          (D.complementStrictWeak.component i)).toQuadraticSpaceIsometry
        (D.complementStrictWeak.component i).lattice
    _ = principalIdeal (K := K)
          (D.complementStrictWeak.normGeneratorUnit i : K) :=
      D.complementStrictWeak.normIdeal_eq_normGeneratorUnit i

/-- The analogous norm-order transport on the smaller side. -/
theorem smallAlmostJordan_normOrder_common_eq_complement
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    ordUnit K (D.smallAlmostJordan.normGeneratorUnit
        (D.smallCommonPosition i)) =
      ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
  rw [D.common_normOrder_eq,
    D.largeAlmostJordan_normOrder_common_eq_complement]

/-- The selected component has rank one with a two-step scale drop, or rank
two with a one-step scale drop. -/
theorem selectedRank_and_scaleOrder
    (D : Beli2019Lemma51Data q M N) :
    (finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 1 ∧
        ordUnit K (D.largeAlmostJordan.scaleGenerator
            D.largeSelectedPosition) =
          ordUnit K (D.smallAlmostJordan.scaleGenerator
            D.smallSelectedPosition) - 2) ∨
      (finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 2 ∧
        ordUnit K (D.largeAlmostJordan.scaleGenerator
            D.largeSelectedPosition) =
          ordUnit K (D.smallAlmostJordan.scaleGenerator
            D.smallSelectedPosition) - 1) := by
  simpa only [smallAlmostJordan_finrank_selected,
    smallAlmostJordan_scaleGenerator_selected,
    largeAlmostJordan_scaleGenerator_selected] using
      D.input.block.componentRank_and_enlargedScaleOrder

/-- The weak-Jordan norm unit at the selected small block generates that
block's norm ideal. -/
theorem smallSelected_normIdeal_eq
    (D : Beli2019Lemma51Data q M N) :
    normIdeal D.input.block.component.space
        D.input.block.component.lattice =
      principalIdeal (K := K)
        (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition : K) := by
  have h := D.smallAlmostJordan.normIdeal_eq_normGeneratorUnit
    D.smallSelectedPosition
  rw [D.smallAlmostJordan_component_selected] at h
  exact h

/-- The weak-Jordan norm unit at the selected large block generates the
enlarged block's norm ideal. -/
theorem largeSelected_normIdeal_eq
    (D : Beli2019Lemma51Data q M N) :
    normIdeal D.input.enlargedComponent.space
        D.input.enlargedComponent.lattice =
      principalIdeal (K := K)
        (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition : K) := by
  have h := D.largeAlmostJordan.normIdeal_eq_normGeneratorUnit
    D.largeSelectedPosition
  rw [D.largeAlmostJordan_component_selected] at h
  exact h

/-- In the unary case, the selected small component has equal norm and
scale orders. -/
theorem smallSelected_normOrder_eq_scaleOrder_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 1) :
    ordUnit K (D.smallAlmostJordan.normGeneratorUnit
        D.smallSelectedPosition) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator
        D.smallSelectedPosition) := by
  have hfin' : finrank K D.input.block.component.carrier = 1 := by
    simpa only [D.smallAlmostJordan_finrank_selected] using hfin
  simpa only [D.smallAlmostJordan_scaleGenerator_selected] using
    (ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      D.input.block.component.space D.input.block.component.lattice
      D.input.block.scaleGenerator
      (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition)
      hfin' D.small_modular D.smallSelected_normIdeal_eq)

/-- In the unary case, the enlarged selected component also has equal norm
and scale orders. -/
theorem largeSelected_normOrder_eq_scaleOrder_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier = 1) :
    ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator
        D.largeSelectedPosition) := by
  have hfin' : finrank K D.input.block.component.carrier = 1 := by
    simpa only [D.largeAlmostJordan_finrank_selected] using hfin
  simpa only [D.largeAlmostJordan_scaleGenerator_selected] using
    (ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      D.input.enlargedComponent.space D.input.enlargedComponent.lattice
      D.input.block.enlargedScaleGenerator
      (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
      hfin' D.large_modular D.largeSelected_normIdeal_eq)

/-- Enlarging the selected block can only lower its norm order. -/
theorem largeSelected_normOrder_le_smallSelected
    (D : Beli2019Lemma51Data q M N) :
    ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) ≤
      ordUnit K (D.smallAlmostJordan.normGeneratorUnit
        D.smallSelectedPosition) := by
  exact ordUnit_normIdealGenerator_antitone
    D.small_le_large
    (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition)
    (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
    D.smallSelected_normIdeal_eq D.largeSelected_normIdeal_eq

/-- Multiplication by the uniformizer carries the enlarged block into the
small block, so their norm orders differ by at most two. -/
theorem smallSelected_normOrder_le_largeSelected_add_two
    (D : Beli2019Lemma51Data q M N) :
    ordUnit K (D.smallAlmostJordan.normGeneratorUnit
        D.smallSelectedPosition) ≤
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) + 2 := by
  have hpos : 0 < finrank K D.input.block.component.carrier := by
    rcases D.rank_one_or_two with h | h <;> omega
  have hbound :=
    ordUnit_normIdealGenerator_le_add_two_mul_of_rescale_le
      (q := D.input.block.component.space)
      (L := D.input.block.component.lattice)
      (M := D.input.enlargedComponent.lattice)
      (uniformizerUnit K) D.uniformizer_large_le_small hpos
      (D.smallAlmostJordan.normGeneratorUnit D.smallSelectedPosition)
      (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
      D.smallSelected_normIdeal_eq D.largeSelected_normIdeal_eq
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [hpi] at hbound
  omega

/-- The exact two-sided norm-order bound stated in Section 5.4. -/
theorem selected_normOrder_bounds
    (D : Beli2019Lemma51Data q M N) :
    ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) ≤
        ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition) ∧
      ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          D.smallSelectedPosition) ≤
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) + 2 :=
  ⟨D.largeSelected_normOrder_le_smallSelected,
    D.smallSelected_normOrder_le_largeSelected_add_two⟩

/-- Common-complement positions retain their strict scale order on the
smaller side. -/
theorem smallCommonScaleOrder_strict
    (D : Beli2019Lemma51Data q M N) :
    StrictMono (fun i : Fin D.complementComponentCount ↦
      ordUnit K (D.smallAlmostJordan.scaleGenerator
        (D.smallCommonPosition i))) := by
  simpa only [smallAlmostJordan_scaleGenerator_common] using
    D.complementStrictWeak_scaleOrder_strict

/-- Common-complement positions retain their strict scale order on the
larger side. -/
theorem largeCommonScaleOrder_strict
    (D : Beli2019Lemma51Data q M N) :
    StrictMono (fun i : Fin D.complementComponentCount ↦
      ordUnit K (D.largeAlmostJordan.scaleGenerator
        (D.largeCommonPosition i))) := by
  simpa only [largeAlmostJordan_scaleGenerator_common] using
    D.complementStrictWeak_scaleOrder_strict

theorem smallSelectedPosition_ne_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallSelectedPosition ≠ D.smallCommonPosition i := by
  intro h
  have h' := congrArg D.smallSort.equiv h
  simp [smallSelectedPosition, smallCommonPosition] at h'
  exact (Fin.succ_ne_zero i) h'.symm

theorem largeSelectedPosition_ne_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeSelectedPosition ≠ D.largeCommonPosition i := by
  intro h
  have h' := congrArg D.largeSort.equiv h
  simp [largeSelectedPosition, largeCommonPosition] at h'
  exact (Fin.succ_ne_zero i) h'.symm

/-- On the smaller side an equal-scale common component follows the selected
block, as in the displayed almost Jordan decomposition of the paper. -/
theorem smallSelectedPosition_lt_common_of_scaleOrder_eq
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K D.input.block.scaleGenerator =
      ordUnit K (D.complementStrictWeak.scaleGenerator i)) :
    D.smallSelectedPosition < D.smallCommonPosition i := by
  have hscale' : ordUnit K
      (D.smallModularDecomposition.scaleGenerator 0) =
      ordUnit K (D.smallModularDecomposition.scaleGenerator i.succ) := by
    exact hscale
  apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff_of_scaleOrder_eq
    D.smallModularDecomposition D.smallSort
    (i := (0 : Fin (D.complementComponentCount + 1)))
    (j := i.succ) hscale').2
  change (0 : Nat) < i.val + 1
  omega

/-- On the larger side an equal-scale common component precedes the enlarged
selected block, as in the displayed almost Jordan decomposition of the
paper. -/
theorem largeCommonPosition_lt_selected_of_scaleOrder_eq
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator i) =
      ordUnit K D.input.block.enlargedScaleGenerator) :
    D.largeCommonPosition i < D.largeSelectedPosition := by
  have hscale' : ordUnit K
      (D.largeModularDecomposition.scaleGenerator i.succ) =
      ordUnit K (D.largeModularDecomposition.scaleGenerator 0) := by
    exact hscale
  apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff_of_scaleOrder_eq
    D.largeModularDecomposition D.largeSort
    (i := i.succ)
    (j := (0 : Fin (D.complementComponentCount + 1))) hscale').2
  change i.val < D.complementComponentCount
  exact i.isLt

/-- Two distinct equal-scale positions on the smaller side must include the
selected block.  Strictness of the common complement rules out every other
collision. -/
theorem smallEqualScale_involves_selected
    (D : Beli2019Lemma51Data q M N)
    {i j : Fin (D.complementComponentCount + 1)} (hij : i ≠ j)
    (heq : ordUnit K (D.smallAlmostJordan.scaleGenerator i) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator j)) :
    i = D.smallSelectedPosition ∨ j = D.smallSelectedPosition := by
  have hstrict : StrictMono (fun k : Fin D.complementComponentCount ↦
      ordUnit K (D.smallModularDecomposition.scaleGenerator k.succ)) := by
    exact D.complementStrictWeak_scaleOrder_strict
  have heq' : ordUnit K
      (D.smallModularDecomposition.scaleGenerator (D.smallSort.equiv i)) =
      ordUnit K
        (D.smallModularDecomposition.scaleGenerator (D.smallSort.equiv j)) := by
    exact heq
  simpa only [smallSelectedPosition] using
    (ModularDecomposition.SortedReindex.equalScale_involves_oldZero
      D.smallModularDecomposition D.smallSort hstrict hij heq')

/-- Two distinct equal-scale positions on the larger side must include the
enlarged selected block. -/
theorem largeEqualScale_involves_selected
    (D : Beli2019Lemma51Data q M N)
    {i j : Fin (D.complementComponentCount + 1)} (hij : i ≠ j)
    (heq : ordUnit K (D.largeAlmostJordan.scaleGenerator i) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator j)) :
    i = D.largeSelectedPosition ∨ j = D.largeSelectedPosition := by
  have hstrict : StrictMono (fun k : Fin D.complementComponentCount ↦
      ordUnit K (D.largeModularDecomposition.scaleGenerator k.succ)) := by
    exact D.complementStrictWeak_scaleOrder_strict
  have heq' : ordUnit K
      (D.largeModularDecomposition.scaleGenerator (D.largeSort.equiv i)) =
      ordUnit K
        (D.largeModularDecomposition.scaleGenerator (D.largeSort.equiv j)) := by
    exact heq
  simpa only [largeSelectedPosition] using
    (ModularDecomposition.SortedReindex.equalScale_involves_oldZero
      D.largeModularDecomposition D.largeSort hstrict hij heq')

theorem smallPosition_eq_selected_or_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin (D.complementComponentCount + 1)) :
    i = D.smallSelectedPosition ∨
      ∃ j : Fin D.complementComponentCount,
        i = D.smallCommonPosition j := by
  simpa only [smallSelectedPosition, smallCommonPosition] using
    (ModularDecomposition.SortedReindex.position_eq_oldZero_or_succ
      D.smallModularDecomposition D.smallSort i)

theorem largePosition_eq_selected_or_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin (D.complementComponentCount + 1)) :
    i = D.largeSelectedPosition ∨
      ∃ j : Fin D.complementComponentCount,
        i = D.largeCommonPosition j := by
  simpa only [largeSelectedPosition, largeCommonPosition] using
    (ModularDecomposition.SortedReindex.position_eq_oldZero_or_succ
      D.largeModularDecomposition D.largeSort i)

/-- Sorting and inserting the selected block preserves the
improper-even-rank invariant on the smaller almost-Jordan decomposition. -/
theorem smallAlmostJordan_hasImproperEvenRank
    (D : Beli2019Lemma51Data q M N) :
    D.smallAlmostJordan.HasImproperEvenRank := by
  intro p hstrict
  rcases D.smallPosition_eq_selected_or_common p with
    hselected | ⟨i, hcommon⟩
  · subst p
    rcases D.rank_one_or_two with hOne | hTwo
    · have hOne' : finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 1 := by
        simpa only [D.smallAlmostJordan_finrank_selected] using hOne
      have hnorm := D.smallSelected_normOrder_eq_scaleOrder_of_rank_one hOne'
      omega
    · rw [D.smallAlmostJordan_finrank_selected, hTwo]
      exact even_two
  · subst p
    have hcomplement :
        ordUnit K (D.complementStrictWeak.scaleGenerator i) <
          ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
      simpa only [D.smallAlmostJordan_scaleGenerator_common,
        D.smallAlmostJordan_normOrder_common_eq_complement] using hstrict
    rw [D.smallAlmostJordan_finrank_common]
    exact D.complementStrictWeak_hasImproperEvenRank i hcomplement

/-- The analogous improper-even-rank invariant on the larger
almost-Jordan decomposition. -/
theorem largeAlmostJordan_hasImproperEvenRank
    (D : Beli2019Lemma51Data q M N) :
    D.largeAlmostJordan.HasImproperEvenRank := by
  intro p hstrict
  rcases D.largePosition_eq_selected_or_common p with
    hselected | ⟨i, hcommon⟩
  · subst p
    rcases D.rank_one_or_two with hOne | hTwo
    · have hOne' : finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier = 1 := by
        simpa only [D.largeAlmostJordan_finrank_selected] using hOne
      have hnorm := D.largeSelected_normOrder_eq_scaleOrder_of_rank_one hOne'
      omega
    · rw [D.largeAlmostJordan_finrank_selected, hTwo]
      exact even_two
  · subst p
    have hcomplement :
        ordUnit K (D.complementStrictWeak.scaleGenerator i) <
          ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
      simpa only [D.largeAlmostJordan_scaleGenerator_common,
        D.largeAlmostJordan_normOrder_common_eq_complement] using hstrict
    rw [D.largeAlmostJordan_finrank_common]
    exact D.complementStrictWeak_hasImproperEvenRank i hcomplement

/-- An equal-scale collision on the smaller side is an adjacent pair, with
the selected block first. -/
theorem smallCollision_adjacent
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K D.input.block.scaleGenerator =
      ordUnit K (D.complementStrictWeak.scaleGenerator i)) :
    ∃ k : Fin D.complementComponentCount,
      k.castSucc = D.smallSelectedPosition ∧
        k.succ = D.smallCommonPosition i := by
  have hlt := D.smallSelectedPosition_lt_common_of_scaleOrder_eq i hscale
  have heq : ordUnit K (D.smallAlmostJordan.scaleGenerator
        D.smallSelectedPosition) =
      ordUnit K (D.smallAlmostJordan.scaleGenerator
        (D.smallCommonPosition i)) := by
    simpa only [smallAlmostJordan_scaleGenerator_selected,
      smallAlmostJordan_scaleGenerator_common] using hscale
  have hval : (D.smallCommonPosition i).val =
      D.smallSelectedPosition.val + 1 := by
    by_contra hnot
    have hgap : D.smallSelectedPosition.val + 1 <
        (D.smallCommonPosition i).val := by
      omega
    let mid : Fin (D.complementComponentCount + 1) :=
      ⟨D.smallSelectedPosition.val + 1, by omega⟩
    have hleft : D.smallSelectedPosition ≤ mid := by
      change D.smallSelectedPosition.val ≤
        D.smallSelectedPosition.val + 1
      omega
    have hright : mid ≤ D.smallCommonPosition i := by
      change D.smallSelectedPosition.val + 1 ≤
        (D.smallCommonPosition i).val
      omega
    have hmonoLeft := D.smallAlmostJordan.scaleOrder_mono hleft
    have hmonoRight := D.smallAlmostJordan.scaleOrder_mono hright
    have hmidEq : ordUnit K (D.smallAlmostJordan.scaleGenerator mid) =
        ordUnit K (D.smallAlmostJordan.scaleGenerator
          (D.smallCommonPosition i)) := by
      apply le_antisymm hmonoRight
      exact heq.symm.le.trans hmonoLeft
    have hmidNe : mid ≠ D.smallCommonPosition i := by
      intro h
      have := congrArg Fin.val h
      dsimp [mid] at this
      omega
    rcases D.smallEqualScale_involves_selected hmidNe hmidEq with
      hmidSelected | hcommonSelected
    · have := congrArg Fin.val hmidSelected
      dsimp [mid] at this
      omega
    · exact (D.smallSelectedPosition_ne_common i)
        hcommonSelected.symm
  let k : Fin D.complementComponentCount :=
    ⟨D.smallSelectedPosition.val, by omega⟩
  refine ⟨k, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · apply Fin.ext
    exact hval.symm

/-- An equal-scale collision on the larger side is an adjacent pair, with
the common-complement block first and the enlarged selected block second. -/
theorem largeCollision_adjacent
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator i) =
      ordUnit K D.input.block.enlargedScaleGenerator) :
    ∃ k : Fin D.complementComponentCount,
      k.castSucc = D.largeCommonPosition i ∧
        k.succ = D.largeSelectedPosition := by
  have hlt := D.largeCommonPosition_lt_selected_of_scaleOrder_eq i hscale
  have heq : ordUnit K (D.largeAlmostJordan.scaleGenerator
        (D.largeCommonPosition i)) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator
        D.largeSelectedPosition) := by
    simpa only [largeAlmostJordan_scaleGenerator_selected,
      largeAlmostJordan_scaleGenerator_common] using hscale
  have hval : D.largeSelectedPosition.val =
      (D.largeCommonPosition i).val + 1 := by
    by_contra hnot
    have hgap : (D.largeCommonPosition i).val + 1 <
        D.largeSelectedPosition.val := by
      omega
    let mid : Fin (D.complementComponentCount + 1) :=
      ⟨(D.largeCommonPosition i).val + 1, by omega⟩
    have hleft : D.largeCommonPosition i ≤ mid := by
      change (D.largeCommonPosition i).val ≤
        (D.largeCommonPosition i).val + 1
      omega
    have hright : mid ≤ D.largeSelectedPosition := by
      change (D.largeCommonPosition i).val + 1 ≤
        D.largeSelectedPosition.val
      omega
    have hmonoLeft := D.largeAlmostJordan.scaleOrder_mono hleft
    have hmonoRight := D.largeAlmostJordan.scaleOrder_mono hright
    have hcommonMid : ordUnit K
          (D.largeAlmostJordan.scaleGenerator (D.largeCommonPosition i)) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator mid) := by
      apply le_antisymm hmonoLeft
      exact hmonoRight.trans heq.symm.le
    have hcommonNe : D.largeCommonPosition i ≠ mid := by
      intro h
      have := congrArg Fin.val h
      dsimp [mid] at this
      omega
    rcases D.largeEqualScale_involves_selected hcommonNe hcommonMid with
      hcommonSelected | hmidSelected
    · exact (D.largeSelectedPosition_ne_common i)
        hcommonSelected.symm
    · have := congrArg Fin.val hmidSelected
      dsimp [mid] at this
      omega
  let k : Fin D.complementComponentCount :=
    ⟨(D.largeCommonPosition i).val, by omega⟩
  refine ⟨k, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · apply Fin.ext
    exact hval.symm

/-- Once the small-side collision index is identified, it is the only
possible equality of distinct scale positions. -/
theorem smallOnlyScaleCollisionAt
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K D.input.block.scaleGenerator =
      ordUnit K (D.complementStrictWeak.scaleGenerator i))
    (k : Fin D.complementComponentCount)
    (hk : k.castSucc = D.smallSelectedPosition ∧
      k.succ = D.smallCommonPosition i) :
    WeakJordanDecomposition.OnlyScaleCollisionAt
      D.smallAlmostJordan k := by
  intro p q hpq heq
  have hpne : p ≠ q := Fin.ne_of_lt hpq
  rcases D.smallEqualScale_involves_selected hpne heq with
    hpSelected | hqSelected
  · subst p
    rcases D.smallPosition_eq_selected_or_common q with
      hqSelected | ⟨j, hqCommon⟩
    · subst q
      exact (lt_irrefl _ hpq).elim
    · subst q
      have heq' := heq
      simp only [smallAlmostJordan_scaleGenerator_selected,
        smallAlmostJordan_scaleGenerator_common] at heq'
      have hji : j = i :=
        D.complementStrictWeak_scaleOrder_strict.injective
          (heq'.symm.trans hscale)
      subst j
      exact ⟨hk.1.symm, hk.2.symm⟩
  · subst q
    rcases D.smallPosition_eq_selected_or_common p with
      hpSelected | ⟨j, hpCommon⟩
    · subst p
      exact (lt_irrefl _ hpq).elim
    · subst p
      have heq' := heq
      simp only [smallAlmostJordan_scaleGenerator_selected,
        smallAlmostJordan_scaleGenerator_common] at heq'
      have hreverse :=
        D.smallSelectedPosition_lt_common_of_scaleOrder_eq j heq'.symm
      exact (lt_asymm hpq hreverse).elim

/-- Once the large-side collision index is identified, it is the only
possible equality of distinct scale positions. -/
theorem largeOnlyScaleCollisionAt
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator i) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    (k : Fin D.complementComponentCount)
    (hk : k.castSucc = D.largeCommonPosition i ∧
      k.succ = D.largeSelectedPosition) :
    WeakJordanDecomposition.OnlyScaleCollisionAt
      D.largeAlmostJordan k := by
  intro p q hpq heq
  have hpne : p ≠ q := Fin.ne_of_lt hpq
  rcases D.largeEqualScale_involves_selected hpne heq with
    hpSelected | hqSelected
  · subst p
    rcases D.largePosition_eq_selected_or_common q with
      hqSelected | ⟨j, hqCommon⟩
    · subst q
      exact (lt_irrefl _ hpq).elim
    · subst q
      have heq' := heq
      simp only [largeAlmostJordan_scaleGenerator_selected,
        largeAlmostJordan_scaleGenerator_common] at heq'
      have hreverse :=
        D.largeCommonPosition_lt_selected_of_scaleOrder_eq j heq'.symm
      exact (lt_asymm hpq hreverse).elim
  · subst q
    rcases D.largePosition_eq_selected_or_common p with
      hpSelected | ⟨j, hpCommon⟩
    · subst p
      exact (lt_irrefl _ hpq).elim
    · subst p
      have heq' := heq
      simp only [largeAlmostJordan_scaleGenerator_selected,
        largeAlmostJordan_scaleGenerator_common] at heq'
      have hji : j = i :=
        D.complementStrictWeak_scaleOrder_strict.injective
          (heq'.trans hscale.symm)
      subst j
      exact ⟨hk.1.symm, hk.2.symm⟩

/-- The selected small block has the scale of a common-complement block. -/
def SmallScaleCollision (D : Beli2019Lemma51Data q M N) : Prop :=
  ∃ i : Fin D.complementComponentCount,
    ordUnit K D.input.block.scaleGenerator =
      ordUnit K (D.complementStrictWeak.scaleGenerator i)

/-- The enlarged selected block has the scale of a common-complement
block. -/
def LargeScaleCollision (D : Beli2019Lemma51Data q M N) : Prop :=
  ∃ i : Fin D.complementComponentCount,
    ordUnit K (D.complementStrictWeak.scaleGenerator i) =
      ordUnit K D.input.block.enlargedScaleGenerator

/-- In the absence of the unique possible small-side collision, the almost
Jordan decomposition is already strict. -/
theorem smallAlmostJordan_scaleOrder_strict_of_noCollision
    (D : Beli2019Lemma51Data q M N) (h : ¬D.SmallScaleCollision) :
    StrictMono (fun i ↦
      ordUnit K (D.smallAlmostJordan.scaleGenerator i)) := by
  apply D.smallAlmostJordan.scaleOrder_mono.strictMono_of_injective
  intro p q heq
  by_cases hpq : p = q
  · exact hpq
  rcases D.smallEqualScale_involves_selected hpq heq with
    hpSelected | hqSelected
  · subst p
    rcases D.smallPosition_eq_selected_or_common q with
      hqSelected | ⟨j, hqCommon⟩
    · exact hqSelected.symm
    · exfalso
      apply h
      refine ⟨j, ?_⟩
      subst q
      simpa only [smallAlmostJordan_scaleGenerator_selected,
        smallAlmostJordan_scaleGenerator_common] using heq
  · subst q
    rcases D.smallPosition_eq_selected_or_common p with
      hpSelected | ⟨j, hpCommon⟩
    · exact hpSelected
    · exfalso
      apply h
      refine ⟨j, ?_⟩
      subst p
      simpa only [smallAlmostJordan_scaleGenerator_selected,
        smallAlmostJordan_scaleGenerator_common] using heq.symm

/-- In the absence of the unique possible large-side collision, the almost
Jordan decomposition is already strict. -/
theorem largeAlmostJordan_scaleOrder_strict_of_noCollision
    (D : Beli2019Lemma51Data q M N) (h : ¬D.LargeScaleCollision) :
    StrictMono (fun i ↦
      ordUnit K (D.largeAlmostJordan.scaleGenerator i)) := by
  apply D.largeAlmostJordan.scaleOrder_mono.strictMono_of_injective
  intro p q heq
  by_cases hpq : p = q
  · exact hpq
  rcases D.largeEqualScale_involves_selected hpq heq with
    hpSelected | hqSelected
  · subst p
    rcases D.largePosition_eq_selected_or_common q with
      hqSelected | ⟨j, hqCommon⟩
    · exact hqSelected.symm
    · exfalso
      apply h
      refine ⟨j, ?_⟩
      subst q
      simpa only [largeAlmostJordan_scaleGenerator_selected,
        largeAlmostJordan_scaleGenerator_common] using heq.symm
  · subst q
    rcases D.largePosition_eq_selected_or_common p with
      hpSelected | ⟨j, hpCommon⟩
    · exact hpSelected
    · exfalso
      apply h
      refine ⟨j, ?_⟩
      subst p
      simpa only [largeAlmostJordan_scaleGenerator_selected,
        largeAlmostJordan_scaleGenerator_common] using heq

/-- Amalgamating equal-scale neighbours gives a genuine Jordan
decomposition of the smaller lattice. -/
noncomputable def smallJordan
    (D : Beli2019Lemma51Data q M N) :
    Σ s : Nat, JordanDecomposition q N s := by
  classical
  by_cases hcollision : D.SmallScaleCollision
  · let i := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.smallCollision_adjacent i hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.smallAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.smallAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [smallAlmostJordan_scaleGenerator_selected,
        smallAlmostJordan_scaleGenerator_common] using hscale
    let S := D.smallAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.smallAlmostJordan k heq
          (D.smallOnlyScaleCollisionAt i hscale k hk)
    exact ⟨D.complementComponentCount, S.toJordan hstrict⟩
  · exact ⟨D.complementComponentCount + 1,
      D.smallAlmostJordan.toJordan
        (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hcollision)⟩

/-- Amalgamating equal-scale neighbours gives a genuine Jordan
decomposition of the larger lattice. -/
noncomputable def largeJordan
    (D : Beli2019Lemma51Data q M N) :
    Σ s : Nat, JordanDecomposition q M s := by
  classical
  by_cases hcollision : D.LargeScaleCollision
  · let i := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent i hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [largeAlmostJordan_scaleGenerator_selected,
        largeAlmostJordan_scaleGenerator_common] using hscale
    let S := D.largeAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt i hscale k hk)
    exact ⟨D.complementComponentCount, S.toJordan hstrict⟩
  · exact ⟨D.complementComponentCount + 1,
      D.largeAlmostJordan.toJordan
        (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hcollision)⟩

end Beli2019Lemma51Data

end Lattice

end Bong
