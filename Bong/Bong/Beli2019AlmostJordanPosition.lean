/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordan

/-!
# Positions in Beli's almost Jordan decompositions

This file identifies the two insertion positions denoted `k₁` and `k₂` in
Beli (2019), Section 5.  On the larger side an equal-scale common component
precedes the selected component; on the smaller side it follows it.
Consequently the two positions count common scales `≤ r'` and `< r`,
respectively.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Match a position of the larger sorted family to the position of the
same old component in the smaller sorted family. -/
noncomputable def largeToSmallPositionEquiv
    (D : Beli2019Lemma51Data q M N) :
    Fin (D.complementComponentCount + 1) ≃
      Fin (D.complementComponentCount + 1) :=
  D.largeSort.equiv.trans D.smallSort.equiv.symm

@[simp]
theorem largeToSmallPositionEquiv_selected
    (D : Beli2019Lemma51Data q M N) :
    D.largeToSmallPositionEquiv D.largeSelectedPosition =
      D.smallSelectedPosition := by
  simp [largeToSmallPositionEquiv, largeSelectedPosition,
    smallSelectedPosition]

@[simp]
theorem largeToSmallPositionEquiv_common
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeToSmallPositionEquiv (D.largeCommonPosition i) =
      D.smallCommonPosition i := by
  simp [largeToSmallPositionEquiv, largeCommonPosition,
    smallCommonPosition]

/-- Number of common-complement components whose scale is strictly below
the supplied order. -/
noncomputable def commonScaleCountLT
    (D : Beli2019Lemma51Data q M N) (r : Int) : Nat :=
  ((Finset.univ : Finset (Fin D.complementComponentCount)).filter
    fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) < r).card

/-- Number of common-complement components whose scale is at most the
supplied order. -/
noncomputable def commonScaleCountLE
    (D : Beli2019Lemma51Data q M N) (r : Int) : Nat :=
  ((Finset.univ : Finset (Fin D.complementComponentCount)).filter
    fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤ r).card

/-- On the smaller side a common block has a smaller sorting key than the
selected block exactly when its scale order is strictly smaller. -/
theorem smallCommon_key_lt_selected_iff
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
        D.smallSort.tie ⟨i.succ⟩ <
      ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
        D.smallSort.tie ⟨0⟩ ↔
    ordUnit K (D.complementStrictWeak.scaleGenerator i) <
      ordUnit K D.input.block.scaleGenerator := by
  simp [ModularDecomposition.ScaleIndex.key,
    ModularDecomposition.sortedReindex,
    smallSort, smallModularDecomposition, Prod.Lex.lt_iff']
  omega

/-- On the larger side the distinguished-last tie rule changes strict key
comparison into a non-strict comparison of scale orders. -/
theorem largeCommon_key_lt_selected_iff
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
        D.largeSort.tie ⟨i.succ⟩ <
      ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
        D.largeSort.tie ⟨0⟩ ↔
    ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
  simp [ModularDecomposition.ScaleIndex.key, largeSort, largeTie,
    largeModularDecomposition, Prod.Lex.lt_iff']

/-- Sorting preserves the original strict order of common-complement
components on the smaller side. -/
theorem smallCommon_key_lt_common_iff
    (D : Beli2019Lemma51Data q M N)
    (i j : Fin D.complementComponentCount) :
    ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
        D.smallSort.tie ⟨i.succ⟩ <
      ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
        D.smallSort.tie ⟨j.succ⟩ ↔ i < j := by
  constructor
  · intro hkey
    by_contra hnot
    have hji : j ≤ i := le_of_not_gt hnot
    rcases hji.eq_or_lt with rfl | hji
    · exact (lt_irrefl _ hkey).elim
    · have hreverse := D.complementStrictWeak_scaleOrder_strict hji
      have hreverseKey : ModularDecomposition.ScaleIndex.key
            D.smallModularDecomposition D.smallSort.tie ⟨j.succ⟩ <
          ModularDecomposition.ScaleIndex.key
            D.smallModularDecomposition D.smallSort.tie ⟨i.succ⟩ := by
        simp only [ModularDecomposition.ScaleIndex.key,
          smallModularDecomposition]
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inl hreverse
      exact (lt_asymm hkey hreverseKey).elim
  · intro hij
    have hscale := D.complementStrictWeak_scaleOrder_strict hij
    simp only [ModularDecomposition.ScaleIndex.key,
      smallModularDecomposition]
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hscale

/-- Sorting preserves the original strict order of common-complement
components on the larger side. -/
theorem largeCommon_key_lt_common_iff
    (D : Beli2019Lemma51Data q M N)
    (i j : Fin D.complementComponentCount) :
    ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
        D.largeSort.tie ⟨i.succ⟩ <
      ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
        D.largeSort.tie ⟨j.succ⟩ ↔ i < j := by
  constructor
  · intro hkey
    by_contra hnot
    have hji : j ≤ i := le_of_not_gt hnot
    rcases hji.eq_or_lt with rfl | hji
    · exact (lt_irrefl _ hkey).elim
    · have hreverse := D.complementStrictWeak_scaleOrder_strict hji
      have hreverseKey : ModularDecomposition.ScaleIndex.key
            D.largeModularDecomposition D.largeSort.tie ⟨j.succ⟩ <
          ModularDecomposition.ScaleIndex.key
            D.largeModularDecomposition D.largeSort.tie ⟨i.succ⟩ := by
        simp only [ModularDecomposition.ScaleIndex.key,
          largeModularDecomposition]
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inl hreverse
      exact (lt_asymm hkey hreverseKey).elim
  · intro hij
    have hscale := D.complementStrictWeak_scaleOrder_strict hij
    simp only [ModularDecomposition.ScaleIndex.key,
      largeModularDecomposition]
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hscale

/-- The exact numerical insertion position on the smaller side. -/
theorem smallSelectedPosition_val
    (D : Beli2019Lemma51Data q M N) :
    D.smallSelectedPosition.val =
      D.commonScaleCountLT
        (ordUnit K D.input.block.scaleGenerator) := by
  classical
  let e : {j : Fin (D.complementComponentCount + 1) //
        ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
            D.smallSort.tie ⟨j⟩ <
          ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
            D.smallSort.tie ⟨0⟩} ≃
      {i : Fin D.complementComponentCount //
        ordUnit K (D.complementStrictWeak.scaleGenerator i) <
          ordUnit K D.input.block.scaleGenerator} := {
    toFun := fun j ↦ by
      rcases j with ⟨j, hj⟩
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hj).elim
      | succ i => exact ⟨i, (D.smallCommon_key_lt_selected_iff i).mp hj⟩
    invFun := fun i ↦
      ⟨i.1.succ, (D.smallCommon_key_lt_selected_iff i).mpr i.2⟩
    left_inv := by
      rintro ⟨j, hj⟩
      apply Subtype.ext
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hj).elim
      | succ i => rfl
    right_inv := by
      intro i
      apply Subtype.ext
      rfl
  }
  calc
    D.smallSelectedPosition.val =
        ((Finset.univ : Finset
          (Fin (D.complementComponentCount + 1))).filter fun j ↦
            ModularDecomposition.ScaleIndex.key
                D.smallModularDecomposition D.smallSort.tie ⟨j⟩ <
              ModularDecomposition.ScaleIndex.key
                D.smallModularDecomposition D.smallSort.tie ⟨0⟩).card := by
      exact ModularDecomposition.SortedReindex.oldPosition_val_eq_card_key_lt
        D.smallModularDecomposition D.smallSort 0
    _ = Fintype.card {j : Fin (D.complementComponentCount + 1) //
          ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
              D.smallSort.tie ⟨j⟩ <
            ModularDecomposition.ScaleIndex.key D.smallModularDecomposition
              D.smallSort.tie ⟨0⟩} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card {i : Fin D.complementComponentCount //
          ordUnit K (D.complementStrictWeak.scaleGenerator i) <
            ordUnit K D.input.block.scaleGenerator} :=
      Fintype.card_congr e
    _ = D.commonScaleCountLT
          (ordUnit K D.input.block.scaleGenerator) := by
      rw [commonScaleCountLT, Fintype.card_subtype]

/-- The exact numerical insertion position on the larger side. -/
theorem largeSelectedPosition_val
    (D : Beli2019Lemma51Data q M N) :
    D.largeSelectedPosition.val =
      D.commonScaleCountLE
        (ordUnit K D.input.block.enlargedScaleGenerator) := by
  classical
  let e : {j : Fin (D.complementComponentCount + 1) //
        ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
            D.largeSort.tie ⟨j⟩ <
          ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
            D.largeSort.tie ⟨0⟩} ≃
      {i : Fin D.complementComponentCount //
        ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤
          ordUnit K D.input.block.enlargedScaleGenerator} := {
    toFun := fun j ↦ by
      rcases j with ⟨j, hj⟩
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hj).elim
      | succ i => exact ⟨i, (D.largeCommon_key_lt_selected_iff i).mp hj⟩
    invFun := fun i ↦
      ⟨i.1.succ, (D.largeCommon_key_lt_selected_iff i).mpr i.2⟩
    left_inv := by
      rintro ⟨j, hj⟩
      apply Subtype.ext
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hj).elim
      | succ i => rfl
    right_inv := by
      intro i
      apply Subtype.ext
      rfl
  }
  calc
    D.largeSelectedPosition.val =
        ((Finset.univ : Finset
          (Fin (D.complementComponentCount + 1))).filter fun j ↦
            ModularDecomposition.ScaleIndex.key
                D.largeModularDecomposition D.largeSort.tie ⟨j⟩ <
              ModularDecomposition.ScaleIndex.key
                D.largeModularDecomposition D.largeSort.tie ⟨0⟩).card := by
      exact ModularDecomposition.SortedReindex.oldPosition_val_eq_card_key_lt
        D.largeModularDecomposition D.largeSort 0
    _ = Fintype.card {j : Fin (D.complementComponentCount + 1) //
          ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
              D.largeSort.tie ⟨j⟩ <
            ModularDecomposition.ScaleIndex.key D.largeModularDecomposition
              D.largeSort.tie ⟨0⟩} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card {i : Fin D.complementComponentCount //
          ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤
            ordUnit K D.input.block.enlargedScaleGenerator} :=
      Fintype.card_congr e
    _ = D.commonScaleCountLE
          (ordUnit K D.input.block.enlargedScaleGenerator) := by
      rw [commonScaleCountLE, Fintype.card_subtype]

/-- In the binary case `r = r' + 1`, hence the two selected components
occupy the same numerical position. -/
theorem selectedPositions_eq_of_rank_two
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2) :
    D.smallSelectedPosition = D.largeSelectedPosition := by
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 1 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · omega
    · exact hTwo.2
  apply Fin.ext
  rw [D.smallSelectedPosition_val, D.largeSelectedPosition_val]
  unfold commonScaleCountLT commonScaleCountLE
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- In the unary case, if no common component has the unique intermediate
scale `r' + 1`, the two selected positions coincide. -/
theorem selectedPositions_eq_of_rank_one_of_noIntermediate
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hno : ¬∃ i : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator i) =
        ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.smallSelectedPosition = D.largeSelectedPosition := by
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  apply Fin.ext
  rw [D.smallSelectedPosition_val, D.largeSelectedPosition_val]
  unfold commonScaleCountLT commonScaleCountLE
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hle
    have heq : ordUnit K (D.complementStrictWeak.scaleGenerator i) =
        ordUnit K D.input.block.enlargedScaleGenerator + 1 := by
      omega
    exact hno ⟨i, heq⟩
  · intro hi
    omega

/-- In the unary intermediate-scale case, the smaller selected component
is exactly one component position to the right of the larger one. -/
theorem smallSelectedPosition_val_eq_large_add_one_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.smallSelectedPosition.val = D.largeSelectedPosition.val + 1 := by
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  let smallSet :=
    (Finset.univ : Finset (Fin D.complementComponentCount)).filter
      fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K D.input.block.scaleGenerator
  let largeSet :=
    (Finset.univ : Finset (Fin D.complementComponentCount)).filter
      fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤
        ordUnit K D.input.block.enlargedScaleGenerator
  have hsets : smallSet = insert i₀ largeSet := by
    ext i
    simp only [smallSet, largeSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hle : ordUnit K
          (D.complementStrictWeak.scaleGenerator i) ≤
          ordUnit K D.input.block.enlargedScaleGenerator
      · exact Or.inr hle
      · left
        have hiEq : ordUnit K
            (D.complementStrictWeak.scaleGenerator i) =
            ordUnit K D.input.block.enlargedScaleGenerator + 1 := by
          omega
        exact D.complementStrictWeak_scaleOrder_strict.injective
          (hiEq.trans hi₀.symm)
    · rintro (rfl | hi)
      · omega
      · omega
  have hi₀not : i₀ ∉ largeSet := by
    simp only [largeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [D.smallSelectedPosition_val, D.largeSelectedPosition_val]
  change smallSet.card = largeSet.card + 1
  rw [hsets, Finset.card_insert_of_notMem hi₀not]

/-- Complete `k₁/k₂` alternative in the unary case: either the selected
positions agree, or there is a unique intermediate-scale common component
and the positions differ by one. -/
theorem selectedPositions_unary_alternative
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    D.smallSelectedPosition = D.largeSelectedPosition ∨
      ∃! i : Fin D.complementComponentCount,
        ordUnit K (D.complementStrictWeak.scaleGenerator i) =
          ordUnit K D.input.block.enlargedScaleGenerator + 1 ∧
        D.smallSelectedPosition.val = D.largeSelectedPosition.val + 1 := by
  classical
  by_cases hmid : ∃ i : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator i) =
        ordUnit K D.input.block.enlargedScaleGenerator + 1
  · right
    obtain ⟨i₀, hi₀⟩ := hmid
    refine ⟨i₀, ⟨hi₀,
      D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀⟩, ?_⟩
    intro i hi
    exact D.complementStrictWeak_scaleOrder_strict.injective
      (hi.1.trans hi₀.symm)
  · left
    exact D.selectedPositions_eq_of_rank_one_of_noIntermediate hfin hmid

/-- Common positions occur in their original strict order on the smaller
side. -/
theorem smallCommonPosition_strict
    (D : Beli2019Lemma51Data q M N) :
    StrictMono D.smallCommonPosition := by
  intro i j hij
  apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff
    D.smallModularDecomposition D.smallSort i.succ j.succ).mpr
  exact (D.smallCommon_key_lt_common_iff i j).mpr hij

/-- Common positions occur in their original strict order on the larger
side. -/
theorem largeCommonPosition_strict
    (D : Beli2019Lemma51Data q M N) :
    StrictMono D.largeCommonPosition := by
  intro i j hij
  apply (ModularDecomposition.SortedReindex.oldPosition_lt_iff
    D.largeModularDecomposition D.largeSort i.succ j.succ).mpr
  exact (D.largeCommon_key_lt_common_iff i j).mpr hij

/-- The common components enumerate every smaller-side position except the
selected one, in increasing order. -/
noncomputable def smallCommonPositionOrderIso
    (D : Beli2019Lemma51Data q M N) :
    Fin D.complementComponentCount ≃o
      {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.smallSelectedPosition} := by
  let f : Fin D.complementComponentCount →
      {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.smallSelectedPosition} := fun i ↦
    ⟨D.smallCommonPosition i, (D.smallSelectedPosition_ne_common i).symm⟩
  have hinj : Function.Injective f := fun _ _ h ↦
    D.smallCommonPosition_strict.injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro p
    rcases D.smallPosition_eq_selected_or_common p.1 with
      hselected | ⟨i, hcommon⟩
    · exact (p.2 hselected).elim
    · refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hcommon.symm
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro i j
      constructor
      · intro hij
        apply le_of_not_gt
        intro hji
        exact (not_lt_of_ge hij) (D.smallCommonPosition_strict hji)
      · intro hij
        exact D.smallCommonPosition_strict.monotone hij
  }

@[simp]
theorem smallCommonPositionOrderIso_apply
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    (D.smallCommonPositionOrderIso i).1 = D.smallCommonPosition i := by
  rfl

/-- The common components enumerate every larger-side position except the
selected one, in increasing order. -/
noncomputable def largeCommonPositionOrderIso
    (D : Beli2019Lemma51Data q M N) :
    Fin D.complementComponentCount ≃o
      {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.largeSelectedPosition} := by
  let f : Fin D.complementComponentCount →
      {p : Fin (D.complementComponentCount + 1) //
        p ≠ D.largeSelectedPosition} := fun i ↦
    ⟨D.largeCommonPosition i, (D.largeSelectedPosition_ne_common i).symm⟩
  have hinj : Function.Injective f := fun _ _ h ↦
    D.largeCommonPosition_strict.injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro p
    rcases D.largePosition_eq_selected_or_common p.1 with
      hselected | ⟨i, hcommon⟩
    · exact (p.2 hselected).elim
    · refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hcommon.symm
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro i j
      constructor
      · intro hij
        apply le_of_not_gt
        intro hji
        exact (not_lt_of_ge hij) (D.largeCommonPosition_strict hji)
      · intro hij
        exact D.largeCommonPosition_strict.monotone hij
  }

@[simp]
theorem largeCommonPositionOrderIso_apply
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    (D.largeCommonPositionOrderIso i).1 = D.largeCommonPosition i := by
  rfl

/-- The smaller common positions are the canonical increasing enumeration
obtained by skipping the selected position. -/
theorem smallCommonPosition_eq_succAbove
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.smallCommonPosition i = D.smallSelectedPosition.succAbove i := by
  have happ := congrArg (fun e ↦ (e i).1)
    (Subsingleton.elim D.smallCommonPositionOrderIso
      (finSuccAboveOrderIso D.smallSelectedPosition))
  simpa [finSuccAboveOrderIso_apply] using happ

/-- The larger common positions are the canonical increasing enumeration
obtained by skipping the selected position. -/
theorem largeCommonPosition_eq_succAbove
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount) :
    D.largeCommonPosition i = D.largeSelectedPosition.succAbove i := by
  have happ := congrArg (fun e ↦ (e i).1)
    (Subsingleton.elim D.largeCommonPositionOrderIso
      (finSuccAboveOrderIso D.largeSelectedPosition))
  simpa [finSuccAboveOrderIso_apply] using happ

/-- The unique intermediate-scale component in the unary exceptional case
has old common index equal to the larger selected insertion position. -/
theorem intermediateIndex_val_eq_largeSelectedPosition
    (D : Beli2019Lemma51Data q M N)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    i₀.val = D.largeSelectedPosition.val := by
  classical
  let selectedSet :=
    (Finset.univ : Finset (Fin D.complementComponentCount)).filter
      fun i ↦ ordUnit K (D.complementStrictWeak.scaleGenerator i) ≤
        ordUnit K D.input.block.enlargedScaleGenerator
  have hset : selectedSet = Finset.Iio i₀ := by
    ext i
    simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    constructor
    · intro hscale
      by_contra hnot
      have hle : i₀ ≤ i := le_of_not_gt hnot
      rcases hle.eq_or_lt with hEq | hlt
      · subst i
        omega
      · have hstrict := D.complementStrictWeak_scaleOrder_strict hlt
        change ordUnit K (D.complementStrictWeak.scaleGenerator i₀) <
          ordUnit K (D.complementStrictWeak.scaleGenerator i) at hstrict
        rw [hi₀] at hstrict
        omega
    · intro hlt
      have hstrict := D.complementStrictWeak_scaleOrder_strict hlt
      change ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K (D.complementStrictWeak.scaleGenerator i₀) at hstrict
      rw [hi₀] at hstrict
      omega
  rw [D.largeSelectedPosition_val]
  change i₀.val = selectedSet.card
  rw [hset]
  exact (Fin.card_Iio i₀).symm

/-- In the unary intermediate-scale case, the intermediate common component
occupies the smaller numerical slot of the adjacent transposition. -/
theorem smallCommonPosition_eq_largeSelectedPosition_of_intermediate
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.smallCommonPosition i₀ = D.largeSelectedPosition := by
  have hselected :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hiVal := D.intermediateIndex_val_eq_largeSelectedPosition i₀ hi₀
  rw [D.smallCommonPosition_eq_succAbove]
  rw [Fin.succAbove_of_castSucc_lt]
  · apply Fin.ext
    exact hiVal
  · change i₀.val < D.smallSelectedPosition.val
    omega

/-- The same intermediate component occupies the larger numerical slot on
the larger side. -/
theorem largeCommonPosition_eq_smallSelectedPosition_of_intermediate
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.largeCommonPosition i₀ = D.smallSelectedPosition := by
  have hselected :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hiVal := D.intermediateIndex_val_eq_largeSelectedPosition i₀ hi₀
  rw [D.largeCommonPosition_eq_succAbove]
  rw [Fin.succAbove_of_le_castSucc]
  · apply Fin.ext
    simp only [Fin.val_succ]
    omega
  · change D.largeSelectedPosition.val ≤ i₀.val
    omega

/-- Every other common component keeps the same numerical position across
the adjacent unary transposition. -/
theorem commonPositions_eq_of_intermediate_of_ne
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ j : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (hne : j ≠ i₀) :
    D.smallCommonPosition j = D.largeCommonPosition j := by
  have hselected :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hiVal := D.intermediateIndex_val_eq_largeSelectedPosition i₀ hi₀
  rw [D.smallCommonPosition_eq_succAbove,
    D.largeCommonPosition_eq_succAbove]
  rcases lt_or_gt_of_ne hne with hjlt | hilt
  · rw [Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_castSucc_lt]
    · change j.val < D.largeSelectedPosition.val
      omega
    · change j.val < D.smallSelectedPosition.val
      omega
  · rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    · change D.largeSelectedPosition.val ≤ j.val
      omega
    · change D.smallSelectedPosition.val ≤ j.val
      omega

/-- If the selected positions agree, every corresponding common position
also agrees.  Both sides are the unique increasing enumeration of the same
finite order with one point removed. -/
theorem commonPositions_eq_of_selectedPositions_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (i : Fin D.complementComponentCount) :
    D.smallCommonPosition i = D.largeCommonPosition i := by
  have hsmall : D.smallCommonPosition i =
      D.smallSelectedPosition.succAbove i := by
    have happ := congrArg (fun e ↦ (e i).1)
      (Subsingleton.elim D.smallCommonPositionOrderIso
        (finSuccAboveOrderIso D.smallSelectedPosition))
    simpa [finSuccAboveOrderIso_apply] using happ
  have hlarge : D.largeCommonPosition i =
      D.largeSelectedPosition.succAbove i := by
    have happ := congrArg (fun e ↦ (e i).1)
      (Subsingleton.elim D.largeCommonPositionOrderIso
        (finSuccAboveOrderIso D.largeSelectedPosition))
    simpa [finSuccAboveOrderIso_apply] using happ
  rw [hsmall, hlarge, hselected]

/-- Under equality of the insertion positions, matching old identities is
the identity permutation of sorted positions. -/
theorem largeToSmallPositionEquiv_eq_refl_of_selectedPositions_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition) :
    D.largeToSmallPositionEquiv = Equiv.refl _ := by
  apply Equiv.ext
  intro p
  rcases D.largePosition_eq_selected_or_common p with
    hp | ⟨i, hp⟩
  · subst p
    simp only [largeToSmallPositionEquiv_selected, Equiv.refl_apply]
    exact hselected
  · subst p
    simp only [largeToSmallPositionEquiv_common, Equiv.refl_apply]
    exact D.commonPositions_eq_of_selectedPositions_eq hselected i

end Lattice.Beli2019Lemma51Data

end Bong
