/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.WeakJordanDecomposition
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex

/-!
# Sorting a finite modular decomposition by scale

An orthogonal decomposition into nonzero modular components need not be
presented in scale order.  We sort its finite index type by the pair
`(scale order, old index)`.  The old index is only a tie-breaker, so the
resulting scale orders are nondecreasing.  The result is a weak Jordan
decomposition and can therefore be amalgamated by the existing O'Meara
construction.

This is the bookkeeping needed for the "almost Jordan decompositions" in
Beli (2019), Section 5: the exceptional block may occur at an arbitrary
scale among the components of the common orthogonal complement.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s t : Nat}

namespace OrthogonalDecomposition

/-- Reindex a finite orthogonal decomposition along an equivalence. -/
noncomputable def reindex (D : OrthogonalDecomposition q L t)
    (e : Fin s ≃ Fin t) : OrthogonalDecomposition q L s where
  component i := D.component (e i)
  orthogonal := by
    intro i j hij
    exact D.orthogonal (e i) (e j) (fun h ↦ hij (e.injective h))
  sum_eq :=
    (e.iSup_comp (g := fun i ↦ (D.component i).ambientSubmodule)).trans
      D.sum_eq

@[simp]
theorem reindex_component (D : OrthogonalDecomposition q L t)
    (e : Fin s ≃ Fin t) (i : Fin s) :
    (D.reindex e).component i = D.component (e i) :=
  rfl

end OrthogonalDecomposition

/-- A finite orthogonal decomposition into nonzero modular components,
before its components have been sorted by scale. -/
structure ModularDecomposition (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat)
    extends OrthogonalDecomposition q L t where
  scaleGenerator : Fin t → Kˣ
  modular : ∀ i, IsModular (component i).space (component i).lattice
    (scaleGenerator i)
  component_finrank_pos : ∀ i, 0 < finrank K (component i).carrier

namespace ModularDecomposition

/-- Cyclic tie-break permutation sending the distinguished old index `0` to
the last position and every old successor index one place to the left. -/
def distinguishedLastTie (t : Nat) : Fin (t + 1) ≃ Fin (t + 1) where
  toFun := Fin.cases (Fin.last t) (fun i ↦ i.castSucc)
  invFun := Fin.lastCases 0 (fun i ↦ i.succ)
  left_inv := by
    intro i
    cases i using Fin.cases with
    | zero => apply Fin.ext; simp
    | succ i => apply Fin.ext; simp
  right_inv := by
    intro i
    cases i using Fin.lastCases with
    | last => apply Fin.ext; simp
    | cast i => apply Fin.ext; simp

@[simp]
theorem distinguishedLastTie_zero (t : Nat) :
    distinguishedLastTie t 0 = Fin.last t :=
  rfl

@[simp]
theorem distinguishedLastTie_succ (t : Nat) (i : Fin t) :
    distinguishedLastTie t i.succ = i.castSucc :=
  rfl

/-- A copy of the old component index, used so that its temporary sorting
order cannot interfere with the canonical order on `Fin t`. -/
structure ScaleIndex (t : Nat) where
  val : Fin t
  deriving DecidableEq, Fintype

namespace ScaleIndex

@[ext]
theorem ext {i j : ScaleIndex t} (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- Forget the sorting wrapper. -/
def equivFin : ScaleIndex t ≃ Fin t where
  toFun := val
  invFun i := ⟨i⟩
  left_inv i := by cases i; rfl
  right_inv _ := rfl

/-- Sort first by scale order and use the old finite index only to break
ties. -/
noncomputable def key (D : ModularDecomposition q L t)
    (tie : Fin t ≃ Fin t)
    (i : ScaleIndex t) : Int ×ₗ Nat :=
  toLex (ordUnit K (D.scaleGenerator i.val), (tie i.val).val)

theorem key_injective (D : ModularDecomposition q L t)
    (tie : Fin t ≃ Fin t) : Function.Injective (key D tie) := by
  intro i j h
  apply ext
  apply tie.injective
  apply Fin.ext
  exact congrArg (fun z : Int ×ₗ Nat ↦ (ofLex z).2) h

/-- For blocks of equal scale, the lifted key order is exactly the selected
tie-breaking order. -/
theorem key_lt_key_iff_of_scaleOrder_eq
    (D : ModularDecomposition q L t) (tie : Fin t ≃ Fin t)
    {i j : Fin t}
    (hscale : ordUnit K (D.scaleGenerator i) =
      ordUnit K (D.scaleGenerator j)) :
    key D tie ⟨i⟩ < key D tie ⟨j⟩ ↔
      (tie i).val < (tie j).val := by
  simp [key, Prod.Lex.lt_iff', hscale]

end ScaleIndex

variable (D : ModularDecomposition q L t)

/-- A reindexing which puts the scale orders in nondecreasing order. -/
structure SortedReindex where
  equiv : Fin t ≃ Fin t
  tie : Fin t ≃ Fin t
  scaleOrder_mono : Monotone
    (fun i ↦ ordUnit K (D.scaleGenerator (equiv i)))
  keyOrder_iff : ∀ i j,
    i < j ↔
      ScaleIndex.key D tie ⟨equiv i⟩ <
        ScaleIndex.key D tie ⟨equiv j⟩

/-- Every finite modular decomposition has a scale-sorted reindexing, with
an arbitrary permutation used to break ties between equal-scale blocks. -/
noncomputable def sortedReindexBy (tie : Fin t ≃ Fin t) :
    SortedReindex D := by
  letI : LinearOrder (ScaleIndex t) :=
    LinearOrder.lift' (ScaleIndex.key D tie)
      (ScaleIndex.key_injective D tie)
  let eOrder : Fin t ≃o ScaleIndex t :=
    Fintype.orderIsoFinOfCardEq (ScaleIndex t) (by
      simpa using Fintype.card_congr (ScaleIndex.equivFin (t := t)))
  let e : Fin t ≃ Fin t := eOrder.toEquiv.trans ScaleIndex.equivFin
  refine ⟨e, tie, ?_, ?_⟩
  · intro i j hij
    by_cases hEq : i = j
    · subst j
      exact le_rfl
    have hij' : i < j := lt_of_le_of_ne hij hEq
    have hsorted : eOrder i < eOrder j := eOrder.strictMono hij'
    change ScaleIndex.key D tie (eOrder i) <
      ScaleIndex.key D tie (eOrder j) at hsorted
    exact (Prod.Lex.lt_iff'.mp hsorted).1
  · intro i j
    change i < j ↔ eOrder i < eOrder j
    exact eOrder.lt_iff_lt.symm

/-- The position of an old component in a sorted reindexing is determined
exactly by its scale-and-tie key. -/
theorem SortedReindex.oldPosition_lt_iff
    (S : SortedReindex D) (i j : Fin t) :
    S.equiv.symm i < S.equiv.symm j ↔
      ScaleIndex.key D S.tie ⟨i⟩ <
        ScaleIndex.key D S.tie ⟨j⟩ := by
  simpa using S.keyOrder_iff (S.equiv.symm i) (S.equiv.symm j)

/-- The numerical sorted position of an old component is the number of old
components with strictly smaller scale-and-tie key.  This exposes the rank
of a component without depending on the implementation of `Fintype`'s
sorting equivalence. -/
theorem SortedReindex.oldPosition_val_eq_card_key_lt
    (S : SortedReindex D) (i : Fin t) :
    (S.equiv.symm i).val =
      ((Finset.univ : Finset (Fin t)).filter fun j ↦
        ScaleIndex.key D S.tie ⟨j⟩ <
          ScaleIndex.key D S.tie ⟨i⟩).card := by
  classical
  let e : {p : Fin t // p < S.equiv.symm i} ≃
      {j : Fin t // ScaleIndex.key D S.tie ⟨j⟩ <
        ScaleIndex.key D S.tie ⟨i⟩} := {
    toFun := fun p ↦ ⟨S.equiv p, by
      simpa using
        (S.keyOrder_iff p (S.equiv.symm i)).mp p.property⟩
    invFun := fun j ↦ ⟨S.equiv.symm j, by
      apply (S.keyOrder_iff (S.equiv.symm j)
        (S.equiv.symm i)).mpr
      simpa using j.property⟩
    left_inv := by
      intro p
      apply Subtype.ext
      exact S.equiv.symm_apply_apply p
    right_inv := by
      intro j
      apply Subtype.ext
      exact S.equiv.apply_symm_apply j
  }
  calc
    (S.equiv.symm i).val =
        Fintype.card {p : Fin t // p < S.equiv.symm i} := by
      rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio,
        Fin.card_Iio]
    _ = Fintype.card {j : Fin t //
          ScaleIndex.key D S.tie ⟨j⟩ <
            ScaleIndex.key D S.tie ⟨i⟩} :=
      Fintype.card_congr e
    _ = ((Finset.univ : Finset (Fin t)).filter fun j ↦
          ScaleIndex.key D S.tie ⟨j⟩ <
            ScaleIndex.key D S.tie ⟨i⟩).card := by
      rw [Fintype.card_subtype]

/-- Equal-scale old components occur in the order prescribed by the
tie-breaking permutation. -/
theorem SortedReindex.oldPosition_lt_iff_of_scaleOrder_eq
    (S : SortedReindex D) {i j : Fin t}
    (hscale : ordUnit K (D.scaleGenerator i) =
      ordUnit K (D.scaleGenerator j)) :
    S.equiv.symm i < S.equiv.symm j ↔
      (S.tie i).val < (S.tie j).val := by
  rw [S.oldPosition_lt_iff]
  exact ScaleIndex.key_lt_key_iff_of_scaleOrder_eq D S.tie hscale

/-- If all old successor components have pairwise distinct scale orders,
then any equality between two distinct sorted scale positions involves the
distinguished old component `0`. -/
theorem SortedReindex.equalScale_involves_oldZero
    {t : Nat} (D : ModularDecomposition q L (t + 1))
    (S : SortedReindex D)
    (hstrict : StrictMono (fun i : Fin t ↦
      ordUnit K (D.scaleGenerator i.succ)))
    {i j : Fin (t + 1)} (hij : i ≠ j)
    (heq : ordUnit K (D.scaleGenerator (S.equiv i)) =
      ordUnit K (D.scaleGenerator (S.equiv j))) :
    i = S.equiv.symm 0 ∨ j = S.equiv.symm 0 := by
  generalize hiold : S.equiv i = oi
  generalize hjold : S.equiv j = oj
  cases oi using Fin.cases with
  | zero =>
      left
      apply S.equiv.injective
      rw [hiold]
      simp
  | succ oi =>
      cases oj using Fin.cases with
      | zero =>
          right
          apply S.equiv.injective
          rw [hjold]
          simp
      | succ oj =>
          rw [hiold, hjold] at heq
          have hoij : oi = oj := hstrict.injective heq
          apply (hij ?_).elim
          apply S.equiv.injective
          rw [hiold, hjold, hoij]

/-- Every sorted position is either the distinguished old position `0` or
the position of a unique old successor component. -/
theorem SortedReindex.position_eq_oldZero_or_succ
    {t : Nat} (D : ModularDecomposition q L (t + 1))
    (S : SortedReindex D) (i : Fin (t + 1)) :
    i = S.equiv.symm 0 ∨
      ∃ j : Fin t, i = S.equiv.symm j.succ := by
  generalize hiold : S.equiv i = oi
  cases oi using Fin.cases with
  | zero =>
      left
      apply S.equiv.injective
      rw [hiold]
      simp
  | succ j =>
      right
      refine ⟨j, ?_⟩
      apply S.equiv.injective
      rw [hiold]
      simp

/-- The default scale sort retains the old index order when scales agree. -/
noncomputable def sortedReindex : SortedReindex D :=
  D.sortedReindexBy (Equiv.refl _)

@[simp]
theorem sortedReindexBy_tie (tie : Fin t ≃ Fin t) :
    (D.sortedReindexBy tie).tie = tie :=
  rfl

@[simp]
theorem sortedReindex_tie : D.sortedReindex.tie = Equiv.refl _ :=
  rfl

/-- Sorting the component indices turns an arbitrary finite modular
decomposition into a weak Jordan decomposition. -/
noncomputable def sortedWeakJordan : WeakJordanDecomposition q L t :=
  let S := D.sortedReindex
  {
    toOrthogonalDecomposition :=
      D.toOrthogonalDecomposition.reindex S.equiv
    scaleGenerator := fun i ↦ D.scaleGenerator (S.equiv i)
    modular := fun i ↦ D.modular (S.equiv i)
    component_finrank_pos := fun i ↦ D.component_finrank_pos (S.equiv i)
    scaleOrder_mono := S.scaleOrder_mono
  }

/-- Scale sorting with a caller-selected tie-breaking permutation. -/
noncomputable def sortedWeakJordanBy (tie : Fin t ≃ Fin t) :
    WeakJordanDecomposition q L t :=
  let S := D.sortedReindexBy tie
  {
    toOrthogonalDecomposition :=
      D.toOrthogonalDecomposition.reindex S.equiv
    scaleGenerator := fun i ↦ D.scaleGenerator (S.equiv i)
    modular := fun i ↦ D.modular (S.equiv i)
    component_finrank_pos := fun i ↦ D.component_finrank_pos (S.equiv i)
    scaleOrder_mono := S.scaleOrder_mono
  }

@[simp]
theorem sortedWeakJordan_component_at_old (i : Fin t) :
    D.sortedWeakJordan.component (D.sortedReindex.equiv.symm i) =
      D.component i := by
  simp [sortedWeakJordan]

@[simp]
theorem sortedWeakJordan_scaleGenerator_at_old (i : Fin t) :
    D.sortedWeakJordan.scaleGenerator (D.sortedReindex.equiv.symm i) =
      D.scaleGenerator i := by
  simp [sortedWeakJordan]

@[simp]
theorem sortedWeakJordanBy_component_at_old
    (tie : Fin t ≃ Fin t) (i : Fin t) :
    (D.sortedWeakJordanBy tie).component
        ((D.sortedReindexBy tie).equiv.symm i) =
      D.component i := by
  simp [sortedWeakJordanBy]

@[simp]
theorem sortedWeakJordanBy_scaleGenerator_at_old
    (tie : Fin t ≃ Fin t) (i : Fin t) :
    (D.sortedWeakJordanBy tie).scaleGenerator
        ((D.sortedReindexBy tie).equiv.symm i) =
      D.scaleGenerator i := by
  simp [sortedWeakJordanBy]

end ModularDecomposition

end Lattice

end Bong
