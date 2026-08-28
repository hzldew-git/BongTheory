/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalSup
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Amalgamating adjacent orthogonal components

Two adjacent components of an orthogonal decomposition may be replaced by
their orthogonal sum.  The construction removes the second index and keeps
the order of all remaining components.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace OrthogonalDecomposition

variable (D : OrthogonalDecomposition q L (n + 2))

/-- The supremum of a finite tuple obtained by inserting one entry. -/
theorem iSup_insertNth {α : Type*} [CompleteLattice α]
    (k : Fin (n + 1)) (x : α) (f : Fin n → α) :
    (⨆ r, Fin.insertNth k x f r) = x ⊔ ⨆ r, f r := by
  apply le_antisymm
  · refine _root_.iSup_le fun r ↦ ?_
    induction r using Fin.succAboveCases k with
    | x => simpa using (_root_.le_sup_left : x ≤ x ⊔ ⨆ r, f r)
    | p r =>
      simpa using (_root_.le_sup_of_le_right
        (_root_.le_iSup f r) : f r ≤ x ⊔ ⨆ r, f r)
  · refine _root_.sup_le ?_ ?_
    · have h := _root_.le_iSup (Fin.insertNth k x f) k
      simpa using h
    · refine _root_.iSup_le fun r ↦ ?_
      have h := _root_.le_iSup (Fin.insertNth k x f)
        (k.succAbove r)
      simpa using h

/-- Components after amalgamating positions `k` and `k + 1`. -/
noncomputable def mergeComponents (k : Fin (n + 1)) :
    Fin (n + 1) → QuadraticSublattice q :=
  Fin.insertNth k (D.orthogonalSup k.castSucc_lt_succ.ne)
    (fun r ↦ D.component (k.succ.succAbove (k.succAbove r)))

@[simp]
theorem mergeComponents_other (k : Fin (n + 1)) (r : Fin n) :
    D.mergeComponents k (k.succAbove r) =
      D.component (k.succ.succAbove (k.succAbove r)) := by
  simp [mergeComponents]

@[simp]
theorem mergeComponents_self (k : Fin (n + 1)) :
    D.mergeComponents k k =
      D.orthogonalSup k.castSucc_lt_succ.ne := by
  exact Fin.insertNth_apply_same _ _ _

/-- Amalgamating adjacent components does not change their integral sum. -/
theorem iSup_mergeComponents (k : Fin (n + 1)) :
    (⨆ r, (D.mergeComponents k r).ambientSubmodule) =
      ⨆ a, (D.component a).ambientSubmodule := by
  have hleft :
      (fun r ↦ (D.mergeComponents k r).ambientSubmodule) =
        Fin.insertNth k
          ((D.orthogonalSup k.castSucc_lt_succ.ne).ambientSubmodule)
          (fun r ↦ (D.component
            (k.succ.succAbove (k.succAbove r))).ambientSubmodule) := by
    funext r
    induction r using Fin.succAboveCases k with
    | x => rw [D.mergeComponents_self, Fin.insertNth_apply_same]
    | p r => rw [D.mergeComponents_other,
        Fin.insertNth_apply_succAbove]
  rw [hleft, iSup_insertNth k
    ((D.orthogonalSup k.castSucc_lt_succ.ne).ambientSubmodule)
    (fun r ↦ (D.component
      (k.succ.succAbove (k.succAbove r))).ambientSubmodule)]
  rw [D.orthogonalSup_ambientSubmodule, sup_assoc]
  symm
  have hright :
      (fun a ↦ (D.component a).ambientSubmodule) =
        Fin.insertNth k.succ
          ((D.component k.succ).ambientSubmodule)
          (fun r ↦ (D.component
            (k.succ.succAbove r)).ambientSubmodule) := by
    funext a
    induction a using Fin.succAboveCases k.succ with
    | x => rw [Fin.insertNth_apply_same]
    | p r => rw [Fin.insertNth_apply_succAbove]
  rw [hright, iSup_insertNth k.succ
    ((D.component k.succ).ambientSubmodule)
    (fun r ↦ (D.component (k.succ.succAbove r)).ambientSubmodule)]
  have htail :
      (fun r ↦ (D.component
        (k.succ.succAbove r)).ambientSubmodule) =
        Fin.insertNth k
          ((D.component k.castSucc).ambientSubmodule)
          (fun r ↦ (D.component
            (k.succ.succAbove (k.succAbove r))).ambientSubmodule) := by
    funext r
    induction r using Fin.succAboveCases k with
    | x => rw [Fin.insertNth_apply_same,
        Fin.succAbove_succ_self]
    | p r => rw [Fin.insertNth_apply_succAbove]
  rw [htail, iSup_insertNth k
    ((D.component k.castSucc).ambientSubmodule)
    (fun r ↦ (D.component
      (k.succ.succAbove (k.succAbove r))).ambientSubmodule)]
  exact sup_left_comm _ _ _

/-- Replace adjacent components `k` and `k + 1` by their orthogonal sum. -/
noncomputable def mergeAdjacent (k : Fin (n + 1)) :
    OrthogonalDecomposition q L (n + 1) where
  component := D.mergeComponents k
  orthogonal := by
    intro i j hij
    induction i using Fin.succAboveCases k with
    | x =>
        induction j using Fin.succAboveCases k with
        | x => exact (hij rfl).elim
        | p j =>
            have hfirst : k.castSucc ≠
                k.succ.succAbove (k.succAbove j) := by
              intro hEq
              have heq : k.succ.succAbove (k.succAbove j) =
                  k.succ.succAbove k :=
                hEq.symm.trans (Fin.succAbove_succ_self k).symm
              exact Fin.succAbove_ne k j
                (Fin.succAbove_right_injective heq)
            have hsecond : k.succ ≠
                k.succ.succAbove (k.succAbove j) :=
              Fin.ne_succAbove k.succ (k.succAbove j)
            rw [D.mergeComponents_self, D.mergeComponents_other]
            exact D.orthogonalSup_orthogonal_component
              k.castSucc_lt_succ.ne hfirst hsecond
    | p i =>
        induction j using Fin.succAboveCases k with
        | x =>
            have hfirst : k.succ.succAbove (k.succAbove i) ≠
                k.castSucc := by
              intro hEq
              have heq : k.succ.succAbove (k.succAbove i) =
                  k.succ.succAbove k :=
                hEq.trans (Fin.succAbove_succ_self k).symm
              exact Fin.succAbove_ne k i
                (Fin.succAbove_right_injective heq)
            have hsecond : k.succ.succAbove (k.succAbove i) ≠
                k.succ := Fin.succAbove_ne _ _
            rw [D.mergeComponents_other, D.mergeComponents_self]
            exact D.component_orthogonal_orthogonalSup
              k.castSucc_lt_succ.ne hfirst hsecond
        | p j =>
            have hindices : k.succ.succAbove (k.succAbove i) ≠
                k.succ.succAbove (k.succAbove j) := by
              intro hEq
              apply hij
              apply congrArg k.succAbove
              exact Fin.succAbove_right_injective
                (Fin.succAbove_right_injective hEq)
            rw [D.mergeComponents_other, D.mergeComponents_other]
            exact D.orthogonal (k.succ.succAbove (k.succAbove i))
              (k.succ.succAbove (k.succAbove j)) hindices
  sum_eq := (D.iSup_mergeComponents k).trans D.sum_eq

end OrthogonalDecomposition

end Lattice

end Bong
