/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularParameter
import Bong.Lattice.OrthogonalDecompositionMerge
import Bong.Lattice.RawJordanDecomposition

/-!
# Weak Jordan decompositions

O'Meara's recursive splitting first produces nonzero modular components with
nondecreasing scales.  This intermediate structure retains exactly the data
needed to amalgamate equal-scale neighbours.  Norm generators are chosen only
after amalgamation terminates.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- A modular orthogonal decomposition with nonzero components and
nondecreasing scales. -/
structure WeakJordanDecomposition (q : QuadraticSpace K V)
    (L : Lattice K V) (t : Nat) extends OrthogonalDecomposition q L t where
  scaleGenerator : Fin t → Kˣ
  modular : ∀ i, IsModular (component i).space (component i).lattice
    (scaleGenerator i)
  component_finrank_pos : ∀ i, 0 < finrank K (component i).carrier
  scaleOrder_mono : Monotone (fun i ↦ ordUnit K (scaleGenerator i))

namespace WeakJordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- Forget the unary-or-binary rank bound of a raw decomposition while
retaining positivity of every component rank. -/
noncomputable def ofRaw (R : RawJordanDecomposition q L t) :
    WeakJordanDecomposition q L t where
  toOrthogonalDecomposition := R.toOrthogonalDecomposition
  scaleGenerator := R.scaleGenerator
  modular := R.modular
  component_finrank_pos := by
    intro i
    rcases R.rank_one_or_two i with h | h <;> omega
  scaleOrder_mono := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact R.scaleOrder_mono h

variable {n : Nat} (W : WeakJordanDecomposition q L (n + 2))

/-- Amalgamate adjacent components having equal scale order. -/
noncomputable def mergeAdjacent (k : Fin (n + 1))
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    WeakJordanDecomposition q L (n + 1) where
  toOrthogonalDecomposition :=
    W.toOrthogonalDecomposition.mergeAdjacent k
  scaleGenerator := fun r ↦ W.scaleGenerator (k.succ.succAbove r)
  modular := by
    intro r
    induction r using Fin.succAboveCases k with
    | x =>
        change IsModular
          (W.toOrthogonalDecomposition.mergeComponents k k).space
          (W.toOrthogonalDecomposition.mergeComponents k k).lattice _
        rw [OrthogonalDecomposition.mergeComponents_self,
          Fin.succAbove_succ_self]
        exact OrthogonalDecomposition.IsModular.orthogonalSupComponents
          W.toOrthogonalDecomposition k.castSucc_lt_succ.ne
          (W.modular k.castSucc)
          ((W.modular k.succ).of_principalIdeal_eq
            ((principalIdeal_eq_iff_ordUnit_eq _ _).2 heq.symm))
    | p r =>
        change IsModular
          (W.toOrthogonalDecomposition.mergeComponents k
            (k.succAbove r)).space
          (W.toOrthogonalDecomposition.mergeComponents k
            (k.succAbove r)).lattice _
        rw [OrthogonalDecomposition.mergeComponents_other]
        exact W.modular _
  component_finrank_pos := by
    intro r
    induction r using Fin.succAboveCases k with
    | x =>
        change 0 < finrank K
          (W.toOrthogonalDecomposition.mergeComponents k k).carrier
        rw [OrthogonalDecomposition.mergeComponents_self]
        exact W.toOrthogonalDecomposition.orthogonalSup_finrank_pos_left
          k.castSucc_lt_succ.ne (W.component_finrank_pos k.castSucc)
    | p r =>
        change 0 < finrank K
          (W.toOrthogonalDecomposition.mergeComponents k
            (k.succAbove r)).carrier
        rw [OrthogonalDecomposition.mergeComponents_other]
        exact W.component_finrank_pos _
  scaleOrder_mono :=
    W.scaleOrder_mono.comp
      (Fin.strictMono_succAbove k.succ).monotone

end WeakJordanDecomposition

end Lattice

end Bong
