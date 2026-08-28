/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.ModularSplitting
import Bong.Lattice.OrthogonalDecompositionTail

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace OrthogonalDecomposition

/-- Exchange the two blocks of a two-block orthogonal decomposition. -/
noncomputable abbrev swapPair (P : OrthogonalDecomposition q L 2) :
    OrthogonalDecomposition q L 2 where
  component := Fin.cases (P.component 1) (fun _ => P.component 0)
  orthogonal := by
    intro i j hij x y
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact P.orthogonal 1 0 (by decide) x y
    · exact P.orthogonal 0 1 (by decide) x y
    · exact (hij rfl).elim
  sum_eq := by
    rw [iSup_fin_two_eq_sup_tail]
    change (P.component 1).ambientSubmodule ⊔
      (P.component 0).ambientSubmodule = L.toSubmodule
    rw [_root_.sup_comm]
    simpa only [iSup_fin_two_eq_sup_tail] using P.sum_eq

@[simp]
theorem swapPair_zero (P : OrthogonalDecomposition q L 2) :
    P.swapPair.component 0 = P.component 1 :=
  by rfl

@[simp]
theorem swapPair_one (P : OrthogonalDecomposition q L 2) :
    P.swapPair.component 1 = P.component 0 :=
  by rfl

/-- Flatten a decomposition inside the first block of a two-block splitting,
placing the untouched second block last. -/
noncomputable def appendNested
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 0).space
      (P.component 0).lattice t) :
    OrthogonalDecomposition q L (t + 1) := by
  let D' : OrthogonalDecomposition (P.swapPair.component 1).space
      (P.swapPair.component 1).lattice t := by
    change OrthogonalDecomposition (P.component 0).space
      (P.component 0).lattice t
    exact D
  let R := P.swapPair.prependNested D'
  exact R.reindex (ModularDecomposition.distinguishedLastTie t).symm

@[simp]
theorem appendNested_last
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 0).space
      (P.component 0).lattice t) :
    (P.appendNested D).component (Fin.last t) = P.component 1 := by
  unfold appendNested
  simp [ModularDecomposition.distinguishedLastTie]
  change P.swapPair.component 0 = P.component 1
  rfl

@[simp]
theorem appendNested_castSucc
    (P : OrthogonalDecomposition q L 2)
    (D : OrthogonalDecomposition (P.component 0).space
      (P.component 0).lattice t) (i : Fin t) :
    (P.appendNested D).component i.castSucc =
      (P.component 0).liftNested (D.component i) := by
  unfold appendNested
  simp [ModularDecomposition.distinguishedLastTie]
  change (P.swapPair.component 1).liftNested (D.component i) =
    (P.component 0).liftNested (D.component i)
  rfl

end OrthogonalDecomposition

end Lattice

end Bong
