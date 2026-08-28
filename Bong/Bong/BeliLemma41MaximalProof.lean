/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41ProductModel

/-!
# Beli (2003), Lemma 4.1(i)

This file closes the maximal-norm-splitting half of Lemma 4.1.  The component
BONGs are concatenated in the coordinate product, then transported through the
canonical integral isometry associated with the orthogonal decomposition.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace BONG

open Lattice.OrthogonalDecomposition

/-- Beli (2003), Lemma 4.1(i), with no local-law parameter. -/
theorem maximalNorm_putTogether_proof
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily) :
    ∃ b : BONG V q L (finrank K V),
      b.IsPutTogether M.toOrthogonalDecomposition c := by
  letI : Module.Finite K V := L.moduleFinite
  cases t with
  | zero =>
      let D := M.toOrthogonalDecomposition
      have hfin : finrank K V = 0 := by
        rw [Module.finrank_eq_card_basis D.componentAmbientBasis]
        simp
      have hV : Subsingleton V := Module.finrank_zero_iff.mp hfin
      let b : BONG V q L (finrank K V) :=
        (BONG.nil q L hV).castLength hfin.symm
      let e : Fin (finrank K V) ≃
          Σ i : Fin 0, Fin (D.componentRank i) :=
        { toFun := fun i ↦ Fin.elim0 (Fin.cast hfin i)
          invFun := fun a ↦ Fin.elim0 a.1
          left_inv := fun i ↦ Fin.elim0 (Fin.cast hfin i)
          right_inv := fun a ↦ Fin.elim0 a.1 }
      refine ⟨b, ⟨{
        indexEquiv := e
        order_iff := ?_
        ambientVector_eq := ?_
      }⟩⟩
      · intro i
        exact Fin.elim0 (Fin.cast hfin i)
      · intro i
        exact Fin.elim0 (Fin.cast hfin i)
  | succ n =>
      let D := M.toOrthogonalDecomposition
      let ranks : Fin (n + 1) → Nat := fun i ↦ D.componentRank i
      have hrank : ∀ i, 0 < ranks i := by
        intro i
        exact M.componentRank_pos i
      have hcross : ∀ {i j : Fin (n + 1)}, i < j →
          ∀ k : Fin (ranks i),
            (c i).order k ≤ (c j).order ⟨0, hrank j⟩ := by
        intro i j hij k
        simpa only [ranks,
          Lattice.MaximalNormSplitting.componentFirstIndex] using
          M.component_order_le_later_first c hij k
      let w := BlockBONGWitness.ofFamily n
        (fun i ↦ (D.component i).carrier)
        (fun i ↦ (D.component i).space)
        (fun i ↦ (D.component i).lattice)
        ranks c hrank hcross
      let iso := orthogonalDecompositionProductIsometry D
      let raw := w.bong.mapLatticeIsometry iso
      have hlength : blockTotalRank n ranks = finrank K V :=
        raw.length_eq_finrank
      let b : BONG V q L (finrank K V) := raw.castLength hlength
      let e : Fin (finrank K V) ≃
          Σ i : Fin (n + 1), Fin (D.componentRank i) :=
        (finCongr hlength).symm.trans w.indexEquiv
      refine ⟨b, ⟨{
        indexEquiv := e
        order_iff := ?_
        ambientVector_eq := ?_
      }⟩⟩
      · intro i j
        let ii : Fin (blockTotalRank n ranks) :=
          (finCongr hlength).symm i
        let jj : Fin (blockTotalRank n ranks) :=
          (finCongr hlength).symm j
        change i.val < j.val ↔
          BlockIndexBefore (w.indexEquiv ii) (w.indexEquiv jj)
        change ii.val < jj.val ↔
          BlockIndexBefore (w.indexEquiv ii) (w.indexEquiv jj)
        exact w.order_iff ii jj
      · intro i
        let ii : Fin (blockTotalRank n ranks) :=
          (finCongr hlength).symm i
        rw [show b = raw.castLength hlength by rfl,
          BONG.ambientVector_castLength]
        change raw.ambientVector ii = _
        rw [show raw = w.bong.mapLatticeIsometry iso by rfl,
          BONG.ambientVector_mapLatticeIsometry, w.ambientVector_eq]
        change
          orthogonalDecompositionProductLinearEquiv D
            (Pi.single (w.indexEquiv ii).1
              ((c (w.indexEquiv ii).1).ambientVector
                (w.indexEquiv ii).2)) = _
        rw [orthogonalDecompositionProductLinearEquiv_single]
        rfl

end BONG

end Bong
