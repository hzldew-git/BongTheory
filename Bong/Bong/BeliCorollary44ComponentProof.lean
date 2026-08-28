/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44
import Bong.Bong.BinaryModularInvariant
import Bong.Bong.MaximalNormSplittingDual

/-!
# The component assertion in Beli (2003), Corollary 4.4(iii)

Across two components of a maximal norm splitting, the BONG orders cannot
drop.  Indeed, every component has rank one or is modular binary, so every
local order is at most the first local order.  The first local orders are the
chosen component norm orders, and these are nondecreasing.  Consequently a
strictly decreasing adjacent pair must lie in one component.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace Lattice.MaximalNormSplitting

open Lattice.OrthogonalDecomposition

/-- Every order in a unary or modular-binary component is at most its first
order. -/
theorem componentOrder_le_componentFirst
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    (c i).order j ≤ (c i).order (M.componentFirstIndex i) := by
  rcases M.unary_or_modular_binary i with h₁ | h₂
  · have hj : j = M.componentFirstIndex i := by
      apply Fin.ext
      change j.val = 0
      have hjlt : j.val < 1 := by
        simpa only [Lattice.OrthogonalDecomposition.componentRank, h₁] using
          j.isLt
      omega
    rw [hj]
  · let b₂ := (c i).castLength h₂.1
    have hjlt : j.val < 2 := by
      simpa only [Lattice.OrthogonalDecomposition.componentRank, h₂.1] using
        j.isLt
    have hjcases : j.val = 0 ∨ j.val = 1 := by omega
    rcases hjcases with hj | hj
    · have hindex : j = M.componentFirstIndex i := by
        apply Fin.ext
        simpa only [componentFirstIndex] using hj
      rw [hindex]
    · have hle := b₂.order_one_le_order_zero_of_isModular
          (M.scaleGenerator i) h₂.2
      have hindex : j =
          (⟨1, by simpa [Lattice.OrthogonalDecomposition.componentRank,
            h₂.1]⟩ : Fin
              (M.toOrthogonalDecomposition.componentRank i)) :=
        Fin.ext hj
      rw [hindex]
      simp only [b₂, BONG.order_castLength] at hle
      convert hle using 1 <;> congr

end Lattice.MaximalNormSplitting

namespace BONG.PutTogetherWitness

open Lattice.OrthogonalDecomposition

variable {b : BONG V q L n}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily}

/-- When two consecutive global indices cross a component boundary, the
second index is the first local index of its component. -/
theorem localIndex_succ_eq_zero_of_component_lt
    (w : PutTogetherWitness b D c)
    (i : Fin n) (hi : i.val + 1 < n)
    (hcomponent : w.componentIndex i <
      w.componentIndex ⟨i.val + 1, hi⟩) :
    (w.localIndex ⟨i.val + 1, hi⟩).val = 0 := by
  let next : Fin n := ⟨i.val + 1, hi⟩
  by_contra hzero
  have hpositive : 0 < (w.localIndex next).val := Nat.pos_of_ne_zero hzero
  let previousLocal : Fin (D.componentRank (w.componentIndex next)) :=
    ⟨(w.localIndex next).val - 1, by omega⟩
  let k : Fin n :=
    w.indexEquiv.symm ⟨w.componentIndex next, previousLocal⟩
  have hikLex : ComponentIndexBefore D (w.indexEquiv i) (w.indexEquiv k) := by
    change ComponentIndexBefore D (w.indexEquiv i)
      (w.indexEquiv (w.indexEquiv.symm
        ⟨w.componentIndex next, previousLocal⟩))
    rw [w.indexEquiv.apply_symm_apply]
    exact Or.inl hcomponent
  have hknLex : ComponentIndexBefore D (w.indexEquiv k)
      (w.indexEquiv next) := by
    change ComponentIndexBefore D
      (w.indexEquiv (w.indexEquiv.symm
        ⟨w.componentIndex next, previousLocal⟩))
      (w.indexEquiv next)
    rw [w.indexEquiv.apply_symm_apply]
    refine Or.inr ⟨rfl, ?_⟩
    change (w.localIndex next).val - 1 < (w.localIndex next).val
    omega
  have hik : i < k := (w.order_iff i k).2 hikLex
  have hkn : k < next := (w.order_iff k next).2 hknLex
  change i.val < k.val at hik
  change k.val < i.val + 1 at hkn
  omega

end BONG.PutTogetherWitness

namespace BONG

open Lattice.OrthogonalDecomposition

/-- Beli (2003), Corollary 4.4(iii), proved from the defining inequalities of
a maximal norm splitting. -/
theorem beliCorollary44_iii_unconditional
    (b : BONG V q L n)
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (hconcat : b.IsPutTogether M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.val + 1 < n)
    (horder : b.order ⟨i.val + 1, hi⟩ < b.order i) :
    b.AdjacentPairIsOneComponent M c i hi := by
  rcases hconcat with ⟨w⟩
  refine ⟨w, ?_⟩
  let next : Fin n := ⟨i.val + 1, hi⟩
  have hinext : i < next := by
    change i.val < i.val + 1
    omega
  have hlex := (w.order_iff i next).1 hinext
  rcases hlex with hcomponent | hsame
  · have hnextZero :=
        w.localIndex_succ_eq_zero_of_component_lt i hi hcomponent
    have hnextFirst : w.localIndex next =
        M.componentFirstIndex (w.componentIndex next) := by
      apply Fin.ext
      simpa only [Lattice.MaximalNormSplitting.componentFirstIndex] using
        hnextZero
    have hnormMono : ordUnit K (M.normGenerator (w.componentIndex i)) ≤
        ordUnit K (M.normGenerator (w.componentIndex next)) := by
      have hgap : 0 ≤ ordUnit K (M.normGenerator (w.componentIndex next)) -
          ordUnit K (M.normGenerator (w.componentIndex i)) := by
        simpa only [PutTogetherWitness.componentIndex] using
          (M.normGap_bounds hcomponent).1
      omega
    have hnotDrop : b.order i ≤ b.order next := by
      calc
        b.order i = (c (w.componentIndex i)).order (w.localIndex i) :=
          w.order_eq i
        _ ≤ (c (w.componentIndex i)).order
            (M.componentFirstIndex (w.componentIndex i)) :=
          M.componentOrder_le_componentFirst c _ _
        _ = ordUnit K (M.normGenerator (w.componentIndex i)) :=
          M.componentFirst_order_eq_normGeneratorOrder c _
        _ ≤ ordUnit K (M.normGenerator (w.componentIndex next)) := hnormMono
        _ = (c (w.componentIndex next)).order
            (M.componentFirstIndex (w.componentIndex next)) :=
          (M.componentFirst_order_eq_normGeneratorOrder c _).symm
        _ = (c (w.componentIndex next)).order (w.localIndex next) := by
          rw [hnextFirst]
        _ = b.order next := (w.order_eq next).symm
    exact (not_lt_of_ge hnotDrop horder).elim
  · exact hsame.1

end BONG

end Bong
