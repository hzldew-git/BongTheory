/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41MaximalProof
import Bong.Bong.BeliCorollary44ComponentProof
import Bong.Lattice.RankOneNormScale

/-!
# Beli (2003), Corollary 4.2(ii)

The last orders of the blocks in a maximal norm splitting are nondecreasing.
This is the reverse-dual counterpart of monotonicity of the first orders.  It
supplies the only nontrivial boundary case in the proof that a concatenated
component BONG is good.
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

variable (M : Lattice.MaximalNormSplitting q L t)
  (c : M.toOrthogonalDecomposition.ComponentBONGFamily)

/-- The last local index of a nonzero component. -/
noncomputable def componentLastIndex (i : Fin t) :
    Fin (M.toOrthogonalDecomposition.componentRank i) :=
  ⟨M.toOrthogonalDecomposition.componentRank i - 1, by
    exact Nat.sub_lt (M.componentRank_pos i) Nat.zero_lt_one⟩

/-- The chosen last index really has the largest possible value. -/
theorem componentLastIndex_val (i : Fin t) :
    (M.componentLastIndex i).val + 1 =
      M.toOrthogonalDecomposition.componentRank i := by
  rw [componentLastIndex]
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (M.componentRank_pos i))

/-- The last order of a unary or modular-binary component is
`2 ord(scale) - ord(norm)`. -/
theorem componentLast_order_eq (i : Fin t) :
    (c i).order (M.componentLastIndex i) =
      2 * ordUnit K (M.scaleGenerator i) -
        ordUnit K (M.normGenerator i) := by
  rcases M.componentRank_eq_one_or_two i with hOne | hTwo
  · have hlast : M.componentLastIndex i = M.componentFirstIndex i := by
      apply Fin.ext
      change M.componentRank i - 1 = 0
      rw [hOne]
    rw [hlast, M.componentFirst_order_eq_normGeneratorOrder c]
    have hnormScale :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (M.toOrthogonalDecomposition.component i).space
        (M.toOrthogonalDecomposition.component i).lattice
        (M.scaleGenerator i) (M.normGenerator i) hOne
        (M.component_isModular c i) (M.normIdeal_eq i)
    omega
  · let bTwo := (c i).castLength hTwo
    have hformula := bTwo.order_one_eq_of_isModular
      (M.scaleGenerator i) (M.component_isModular c i)
    let oneOriginal : Fin (M.componentRank i) := ⟨1, by
      rw [hTwo]
      omega⟩
    let zeroOriginal : Fin (M.componentRank i) := ⟨0, M.componentRank_pos i⟩
    have hone : oneOriginal = M.componentLastIndex i := by
      apply Fin.ext
      change 1 = M.componentRank i - 1
      rw [hTwo]
    have hzero : zeroOriginal = M.componentFirstIndex i := by
      apply Fin.ext
      rfl
    have hcastOne : bTwo.order (1 : Fin 2) =
        (c i).order oneOriginal := by
      have h := BONG.order_castLength (c i) hTwo (1 : Fin 2)
      change bTwo.order (1 : Fin 2) = (c i).order oneOriginal at h
      exact h
    have hcastZero : bTwo.order (0 : Fin 2) =
        (c i).order zeroOriginal := by
      have h := BONG.order_castLength (c i) hTwo (0 : Fin 2)
      change bTwo.order (0 : Fin 2) = (c i).order zeroOriginal at h
      exact h
    calc
      (c i).order (M.componentLastIndex i) = bTwo.order 1 := by
        rw [← hone, ← hcastOne]
      _ = 2 * ordUnit K (M.scaleGenerator i) - bTwo.order 0 := hformula
      _ = 2 * ordUnit K (M.scaleGenerator i) -
          (c i).order (M.componentFirstIndex i) := by
        rw [hcastZero, hzero]
      _ = 2 * ordUnit K (M.scaleGenerator i) -
          ordUnit K (M.normGenerator i) := by
        rw [M.componentFirst_order_eq_normGeneratorOrder c]

/-- Last component orders are nondecreasing. -/
theorem componentLast_order_mono {i j : Fin t} (hij : i < j) :
    (c i).order (M.componentLastIndex i) ≤
      (c j).order (M.componentLastIndex j) := by
  rw [M.componentLast_order_eq c i, M.componentLast_order_eq c j]
  have hgap := (M.normGap_bounds hij).2
  omega

end Lattice.MaximalNormSplitting

namespace BONG.PutTogetherWitness

open Lattice.OrthogonalDecomposition

variable {b : BONG V q L n}
  {M : Lattice.MaximalNormSplitting q L t}
  {c : M.toOrthogonalDecomposition.ComponentBONGFamily}

/-- Immediately before a component boundary, the local coordinate is the
last coordinate of its component. -/
theorem localIndex_eq_componentLast_of_component_lt_succ
    (w : PutTogetherWitness b M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.val + 1 < n)
    (hcomponent : w.componentIndex i <
      w.componentIndex ⟨i.val + 1, hi⟩) :
    w.localIndex i = M.componentLastIndex (w.componentIndex i) := by
  apply Fin.ext
  by_contra hne
  have hstep : (w.localIndex i).val + 1 <
      M.toOrthogonalDecomposition.componentRank (w.componentIndex i) := by
    have hlocal := (w.localIndex i).isLt
    have hlast := M.componentLastIndex_val (w.componentIndex i)
    omega
  let next : Fin n := ⟨i.val + 1, hi⟩
  let nextLocal : Fin
      (M.toOrthogonalDecomposition.componentRank (w.componentIndex i)) :=
    ⟨(w.localIndex i).val + 1, hstep⟩
  let k : Fin n := w.indexEquiv.symm
    ⟨w.componentIndex i, nextLocal⟩
  have hikLex : ComponentIndexBefore M.toOrthogonalDecomposition
      (w.indexEquiv i) (w.indexEquiv k) := by
    change ComponentIndexBefore M.toOrthogonalDecomposition
      (w.indexEquiv i)
      (w.indexEquiv (w.indexEquiv.symm
        ⟨w.componentIndex i, nextLocal⟩))
    rw [w.indexEquiv.apply_symm_apply]
    exact Or.inr ⟨rfl, by
      change (w.localIndex i).val < (w.localIndex i).val + 1
      omega⟩
  have hknLex : ComponentIndexBefore M.toOrthogonalDecomposition
      (w.indexEquiv k) (w.indexEquiv next) := by
    change ComponentIndexBefore M.toOrthogonalDecomposition
      (w.indexEquiv (w.indexEquiv.symm
        ⟨w.componentIndex i, nextLocal⟩))
      (w.indexEquiv next)
    rw [w.indexEquiv.apply_symm_apply]
    exact Or.inl hcomponent
  have hik : i < k := (w.order_iff i k).2 hikLex
  have hkn : k < next := (w.order_iff k next).2 hknLex
  change i.val < k.val at hik
  change k.val < i.val + 1 at hkn
  omega

end BONG.PutTogetherWitness

namespace BONG

open Lattice.OrthogonalDecomposition

/-- Beli (2003), Corollary 4.2(ii), with no local-law parameter. -/
theorem maximalNorm_putTogether_isGood_proof
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (hb : b.IsPutTogether M.toOrthogonalDecomposition c) : b.IsGood := by
  rcases hb with ⟨w⟩
  intro i hi
  let middle : Fin n := ⟨i.val + 1, by omega⟩
  let last : Fin n := ⟨i.val + 2, hi⟩
  have him : i < middle := by
    change i.val < i.val + 1
    omega
  have hml : middle < last := by
    change i.val + 1 < i.val + 2
    omega
  have hmiddleLast := (w.order_iff middle last).1 hml
  rcases hmiddleLast with hcross | hsame
  · have hmiddleBound : middle.val + 1 < n := by
      dsimp only [middle]
      omega
    have hzeroRaw := w.localIndex_succ_eq_zero_of_component_lt
      middle hmiddleBound hcross
    have hnextEq :
        (⟨middle.val + 1, hmiddleBound⟩ : Fin n) = last := by
      apply Fin.ext
      simp [middle, last]
    rw [hnextEq] at hzeroRaw
    have hlastFirst : w.localIndex last =
        M.componentFirstIndex (w.componentIndex last) := by
      apply Fin.ext
      simpa only [Lattice.MaximalNormSplitting.componentFirstIndex] using
        hzeroRaw
    have hil := (w.order_iff i last).1 (him.trans hml)
    have hcomponent : w.componentIndex i < w.componentIndex last := by
      rcases hil with hlt | hsameIL
      · exact hlt
      · have hlocal := hsameIL.2
        change (w.localIndex i).val < (w.localIndex last).val at hlocal
        rw [hlastFirst] at hlocal
        change (w.localIndex i).val < 0 at hlocal
        omega
    calc
      b.order i = (c (w.componentIndex i)).order (w.localIndex i) :=
        w.order_eq i
      _ ≤ (c (w.componentIndex last)).order
          (M.componentFirstIndex (w.componentIndex last)) :=
        M.component_order_le_later_first c hcomponent (w.localIndex i)
      _ = (c (w.componentIndex last)).order (w.localIndex last) := by
        rw [hlastFirst]
      _ = b.order last := (w.order_eq last).symm
  · have hmiddleZero : (w.localIndex middle).val = 0 := by
      have hlastLt := (w.localIndex last).isLt
      have hcomponentRank :
          M.toOrthogonalDecomposition.componentRank
              (w.componentIndex last) ≤ 2 := by
        simpa only [Lattice.MaximalNormSplitting.componentRank,
          Lattice.OrthogonalDecomposition.componentRank] using
          M.componentRank_le_two (w.componentIndex last)
      have hlocalLt := hsame.2
      change (w.localIndex middle).val < (w.localIndex last).val at hlocalLt
      omega
    have himLex := (w.order_iff i middle).1 him
    have hcomponent : w.componentIndex i < w.componentIndex middle := by
      rcases himLex with hlt | hsameIM
      · exact hlt
      · have hlocal := hsameIM.2
        change (w.localIndex i).val < (w.localIndex middle).val at hlocal
        rw [hmiddleZero] at hlocal
        omega
    have hiLast := w.localIndex_eq_componentLast_of_component_lt_succ
      i (by omega) hcomponent
    have hsameComponent : w.componentIndex middle =
        w.componentIndex last := hsame.1
    have hlastIndex : w.localIndex last =
        M.componentLastIndex (w.componentIndex last) := by
      apply Fin.ext
      change (w.localIndex last).val =
        (M.componentLastIndex (w.componentIndex last)).val
      have hlastVal := M.componentLastIndex_val (w.componentIndex last)
      have hrankLe :
          M.toOrthogonalDecomposition.componentRank
              (w.componentIndex last) ≤ 2 := by
        simpa only [Lattice.MaximalNormSplitting.componentRank,
          Lattice.OrthogonalDecomposition.componentRank] using
          M.componentRank_le_two (w.componentIndex last)
      have hlocalLt := hsame.2
      change (w.localIndex middle).val < (w.localIndex last).val at hlocalLt
      have hlastLt := (w.localIndex last).isLt
      omega
    calc
      b.order i = (c (w.componentIndex i)).order (w.localIndex i) :=
        w.order_eq i
      _ = (c (w.componentIndex i)).order
          (M.componentLastIndex (w.componentIndex i)) := by rw [hiLast]
      _ ≤ (c (w.componentIndex last)).order
          (M.componentLastIndex (w.componentIndex last)) := by
        apply M.componentLast_order_mono c
        exact hcomponent.trans_eq hsameComponent
      _ = (c (w.componentIndex last)).order (w.localIndex last) := by
        rw [hlastIndex]
      _ = b.order last := (w.order_eq last).symm

/-- Beli (2003), Corollary 4.2(i), for a BONG already displayed as the
concatenation of the blocks of a property-A Jordan decomposition.  This is
the strict counterpart of `maximalNorm_putTogether_isGood_proof`. -/
theorem jordanPropertyA_putTogether_hasPropertyA_proof
    (J : Lattice.JordanDecomposition q L t) (hJ : J.HasPropertyA)
    (c : J.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (hb : b.IsPutTogether J.toOrthogonalDecomposition c) :
    b.HasPropertyA := by
  let M := Lattice.MaximalNormSplitting.ofJordanPropertyA J hJ
  let cM : M.toOrthogonalDecomposition.ComponentBONGFamily := c
  have hbM : b.IsPutTogether M.toOrthogonalDecomposition cM := by
    change b.IsPutTogether J.toOrthogonalDecomposition c
    exact hb
  rcases hbM with ⟨w⟩
  intro i hi
  let middle : Fin n := ⟨i.val + 1, by omega⟩
  let last : Fin n := ⟨i.val + 2, hi⟩
  have him : i < middle := by
    change i.val < i.val + 1
    omega
  have hml : middle < last := by
    change i.val + 1 < i.val + 2
    omega
  have hmiddleLast := (w.order_iff middle last).1 hml
  rcases hmiddleLast with hcross | hsame
  · have hmiddleBound : middle.val + 1 < n := by
      dsimp only [middle]
      omega
    have hzeroRaw := w.localIndex_succ_eq_zero_of_component_lt
      middle hmiddleBound hcross
    have hnextEq :
        (⟨middle.val + 1, hmiddleBound⟩ : Fin n) = last := by
      apply Fin.ext
      simp [middle, last]
    rw [hnextEq] at hzeroRaw
    have hlastFirst : w.localIndex last =
        M.componentFirstIndex (w.componentIndex last) := by
      apply Fin.ext
      simpa only [Lattice.MaximalNormSplitting.componentFirstIndex] using
        hzeroRaw
    have hil := (w.order_iff i last).1 (him.trans hml)
    have hcomponent : w.componentIndex i < w.componentIndex last := by
      rcases hil with hlt | hsameIL
      · exact hlt
      · have hlocal := hsameIL.2
        change (w.localIndex i).val < (w.localIndex last).val at hlocal
        rw [hlastFirst] at hlocal
        change (w.localIndex i).val < 0 at hlocal
        omega
    calc
      b.order i = (cM (w.componentIndex i)).order (w.localIndex i) :=
        w.order_eq i
      _ ≤ ordUnit K (M.normGenerator (w.componentIndex i)) :=
        M.component_order_le_normGeneratorOrder cM
          (w.componentIndex i) (w.localIndex i)
      _ < ordUnit K (M.normGenerator (w.componentIndex last)) := by
        have hgap := (hJ.2 hcomponent).1
        change 0 < ordUnit K (M.normGenerator (w.componentIndex last)) -
          ordUnit K (M.normGenerator (w.componentIndex i)) at hgap
        omega
      _ = (cM (w.componentIndex last)).order
          (M.componentFirstIndex (w.componentIndex last)) :=
        (M.componentFirst_order_eq_normGeneratorOrder cM
          (w.componentIndex last)).symm
      _ = (cM (w.componentIndex last)).order (w.localIndex last) := by
        rw [hlastFirst]
      _ = b.order last := (w.order_eq last).symm
  · have hmiddleZero : (w.localIndex middle).val = 0 := by
      have hlastLt := (w.localIndex last).isLt
      have hcomponentRank :
          M.toOrthogonalDecomposition.componentRank
              (w.componentIndex last) ≤ 2 := by
        simpa only [Lattice.MaximalNormSplitting.componentRank,
          Lattice.OrthogonalDecomposition.componentRank] using
          M.componentRank_le_two (w.componentIndex last)
      have hlocalLt := hsame.2
      change (w.localIndex middle).val < (w.localIndex last).val at hlocalLt
      omega
    have himLex := (w.order_iff i middle).1 him
    have hcomponent : w.componentIndex i < w.componentIndex middle := by
      rcases himLex with hlt | hsameIM
      · exact hlt
      · have hlocal := hsameIM.2
        change (w.localIndex i).val < (w.localIndex middle).val at hlocal
        rw [hmiddleZero] at hlocal
        omega
    have hiLast := w.localIndex_eq_componentLast_of_component_lt_succ
      i (by omega) hcomponent
    have hsameComponent : w.componentIndex middle =
        w.componentIndex last := hsame.1
    have hlastIndex : w.localIndex last =
        M.componentLastIndex (w.componentIndex last) := by
      apply Fin.ext
      change (w.localIndex last).val =
        (M.componentLastIndex (w.componentIndex last)).val
      have hlastVal := M.componentLastIndex_val (w.componentIndex last)
      have hrankLe :
          M.toOrthogonalDecomposition.componentRank
              (w.componentIndex last) ≤ 2 := by
        simpa only [Lattice.MaximalNormSplitting.componentRank,
          Lattice.OrthogonalDecomposition.componentRank] using
          M.componentRank_le_two (w.componentIndex last)
      have hlocalLt := hsame.2
      change (w.localIndex middle).val < (w.localIndex last).val at hlocalLt
      have hlastLt := (w.localIndex last).isLt
      omega
    calc
      b.order i = (cM (w.componentIndex i)).order (w.localIndex i) :=
        w.order_eq i
      _ = (cM (w.componentIndex i)).order
          (M.componentLastIndex (w.componentIndex i)) := by rw [hiLast]
      _ < (cM (w.componentIndex last)).order
          (M.componentLastIndex (w.componentIndex last)) := by
        rw [M.componentLast_order_eq cM (w.componentIndex i),
          M.componentLast_order_eq cM (w.componentIndex last)]
        have hindex : w.componentIndex i < w.componentIndex last :=
          hcomponent.trans_eq hsameComponent
        have hgap := (hJ.2 hindex).2
        change ordUnit K (M.normGenerator (w.componentIndex last)) -
              ordUnit K (M.normGenerator (w.componentIndex i)) <
            2 * (ordUnit K (M.scaleGenerator (w.componentIndex last)) -
              ordUnit K (M.scaleGenerator (w.componentIndex i))) at hgap
        omega
      _ = (cM (w.componentIndex last)).order (w.localIndex last) := by
        rw [hlastIndex]
      _ = b.order last := (w.order_eq last).symm

end BONG

end Bong
