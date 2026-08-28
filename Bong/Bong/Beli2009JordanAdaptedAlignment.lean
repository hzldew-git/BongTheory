/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanAdaptedAmalgamation

/-!
# Adapted strict Jordan alignment for Beli (2009)

This file retains actual component BONGs and their ambient put-together
witnesses throughout synchronous equal-scale Jordan amalgamation.  It upgrades
the endpoint-only alignment to the concrete data required by Beli's weight,
fundamental-ideal, defect, and representation arguments.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

namespace PutTogetherWitness

variable {b : BONG V q L n} {t : Nat}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily}

/-- At a specified component coordinate, the global order is the local
component order.  Unlike the earlier maximal-norm version, this statement
only uses the exact put-together witness and therefore survives Jordan
amalgamation. -/
theorem order_inverse_indexEquiv_general
    (h : PutTogetherWitness b D c) (i : Fin t)
    (j : Fin (D.componentRank i)) :
    b.order (h.indexEquiv.symm ⟨i, j⟩) = (c i).order j := by
  rw [b.order_eq_ordUnit, (c i).order_eq_ordUnit]
  congr 1
  apply Units.ext
  simp only [BONG.coe_valueUnit]
  have hv := h.ambientVector_eq (h.indexEquiv.symm ⟨i, j⟩)
  have heq : h.indexEquiv (h.indexEquiv.symm ⟨i, j⟩) = ⟨i, j⟩ :=
    h.indexEquiv.apply_symm_apply ⟨i, j⟩
  change b.value (h.indexEquiv.symm ⟨i, j⟩) = _
  rw [← b.quadratic_ambientVector,
    ← (c i).quadratic_ambientVector]
  rw [heq] at hv
  exact congrArg q.quadratic hv

/-- Every component BONG in an exact ordered concatenation of a good BONG is
itself good.  This is the hereditary step needed after equal-scale Jordan
components have been amalgamated. -/
theorem componentBONG_isGood
    (h : PutTogetherWitness b D c) (hb : b.IsGood) (i : Fin t) :
    (c i).IsGood := by
  intro j hj
  let j2 : Fin (D.componentRank i) := ⟨j.val + 2, hj⟩
  let g0 : Fin n := h.indexEquiv.symm ⟨i, j⟩
  let g2 : Fin n := h.indexEquiv.symm ⟨i, j2⟩
  have hv0 : g0.val =
      (∑ k ∈ Finset.Iio i, D.componentRank k) + j.val := by
    dsimp only [g0]
    exact h.inverse_index_val i j
  have hv2 : g2.val =
      (∑ k ∈ Finset.Iio i, D.componentRank k) + (j.val + 2) := by
    dsimp only [g2, j2]
    exact h.inverse_index_val i ⟨j.val + 2, hj⟩
  have hg2val : g0.val + 2 = g2.val := by
    omega
  have hbound : g0.val + 2 < n := by
    rw [hg2val]
    exact g2.isLt
  have hglobal := hb g0 hbound
  have hg2 : (⟨g0.val + 2, hbound⟩ : Fin n) = g2 :=
    Fin.ext hg2val
  calc
    (c i).order j = b.order g0 :=
      (h.order_inverse_indexEquiv_general i j).symm
    _ ≤ b.order ⟨g0.val + 2, hbound⟩ := hglobal
    _ = b.order g2 := congrArg b.order hg2
    _ = (c i).order j2 := h.order_inverse_indexEquiv_general i j2

end PutTogetherWitness

@[simp] theorem mergeComponentBONGFamily_order_left {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (i : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc)) :
    (mergeComponentBONGFamily W c hlocal hhead k heq hnorm k).order
        (mergeComponentLeftIndex W k heq i) = (c k.castSucc).order i := by
  rw [mergeComponentBONGFamily_self]
  change (mergeComponentBONG W c hlocal hhead k heq hnorm).order
    ⟨i.val, by
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      exact Nat.lt_add_right _ i.isLt⟩ = _
  exact mergeComponentBONG_order_left W c hlocal hhead k heq hnorm i

@[simp] theorem mergeComponentBONGFamily_order_right {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (j : Fin (W.toOrthogonalDecomposition.componentRank k.succ)) :
    (mergeComponentBONGFamily W c hlocal hhead k heq hnorm k).order
        (mergeComponentRightIndex W k heq j) = (c k.succ).order j := by
  rw [mergeComponentBONGFamily_self]
  change (mergeComponentBONG W c hlocal hhead k heq hnorm).order
    ⟨W.toOrthogonalDecomposition.componentRank k.castSucc + j.val, by
      have hjlt := j.isLt
      simp only [Lattice.OrthogonalDecomposition.componentRank] at hjlt ⊢
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      omega⟩ = _
  exact mergeComponentBONG_order_right W c hlocal hhead k heq hnorm j

/-- A weak Jordan decomposition whose component BONGs literally concatenate
to the original ambient BONG.  The two order conditions are precisely what is
needed to preserve this data through equal-scale amalgamation. -/
structure WeakJordanAdaptedWitness (b : BONG V q L n) {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t) where
  componentBONG : W.toOrthogonalDecomposition.ComponentBONGFamily
  putTogether : PutTogetherWitness b W.toOrthogonalDecomposition componentBONG
  local_order_le_head : ∀ i j, (componentBONG i).order j ≤
    (componentBONG i).order (weakComponentHeadIndex W i)
  head_order_eq_norm : ∀ i,
    (componentBONG i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i)

namespace WeakJordanAdaptedWitness

variable {b : BONG V q L n} {t : Nat}
  {W : Lattice.WeakJordanDecomposition q L t}

/-- The concrete BONG carried by every adapted Jordan component is good as
soon as the original global BONG is good. -/
theorem componentBONG_isGood
    (A : WeakJordanAdaptedWitness b W) (hb : b.IsGood) (i : Fin t) :
    (A.componentBONG i).IsGood :=
  A.putTogether.componentBONG_isGood hb i

/-- Package an adapted Jordan component as an actual good BONG. -/
noncomputable def componentGoodBONG
    (A : WeakJordanAdaptedWitness b W) (hb : b.IsGood) (i : Fin t) :
    GoodBONG (W.component i).space (W.component i).lattice
      (finrank K (W.component i).carrier) where
  toBONG := A.componentBONG i
  good := A.componentBONG_isGood hb i

noncomputable def mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (A : WeakJordanAdaptedWitness b W)
    (E : WeakJordanEndpointWitness b W)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    WeakJordanAdaptedWitness b (W.mergeAdjacentAt k heq) := by
  let hnorm := E.normOrder_eq_of_scaleOrder_eq k.castSucc k.succ heq
  let c' := mergeComponentBONGFamily W A.componentBONG
    A.local_order_le_head A.head_order_eq_norm k heq hnorm
  have hlocal' : ∀ i j, (c' i).order j ≤
      (c' i).order (weakComponentHeadIndex (W.mergeAdjacentAt k heq) i) := by
    intro i j
    by_cases hik : i = k
    · subst i
      have hrank := W.mergeAdjacentAt_componentRank_self k heq
      by_cases hj : j.val < W.toOrthogonalDecomposition.componentRank k.castSucc
      · let old : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc) :=
          ⟨j.val, hj⟩
        have hindex : j = mergeComponentLeftIndex W k heq old := Fin.ext rfl
        have hheadIndex : weakComponentHeadIndex (W.mergeAdjacentAt k heq) k =
            mergeComponentLeftIndex W k heq
              (weakComponentHeadIndex W k.castSucc) := Fin.ext rfl
        rw [hindex, hheadIndex]
        dsimp only [c']
        rw [mergeComponentBONGFamily_order_left,
          mergeComponentBONGFamily_order_left]
        exact A.local_order_le_head k.castSucc old
      · have hjRightBound : j.val -
            W.toOrthogonalDecomposition.componentRank k.castSucc <
            W.toOrthogonalDecomposition.componentRank k.succ := by
          have hjBound := j.isLt
          simp only [Lattice.OrthogonalDecomposition.componentRank] at hj hjBound ⊢
          omega
        let old : Fin (W.toOrthogonalDecomposition.componentRank k.succ) :=
          ⟨j.val - W.toOrthogonalDecomposition.componentRank k.castSucc,
            hjRightBound⟩
        have hindex : j = mergeComponentRightIndex W k heq old := by
          apply Fin.ext
          dsimp only [mergeComponentRightIndex, old]
          omega
        have hheadIndex : weakComponentHeadIndex (W.mergeAdjacentAt k heq) k =
            mergeComponentLeftIndex W k heq
              (weakComponentHeadIndex W k.castSucc) := Fin.ext rfl
        rw [hindex, hheadIndex]
        dsimp only [c']
        rw [mergeComponentBONGFamily_order_right,
          mergeComponentBONGFamily_order_left]
        calc
          (A.componentBONG k.succ).order old ≤
              (A.componentBONG k.succ).order
                (weakComponentHeadIndex W k.succ) :=
            A.local_order_le_head k.succ old
          _ = ordUnit K (W.normGeneratorUnit k.succ) :=
            A.head_order_eq_norm k.succ
          _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hnorm.symm
          _ = (A.componentBONG k.castSucc).order
                (weakComponentHeadIndex W k.castSucc) :=
            (A.head_order_eq_norm k.castSucc).symm
    · dsimp only [c']
      rw [mergeComponentBONGFamily_of_ne W A.componentBONG
        A.local_order_le_head A.head_order_eq_norm k heq hnorm i hik]
      rw [BONG.order_castLength, BONG.order_castLength,
        BONG.order_castQuadraticSublattice,
        BONG.order_castQuadraticSublattice]
      exact A.local_order_le_head (k.succ.succAbove i) _
  have hhead' : ∀ i, (c' i).order
        (weakComponentHeadIndex (W.mergeAdjacentAt k heq) i) =
      ordUnit K ((W.mergeAdjacentAt k heq).normGeneratorUnit i) := by
    intro i
    by_cases hik : i = k
    · subst i
      have hheadIndex : weakComponentHeadIndex (W.mergeAdjacentAt k heq) k =
          mergeComponentLeftIndex W k heq
            (weakComponentHeadIndex W k.castSucc) := Fin.ext rfl
      rw [hheadIndex]
      dsimp only [c']
      rw [mergeComponentBONGFamily_order_left,
        A.head_order_eq_norm,
        W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self]
      rw [hnorm, min_self]
    · dsimp only [c']
      rw [mergeComponentBONGFamily_of_ne W A.componentBONG
        A.local_order_le_head A.head_order_eq_norm k heq hnorm i hik]
      rw [BONG.order_castLength, BONG.order_castQuadraticSublattice,
        W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq i hik]
      exact A.head_order_eq_norm (k.succ.succAbove i)
  exact {
    componentBONG := c'
    putTogether := A.putTogether.mergeAdjacentAtAdapted W A.componentBONG
      A.local_order_le_head A.head_order_eq_norm k heq hnorm
    local_order_le_head := hlocal'
    head_order_eq_norm := hhead'
  }

end WeakJordanAdaptedWitness

/-- The maximal-norm splitting supplied by Beli (2003), Lemma 4.1 already
carries the adapted component BONG data required at the start of the 2009
Jordan amalgamation. -/
noncomputable def weakJordanAdaptedWitnessOfMaximalNorm
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (w : PutTogetherWitness b M.toOrthogonalDecomposition c) :
    WeakJordanAdaptedWitness b (M.toWeakJordan c) where
  componentBONG := c
  putTogether := w
  local_order_le_head := by
    intro i j
    have hindex : weakComponentHeadIndex (M.toWeakJordan c) i =
        M.componentFirstIndex i := Fin.ext rfl
    rw [hindex]
    exact M.componentOrder_le_componentFirst c i j
  head_order_eq_norm := by
    intro i
    have hindex : weakComponentHeadIndex (M.toWeakJordan c) i =
        M.componentFirstIndex i := Fin.ext rfl
    calc
      (c i).order (weakComponentHeadIndex (M.toWeakJordan c) i) =
          ordUnit K (M.normGenerator i) := by
        rw [hindex]
        exact M.componentFirst_order_eq_normGeneratorOrder c i
      _ = ordUnit K ((M.toWeakJordan c).normGeneratorUnit i) :=
        (M.toWeakJordan_normGeneratorOrder c i).symm

/-- The endpoint alignment used in Beli (2009) together with component BONGs
which still concatenate to the two original good BONGs. -/
structure WeakJordanAdaptedAlignment
    {X : Type w} [AddCommGroup X] [Module K X]
    {r : QuadraticSpace K X} {N : Lattice K X}
    (a : BONG V q L (m + 1)) (b : BONG X r N (m + 1)) (t : Nat) where
  endpoint : WeakJordanEndpointAlignment a b t
  sourceAdapted : WeakJordanAdaptedWitness a endpoint.sourceWeak
  targetAdapted : WeakJordanAdaptedWitness b endpoint.targetWeak

namespace GoodMaximalNormAlignment

variable {X : Type w} [AddCommGroup X] [Module K X]
  {r : QuadraticSpace K X} {N : Lattice K X} {m t : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r N (m + 1)}

/-- Initial adapted alignment before equal-scale neighbours are merged. -/
noncomputable def toWeakJordanAdaptedAlignment
    (P : GoodMaximalNormAlignment a b t) :
    WeakJordanAdaptedAlignment a.toBONG b.toBONG t := by
  let E := P.toWeakJordanEndpointAlignment
  exact {
    endpoint := E
    sourceAdapted := weakJordanAdaptedWitnessOfMaximalNorm
      P.source.splitting P.source.componentBONG a.toBONG P.source.putTogether
    targetAdapted := weakJordanAdaptedWitnessOfMaximalNorm
      P.target.splitting P.target.componentBONG b.toBONG P.target.putTogether
  }

end GoodMaximalNormAlignment

namespace WeakJordanAdaptedAlignment

variable {X : Type w} [AddCommGroup X] [Module K X]
  {r : QuadraticSpace K X} {N : Lattice K X}
  {m : Nat} {a : BONG V q L (m + 1)} {b : BONG X r N (m + 1)}

/-- The scale equality transported to the target side. -/
theorem target_scaleOrder_eq {t : Nat}
    (P : WeakJordanAdaptedAlignment a b (t + 1)) (k : Fin t)
    (heq : ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.succ)) :
    ordUnit K (P.endpoint.targetWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.endpoint.targetWeak.scaleGenerator k.succ) := by
  have hleft := congrFun P.endpoint.scaleOrderFamily_eq k.castSucc
  have hright := congrFun P.endpoint.scaleOrderFamily_eq k.succ
  change ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.castSucc) =
    ordUnit K (P.endpoint.targetWeak.scaleGenerator k.castSucc) at hleft
  change ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.succ) =
    ordUnit K (P.endpoint.targetWeak.scaleGenerator k.succ) at hright
  exact hleft.symm.trans (heq.trans hright)

/-- Synchronously merge one equal-scale pair without losing the component
BONGs or their ambient concatenation witnesses. -/
noncomputable def mergeAdjacentAt {t : Nat}
    (P : WeakJordanAdaptedAlignment a b (t + 1)) (k : Fin t)
    (heq : ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.endpoint.sourceWeak.scaleGenerator k.succ)) :
    WeakJordanAdaptedAlignment a b t := by
  let heqTarget := P.target_scaleOrder_eq k heq
  exact {
    endpoint := P.endpoint.mergeAdjacentAt k heq
    sourceAdapted := P.sourceAdapted.mergeAdjacentAt
      P.endpoint.sourceEndpoints k heq
    targetAdapted := P.targetAdapted.mergeAdjacentAt
      P.endpoint.targetEndpoints k heqTarget
  }

end WeakJordanAdaptedAlignment

/-- The strict Jordan endpoint alignment with the actual component BONGs and
put-together witnesses retained. -/
structure StrictJordanAdaptedAlignment
    {X : Type w} [AddCommGroup X] [Module K X]
    {r : QuadraticSpace K X} {N : Lattice K X}
    (a : BONG V q L (m + 1)) (b : BONG X r N (m + 1)) where
  componentCount : Nat
  weakAlignment : WeakJordanAdaptedAlignment a b componentCount
  sourceStrict : StrictMono (fun i ↦
    ordUnit K (weakAlignment.endpoint.sourceWeak.scaleGenerator i))
  targetStrict : StrictMono (fun i ↦
    ordUnit K (weakAlignment.endpoint.targetWeak.scaleGenerator i))

namespace StrictJordanAdaptedAlignment

variable {X : Type w} [AddCommGroup X] [Module K X]
  {r : QuadraticSpace K X} {N : Lattice K X}
  {m : Nat} {a : BONG V q L (m + 1)} {b : BONG X r N (m + 1)}

/-- Forgetting the retained component BONGs recovers the strict endpoint
alignment used by the semantic Jordan-invariant layer. -/
noncomputable def toStrictJordanEndpointAlignment
    (S : StrictJordanAdaptedAlignment a b) :
    StrictJordanEndpointAlignment a b where
  componentCount := S.componentCount
  weakAlignment := S.weakAlignment.endpoint
  sourceStrict := S.sourceStrict
  targetStrict := S.targetStrict

/-- The actual strict source Jordan decomposition. -/
noncomputable def sourceJordan (S : StrictJordanAdaptedAlignment a b) :
    Lattice.JordanDecomposition q L S.componentCount :=
  S.toStrictJordanEndpointAlignment.sourceJordan

/-- The actual strict target Jordan decomposition. -/
noncomputable def targetJordan (S : StrictJordanAdaptedAlignment a b) :
    Lattice.JordanDecomposition r N S.componentCount :=
  S.toStrictJordanEndpointAlignment.targetJordan

/-- The global source good BONG, viewed with the exact order profile of the
strict Jordan decomposition retained by the adapted alignment. -/
noncomputable def sourceProfile (S : StrictJordanAdaptedAlignment a b) :
    JordanOrderProfileWitness a S.sourceJordan :=
  S.weakAlignment.endpoint.sourceEndpoints.profile.toJordanOfStrict
    S.weakAlignment.endpoint.sourceWeak S.sourceStrict

/-- The corresponding exact order profile on the target side. -/
noncomputable def targetProfile (S : StrictJordanAdaptedAlignment a b) :
    JordanOrderProfileWitness b S.targetJordan :=
  S.weakAlignment.endpoint.targetEndpoints.profile.toJordanOfStrict
    S.weakAlignment.endpoint.targetWeak S.targetStrict

/-- The profile retained by the endpoint witness and the concrete
put-together witness enumerate source coordinates in exactly the same way. -/
theorem sourceProfile_indexEquiv_eq_putTogether
    (S : StrictJordanAdaptedAlignment a b) :
    S.sourceProfile.indexEquiv =
      S.weakAlignment.sourceAdapted.putTogether.indexEquiv := by
  apply Equiv.ext
  intro i
  let p := S.weakAlignment.endpoint.sourceEndpoints.profile
  let h := S.weakAlignment.sourceAdapted.putTogether
  have hi : p.indexOrderIso i = h.indexOrderIso i := by
    exact congrArg (fun e ↦ e i)
      (Subsingleton.elim p.indexOrderIso h.indexOrderIso)
  change toLex (p.indexEquiv i) = toLex (h.indexEquiv i) at hi
  exact toLex_inj.mp hi

/-- Target analogue of `sourceProfile_indexEquiv_eq_putTogether`. -/
theorem targetProfile_indexEquiv_eq_putTogether
    (S : StrictJordanAdaptedAlignment a b) :
    S.targetProfile.indexEquiv =
      S.weakAlignment.targetAdapted.putTogether.indexEquiv := by
  apply Equiv.ext
  intro i
  let p := S.weakAlignment.endpoint.targetEndpoints.profile
  let h := S.weakAlignment.targetAdapted.putTogether
  have hi : p.indexOrderIso i = h.indexOrderIso i := by
    exact congrArg (fun e ↦ e i)
      (Subsingleton.elim p.indexOrderIso h.indexOrderIso)
  change toLex (p.indexEquiv i) = toLex (h.indexEquiv i) at hi
  exact toLex_inj.mp hi

/-- Corresponding strict Jordan components have equal ranks. -/
theorem componentRank_eq (S : StrictJordanAdaptedAlignment a b)
    (i : Fin S.componentCount) :
    S.weakAlignment.endpoint.sourceWeak.toOrthogonalDecomposition.componentRank i =
      S.weakAlignment.endpoint.targetWeak.toOrthogonalDecomposition.componentRank i := by
  exact congrFun S.weakAlignment.endpoint.componentRankFamily_eq i

/-- Transport a source component coordinate to the same numerical coordinate
of the corresponding target component. -/
noncomputable def targetLocalIndex (S : StrictJordanAdaptedAlignment a b)
    (i : Fin S.componentCount)
    (j : Fin
      (S.weakAlignment.endpoint.sourceWeak.toOrthogonalDecomposition.componentRank i)) :
    Fin (S.weakAlignment.endpoint.targetWeak.toOrthogonalDecomposition.componentRank i) :=
  Fin.cast (S.componentRank_eq i) j

@[simp] theorem targetLocalIndex_val
    (S : StrictJordanAdaptedAlignment a b)
    (i : Fin S.componentCount)
    (j : Fin
      (S.weakAlignment.endpoint.sourceWeak.toOrthogonalDecomposition.componentRank i)) :
    (S.targetLocalIndex i j).val = j.val :=
  rfl

/-- The source global coordinate attached to `(i,j)` is also the target
global coordinate attached to the transported local coordinate.  This is the
exact indexing statement behind Beli's synchronous Jordan comparison. -/
theorem inverse_indexEquiv_eq
    (S : StrictJordanAdaptedAlignment a b)
    (i : Fin S.componentCount)
    (j : Fin
      (S.weakAlignment.endpoint.sourceWeak.toOrthogonalDecomposition.componentRank i)) :
    S.weakAlignment.sourceAdapted.putTogether.indexEquiv.symm ⟨i, j⟩ =
      S.weakAlignment.targetAdapted.putTogether.indexEquiv.symm
        ⟨i, S.targetLocalIndex i j⟩ := by
  apply Fin.ext
  rw [S.weakAlignment.sourceAdapted.putTogether.inverse_index_val,
    S.weakAlignment.targetAdapted.putTogether.inverse_index_val]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact congrFun S.weakAlignment.endpoint.componentRankFamily_eq k

/-- Equal global good-BONG order sequences induce equal order sequences on
every pair of corresponding retained Jordan-component BONGs. -/
theorem componentBONG_order_eq
    (S : StrictJordanAdaptedAlignment a b)
    (horders : ∀ i, a.order i = b.order i)
    (i : Fin S.componentCount)
    (j : Fin
      (S.weakAlignment.endpoint.sourceWeak.toOrthogonalDecomposition.componentRank i)) :
    (S.weakAlignment.sourceAdapted.componentBONG i).order j =
      (S.weakAlignment.targetAdapted.componentBONG i).order
        (S.targetLocalIndex i j) := by
  let g := S.weakAlignment.sourceAdapted.putTogether.indexEquiv.symm ⟨i, j⟩
  calc
    (S.weakAlignment.sourceAdapted.componentBONG i).order j = a.order g :=
      (S.weakAlignment.sourceAdapted.putTogether.order_inverse_indexEquiv_general
        i j).symm
    _ = b.order g := horders g
    _ = (S.weakAlignment.targetAdapted.componentBONG i).order
        (S.targetLocalIndex i j) := by
      rw [show g = S.weakAlignment.targetAdapted.putTogether.indexEquiv.symm
          ⟨i, S.targetLocalIndex i j⟩ from S.inverse_indexEquiv_eq i j]
      exact S.weakAlignment.targetAdapted.putTogether.order_inverse_indexEquiv_general
        i (S.targetLocalIndex i j)

/-- A nonempty global good BONG gives a nonempty strict Jordan family. -/
theorem componentCount_pos (S : StrictJordanAdaptedAlignment a b) :
    0 < S.componentCount :=
  S.toStrictJordanEndpointAlignment.componentCount_pos

end StrictJordanAdaptedAlignment

namespace WeakJordanAdaptedAlignment

variable {X : Type w} [AddCommGroup X] [Module K X]
  {r : QuadraticSpace K X} {N : Lattice K X}
  {m : Nat} {a : BONG V q L (m + 1)} {b : BONG X r N (m + 1)}

/-- Repeated synchronous amalgamation terminates while preserving all adapted
component data. -/
theorem exists_strict :
    ∀ (t : Nat) (_P : WeakJordanAdaptedAlignment a b t),
      Nonempty (StrictJordanAdaptedAlignment a b) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro P
      let f : Fin t → Int := fun i ↦
        ordUnit K (P.endpoint.sourceWeak.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · have htarget : StrictMono (fun i ↦
            ordUnit K (P.endpoint.targetWeak.scaleGenerator i)) := by
          change StrictMono P.endpoint.targetWeak.scaleOrderFamily
          rw [← P.endpoint.scaleOrderFamily_eq]
          exact hstrict
        exact ⟨{
          componentCount := t
          weakAlignment := P
          sourceStrict := hstrict
          targetStrict := htarget
        }⟩
      · cases t with
        | zero =>
            exfalso
            apply hstrict
            exact fun i ↦ Fin.elim0 i
        | succ t =>
            cases t with
            | zero =>
                exfalso
                apply hstrict
                intro i j hij
                omega
            | succ d =>
                have hadj : ¬∀ k : Fin (d + 1),
                    f k.castSucc < f k.succ := by
                  intro hall
                  exact hstrict ((Fin.strictMono_iff_lt_succ).2 hall)
                push Not at hadj
                obtain ⟨k, hk⟩ := hadj
                have hle : f k.castSucc ≤ f k.succ :=
                  P.endpoint.sourceWeak.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K
                      (P.endpoint.sourceWeak.scaleGenerator k.castSucc) =
                    ordUnit K
                      (P.endpoint.sourceWeak.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                exact ih (d + 1) (by omega) (P.mergeAdjacentAt k heq)

end WeakJordanAdaptedAlignment

/-- Equal order sequences of nonempty good BONGs admit strict aligned Jordan
decompositions whose component BONGs still literally recover both inputs. -/
theorem GoodBONG.nonempty_strictJordanAdaptedAlignment
    {X : Type w} [AddCommGroup X] [Module K X]
    {r : QuadraticSpace K X} {N : Lattice K X} {m : Nat}
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r N (m + 1))
    (horders : ∀ i, a.order i = b.order i) :
    Nonempty (StrictJordanAdaptedAlignment a.toBONG b.toBONG) := by
  rcases a.nonempty_goodMaximalNormAlignment b horders with ⟨t, ⟨P⟩⟩
  exact (P.toWeakJordanAdaptedAlignment).exists_strict t

end BONG
end Bong
