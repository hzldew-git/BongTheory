/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanEndpointAmalgamation
import Bong.Bong.BeliCorollary42GoodProof
import Bong.Bong.JordanOrderProfileSequence

/-!
# Aligned strict Jordan decompositions from equal good-BONG orders

This file proves the concrete alignment step used in Beli (2009), Theorem 3.1.
If two nonempty good BONGs have the same order sequence, their canonical
maximal-norm splittings have corresponding components with equal rank, scale
order, and norm order.  Amalgamating equal-scale neighbours synchronously then
produces strict Jordan decompositions on both sides while retaining the first
and last scalar norm generators of every component.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG.PutTogetherWitness

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily} {b : BONG V q L n}

/-- The order-preserving equivalence underlying a put-together witness. -/
noncomputable def indexOrderIso
    (h : PutTogetherWitness b D c) :
    Fin n ≃o Lex (Σ i : Fin t, Fin (D.componentRank i)) where
  toFun i := toLex (h.indexEquiv i)
  invFun z := h.indexEquiv.symm (ofLex z)
  left_inv i := by
    change h.indexEquiv.symm (h.indexEquiv i) = i
    exact h.indexEquiv.symm_apply_apply i
  right_inv z := by
    change toLex (h.indexEquiv (h.indexEquiv.symm (ofLex z))) = z
    rw [h.indexEquiv.apply_symm_apply]
    exact toLex_ofLex z
  map_rel_iff' := by
    intro i j
    change toLex (h.indexEquiv i) ≤ toLex (h.indexEquiv j) ↔ i ≤ j
    constructor
    · intro hij
      apply le_of_not_gt
      intro hji
      have hlex := (h.order_iff j i).1 hji
      rw [JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt] at hlex
      exact (not_lt_of_ge hij) hlex
    · intro hij
      apply le_of_not_gt
      intro hji
      have hlex : toLex (h.indexEquiv j) < toLex (h.indexEquiv i) := hji
      rw [← JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt] at hlex
      exact (not_lt_of_ge hij) ((h.order_iff j i).2 hlex)

/-- The numerical global index is its component-prefix rank plus local index. -/
theorem index_val_eq_componentStart_add_local
    (h : PutTogetherWitness b D c) (i : Fin n) :
    i.val =
      (∑ k ∈ Finset.Iio (h.componentIndex i), D.componentRank k) +
        (h.localIndex i).val := by
  calc
    i.val = Fintype.card {x : Lex (Σ k : Fin t, Fin (D.componentRank k)) //
        x < h.indexOrderIso i} :=
      JordanProfileIndexing.orderIso_fin_val_eq_card_Iio h.indexOrderIso i
    _ = _ := by
      change Fintype.card {x : Lex (Σ k : Fin t, Fin (D.componentRank k)) //
          x < toLex (h.indexEquiv i)} = _
      exact JordanProfileIndexing.lexSigmaIio_card
        D.componentRank (h.componentIndex i) (h.localIndex i)

/-- Exact global index of a specified component coordinate. -/
theorem inverse_index_val
    (h : PutTogetherWitness b D c) (i : Fin t)
    (j : Fin (D.componentRank i)) :
    (h.indexEquiv.symm ⟨i, j⟩).val =
      (∑ k ∈ Finset.Iio i, D.componentRank k) + j.val := by
  have hx := h.index_val_eq_componentStart_add_local
    (h.indexEquiv.symm ⟨i, j⟩)
  calc
    (h.indexEquiv.symm ⟨i, j⟩).val =
        (∑ k ∈ Finset.Iio
            (h.componentIndex (h.indexEquiv.symm ⟨i, j⟩)),
          D.componentRank k) +
            (h.localIndex (h.indexEquiv.symm ⟨i, j⟩)).val := hx
    _ = _ := by
      have heq : h.indexEquiv (h.indexEquiv.symm ⟨i, j⟩) = ⟨i, j⟩ :=
        h.indexEquiv.apply_symm_apply ⟨i, j⟩
      have hlocalVal := congrArg (fun z ↦ z.2.val) heq
      simp only [PutTogetherWitness.componentIndex,
        PutTogetherWitness.localIndex]
      rw [heq]

/-- At an inverse component coordinate, the global order is the local
component order. -/
theorem order_inverse_indexEquiv
    {M : Lattice.MaximalNormSplitting q L t}
    {c : M.toOrthogonalDecomposition.ComponentBONGFamily}
    (h : PutTogetherWitness b M.toOrthogonalDecomposition c)
    (i : Fin t) (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    b.order (h.indexEquiv.symm ⟨i, j⟩) = (c i).order j := by
  rw [b.order_eq_ordUnit, (c i).order_eq_ordUnit,
    h.valueUnit_inverse_indexEquiv]

/-- A strict order drop across consecutive global coordinates cannot cross
a maximal-norm component boundary. -/
theorem componentIndex_eq_of_order_succ_lt
    {M : Lattice.MaximalNormSplitting q L t}
    {c : M.toOrthogonalDecomposition.ComponentBONGFamily}
    (h : PutTogetherWitness b M.toOrthogonalDecomposition c)
    (i : Fin n) (hi : i.val + 1 < n)
    (hdrop : b.order ⟨i.val + 1, hi⟩ < b.order i) :
    h.componentIndex ⟨i.val + 1, hi⟩ = h.componentIndex i := by
  let next : Fin n := ⟨i.val + 1, hi⟩
  have hinext : i < next := by
    change i.val < i.val + 1
    omega
  have hlex := (h.order_iff i next).1 hinext
  rcases hlex with hcomponent | hsame
  · have hnextZero := h.localIndex_succ_eq_zero_of_component_lt
      i hi hcomponent
    have hnextFirst : h.localIndex next =
        M.componentFirstIndex (h.componentIndex next) := by
      apply Fin.ext
      simpa only [Lattice.MaximalNormSplitting.componentFirstIndex] using
        hnextZero
    have hnormMono : ordUnit K (M.normGenerator (h.componentIndex i)) ≤
        ordUnit K (M.normGenerator (h.componentIndex next)) := by
      have hgap : 0 ≤ ordUnit K (M.normGenerator (h.componentIndex next)) -
          ordUnit K (M.normGenerator (h.componentIndex i)) := by
        simpa only [PutTogetherWitness.componentIndex] using
          (M.normGap_bounds hcomponent).1
      omega
    have hnotDrop : b.order i ≤ b.order next := by
      calc
        b.order i = (c (h.componentIndex i)).order (h.localIndex i) :=
          h.order_eq i
        _ ≤ (c (h.componentIndex i)).order
            (M.componentFirstIndex (h.componentIndex i)) :=
          M.componentOrder_le_componentFirst c _ _
        _ = ordUnit K (M.normGenerator (h.componentIndex i)) :=
          M.componentFirst_order_eq_normGeneratorOrder c _
        _ ≤ ordUnit K (M.normGenerator (h.componentIndex next)) := hnormMono
        _ = (c (h.componentIndex next)).order
            (M.componentFirstIndex (h.componentIndex next)) :=
          (M.componentFirst_order_eq_normGeneratorOrder c _).symm
        _ = (c (h.componentIndex next)).order (h.localIndex next) := by
          rw [hnextFirst]
        _ = b.order next := (h.order_eq next).symm
    exact (not_lt_of_ge hnotDrop hdrop).elim
  · exact hsame.1.symm

/-- In an improper unary-or-binary maximal-norm profile, consecutive global
coordinates lie in one component exactly when the order strictly drops. -/
theorem componentIndex_succ_eq_iff_order_succ_lt
    {M : Lattice.MaximalNormSplitting q L t}
    {c : M.toOrthogonalDecomposition.ComponentBONGFamily}
    (h : PutTogetherWitness b M.toOrthogonalDecomposition c)
    (himproper : AllBinaryComponentsImproper M c)
    (i : Fin n) (hi : i.val + 1 < n) :
    h.componentIndex ⟨i.val + 1, hi⟩ = h.componentIndex i ↔
      b.order ⟨i.val + 1, hi⟩ < b.order i := by
  let next : Fin n := ⟨i.val + 1, hi⟩
  constructor
  · intro hcomponent
    have hinext : i < next := by
      change i.val < i.val + 1
      omega
    have hlex := (h.order_iff i next).1 hinext
    rcases hlex with hlt | hsame
    · have hlt' : h.componentIndex i < h.componentIndex next := hlt
      exact (ne_of_lt hlt' hcomponent.symm).elim
    · generalize hiCoord : h.indexEquiv i = sourceCoord at hsame
      generalize hnCoord : h.indexEquiv next = nextCoord at hsame
      rcases sourceCoord with ⟨sourceComponent, sourceLocal⟩
      rcases nextCoord with ⟨nextComponent, nextLocal⟩
      simp only at hsame
      rcases hsame with ⟨hcomponents, hlocal⟩
      subst nextComponent
      have hrankTwo : M.componentRank sourceComponent = 2 := by
        rcases M.componentRank_eq_one_or_two sourceComponent with hOne | hTwo
        · have hiBound := (h.localIndex i).isLt
          have hnBound := (h.localIndex next).isLt
          unfold PutTogetherWitness.localIndex
            PutTogetherWitness.componentIndex at hiBound hnBound
          rw [hiCoord] at hiBound
          rw [hnCoord] at hnBound
          change sourceLocal.val < M.componentRank sourceComponent at hiBound
          change nextLocal.val < M.componentRank sourceComponent at hnBound
          omega
        · exact hTwo
      have hiZero : sourceLocal.val = 0 := by
        have hiBound := (h.localIndex i).isLt
        have hnBound := (h.localIndex next).isLt
        unfold PutTogetherWitness.localIndex
          PutTogetherWitness.componentIndex at hiBound hnBound
        rw [hiCoord] at hiBound
        rw [hnCoord] at hnBound
        change sourceLocal.val < M.componentRank sourceComponent at hiBound
        change nextLocal.val < M.componentRank sourceComponent at hnBound
        rw [hrankTwo] at hiBound
        rw [hrankTwo] at hnBound
        omega
      have hnOne : nextLocal.val = 1 := by
        have hnBound := (h.localIndex next).isLt
        unfold PutTogetherWitness.localIndex
          PutTogetherWitness.componentIndex at hnBound
        rw [hnCoord] at hnBound
        change nextLocal.val < M.componentRank sourceComponent at hnBound
        rw [hrankTwo] at hnBound
        omega
      let binary := (c sourceComponent).castLength hrankTwo
      have hbinary : binary.IsImproperModular :=
        himproper sourceComponent hrankTwo
      have hdropLocal : binary.order 1 < binary.order 0 := by
        change binary.order 1 - binary.order 0 < 0 at hbinary
        omega
      rw [h.order_eq i, h.order_eq next]
      unfold PutTogetherWitness.componentIndex
        PutTogetherWitness.localIndex
      rw [hiCoord, hnCoord]
      change (c sourceComponent).order nextLocal <
        (c sourceComponent).order sourceLocal
      have hzero : sourceLocal =
          (⟨0, by rw [hrankTwo]; omega⟩ : Fin (M.componentRank sourceComponent)) :=
        Fin.ext hiZero
      have hone : nextLocal =
          (⟨1, by rw [hrankTwo]; omega⟩ : Fin (M.componentRank sourceComponent)) :=
        Fin.ext hnOne
      rw [hzero, hone]
      have hdropLocal' := hdropLocal
      simp only [binary, BONG.order_castLength] at hdropLocal'
      convert hdropLocal' using 1 <;> congr 1
  · exact h.componentIndex_eq_of_order_succ_lt i hi

end BONG.PutTogetherWitness

namespace BONG

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {N : Lattice K W} {m : Nat}

/-- Concrete maximal-norm data selected for a nonempty good BONG. -/
structure GoodMaximalNormData
    (a : GoodBONG q L (m + 1)) (t : Nat) where
  splitting : Lattice.MaximalNormSplitting q L t
  componentBONG : splitting.toOrthogonalDecomposition.ComponentBONGFamily
  putTogether : PutTogetherWitness a.toBONG
    splitting.toOrthogonalDecomposition componentBONG
  allBinaryImproper : AllBinaryComponentsImproper splitting componentBONG

/-- Every nonempty good BONG has concrete maximal-norm data. -/
theorem GoodBONG.nonempty_goodMaximalNormData
    (a : GoodBONG q L (m + 1)) :
    ∃ t, Nonempty (GoodMaximalNormData a t) := by
  rcases a.toBONG.beliLemma43_iii a.good with
    ⟨t, M, c, ⟨h⟩, himproper⟩
  exact ⟨t, ⟨⟨M, c, h, himproper⟩⟩⟩

namespace GoodMaximalNormData

variable {a : GoodBONG q L (m + 1)} {b : GoodBONG r N (m + 1)}
  {s t : Nat} (A : GoodMaximalNormData a t)
  (B : GoodMaximalNormData b s)

/-- First global coordinate belonging to a maximal-norm component. -/
noncomputable def firstGlobalIndex (i : Fin t) : Fin (m + 1) :=
  A.putTogether.indexEquiv.symm
    ⟨i, A.splitting.componentFirstIndex i⟩

/-- The target component containing the first coordinate of a source
component. -/
noncomputable def componentMap (i : Fin t) : Fin s :=
  B.putTogether.componentIndex (A.firstGlobalIndex i)

theorem source_componentIndex_firstGlobalIndex (i : Fin t) :
    A.putTogether.componentIndex (A.firstGlobalIndex i) = i := by
  simp [firstGlobalIndex, PutTogetherWitness.componentIndex]

/-- Every coordinate of one source component belongs to the target component
selected by its first coordinate. -/
theorem target_componentIndex_inverse_source
    (horders : ∀ i, a.order i = b.order i)
    (i : Fin t) (j : Fin (A.splitting.componentRank i)) :
    B.putTogether.componentIndex
        (A.putTogether.indexEquiv.symm ⟨i, j⟩) = A.componentMap B i := by
  rcases A.splitting.componentRank_eq_one_or_two i with hOne | hTwo
  · have hj : j = A.splitting.componentFirstIndex i := by
      apply Fin.ext
      have hjlt := j.isLt
      have hjlt' : j.val < 1 := by simpa only [hOne] using hjlt
      omega
    rw [hj]
    rfl
  · have hjCases : j.val = 0 ∨ j.val = 1 := by
      have hjlt := j.isLt
      have hjlt' : j.val < 2 := by simpa only [hTwo] using hjlt
      omega
    rcases hjCases with hjZero | hjOne
    · have hj : j = A.splitting.componentFirstIndex i := Fin.ext hjZero
      rw [hj]
      rfl
    · let first := A.firstGlobalIndex i
      let current := A.putTogether.indexEquiv.symm ⟨i, j⟩
      have hfirstVal := A.putTogether.inverse_index_val i
        (A.splitting.componentFirstIndex i)
      have hcurrentVal := A.putTogether.inverse_index_val i j
      have hsuccVal : current.val = first.val + 1 := by
        change first.val = _ at hfirstVal
        change current.val = _ at hcurrentVal
        have hfirstZero :
            (A.splitting.componentFirstIndex i).val = 0 := rfl
        omega
      have hfirstBound : first.val + 1 < m + 1 := by
        rw [← hsuccVal]
        exact current.isLt
      have hcurrentEq : current =
          (⟨first.val + 1, hfirstBound⟩ : Fin (m + 1)) := Fin.ext hsuccVal
      have hsameSource : A.putTogether.componentIndex
            (⟨first.val + 1, hfirstBound⟩ : Fin (m + 1)) =
          A.putTogether.componentIndex first := by
        rw [← hcurrentEq]
        dsimp only [current, first, firstGlobalIndex]
        simp only [PutTogetherWitness.componentIndex,
          A.putTogether.indexEquiv.apply_symm_apply]
      have hdropSource : a.order
            (⟨first.val + 1, hfirstBound⟩ : Fin (m + 1)) <
          a.order first :=
        (A.putTogether.componentIndex_succ_eq_iff_order_succ_lt
          A.allBinaryImproper first hfirstBound).1 hsameSource
      have hdropTarget : b.order current < b.order first := by
        rw [hcurrentEq, ← horders, ← horders]
        exact hdropSource
      have hsameTarget :=
        (B.putTogether.componentIndex_succ_eq_iff_order_succ_lt
          B.allBinaryImproper first hfirstBound).2 (by
            rw [← hcurrentEq]
            exact hdropTarget)
      change B.putTogether.componentIndex current = _
      rw [hcurrentEq]
      exact hsameTarget

/-- Component indices are transported pointwise along the map determined by
the common order sequence. -/
theorem target_componentIndex_eq_map_source
    (horders : ∀ i, a.order i = b.order i) (x : Fin (m + 1)) :
    B.putTogether.componentIndex x =
      A.componentMap B (A.putTogether.componentIndex x) := by
  let i := A.putTogether.componentIndex x
  let j := A.putTogether.localIndex x
  have hx : x = A.putTogether.indexEquiv.symm ⟨i, j⟩ := by
    change x = A.putTogether.indexEquiv.symm (A.putTogether.indexEquiv x)
    exact (A.putTogether.indexEquiv.symm_apply_apply x).symm
  rw [hx]
  simpa only [i, j, PutTogetherWitness.componentIndex,
    PutTogetherWitness.localIndex,
    A.putTogether.indexEquiv.apply_symm_apply] using
      A.target_componentIndex_inverse_source B horders i j

/-- The component maps obtained in the two directions are inverse. -/
theorem reverse_componentMap_componentMap
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    B.componentMap A (A.componentMap B i) = i := by
  let x := A.firstGlobalIndex i
  have htarget : B.putTogether.componentIndex x = A.componentMap B i := rfl
  have hsource := B.target_componentIndex_eq_map_source A
    (fun j ↦ (horders j).symm) x
  rw [htarget] at hsource
  exact hsource.symm.trans (A.source_componentIndex_firstGlobalIndex i)

/-- Component correspondence for two equal order sequences. -/
noncomputable def componentEquiv
    (horders : ∀ i, a.order i = b.order i) : Fin t ≃ Fin s where
  toFun := A.componentMap B
  invFun := B.componentMap A
  left_inv := A.reverse_componentMap_componentMap B horders
  right_inv := B.reverse_componentMap_componentMap A
    (fun i ↦ (horders i).symm)

/-- The component correspondence preserves component order. -/
theorem componentMap_strictMono
    (horders : ∀ i, a.order i = b.order i) :
    StrictMono (A.componentMap B) := by
  intro i j hij
  let xi := A.firstGlobalIndex i
  let xj := A.firstGlobalIndex j
  have hxij : xi < xj := by
    apply (A.putTogether.order_iff xi xj).2
    unfold BONG.ComponentIndexBefore
    left
    simp only [xi, xj, firstGlobalIndex,
      A.putTogether.indexEquiv.apply_symm_apply]
    exact hij
  have htarget := (B.putTogether.order_iff xi xj).1 hxij
  rcases htarget with hlt | hsame
  · exact hlt
  · have heq : A.componentMap B i = A.componentMap B j := hsame.1
    have hback := congrArg (B.componentMap A) heq
    rw [A.reverse_componentMap_componentMap B horders,
      A.reverse_componentMap_componentMap B horders] at hback
    exact (ne_of_lt hij hback).elim

/-- The component correspondence as an order isomorphism. -/
noncomputable def componentOrderIso
    (horders : ∀ i, a.order i = b.order i) : Fin t ≃o Fin s where
  toEquiv := A.componentEquiv B horders
  map_rel_iff' := by
    intro i j
    constructor
    · intro hij
      by_contra hnot
      have hji : j < i := lt_of_not_ge hnot
      exact (not_lt_of_ge hij) (A.componentMap_strictMono B horders hji)
    · intro hij
      exact (A.componentMap_strictMono B horders).monotone hij

/-- The global coordinates belonging to one maximal-norm component. -/
abbrev ComponentFiber (i : Fin t) :=
  {x : Fin (m + 1) // A.putTogether.componentIndex x = i}

/-- Local component coordinates are exactly the corresponding global
coordinate fiber. -/
noncomputable def localFiberEquiv (i : Fin t) :
    Fin (A.splitting.toOrthogonalDecomposition.componentRank i) ≃
      A.ComponentFiber i where
  toFun j := ⟨A.putTogether.indexEquiv.symm ⟨i, j⟩, by
    simp only [PutTogetherWitness.componentIndex,
      A.putTogether.indexEquiv.apply_symm_apply]⟩
  invFun x := Fin.cast
    (congrArg A.splitting.toOrthogonalDecomposition.componentRank x.property)
    (A.putTogether.localIndex x.1)
  left_inv j := by
    apply Fin.ext
    have heq : A.putTogether.indexEquiv
        (A.putTogether.indexEquiv.symm ⟨i, j⟩) = ⟨i, j⟩ :=
      A.putTogether.indexEquiv.apply_symm_apply ⟨i, j⟩
    exact congrArg (fun z ↦ z.2.val) heq
  right_inv x := by
    apply Subtype.ext
    apply A.putTogether.indexEquiv.injective
    rw [A.putTogether.indexEquiv.apply_symm_apply]
    generalize hcoord : A.putTogether.indexEquiv x.1 = coord
    rcases coord with ⟨k, j⟩
    have hk : k = i := by
      have hx := x.property
      unfold PutTogetherWitness.componentIndex at hx
      rw [hcoord] at hx
      exact hx
    subst k
    apply Sigma.ext
    · rfl
    · rw [heq_iff_eq]
      apply Fin.ext
      have hjval := congrArg (fun z ↦ z.2.val) hcoord
      unfold PutTogetherWitness.localIndex
      simpa only [Fin.val_cast] using hjval

/-- The preceding fiber equivalence also preserves the inherited global
order. -/
noncomputable def localFiberOrderIso (i : Fin t) :
    Fin (A.splitting.toOrthogonalDecomposition.componentRank i) ≃o
      A.ComponentFiber i where
  toEquiv := A.localFiberEquiv i
  map_rel_iff' := by
    intro j k
    constructor
    · intro hjk
      by_contra hnot
      have hkj : k < j := lt_of_not_ge hnot
      have hglobal :
          A.putTogether.indexEquiv.symm ⟨i, k⟩ <
            A.putTogether.indexEquiv.symm ⟨i, j⟩ := by
        apply (A.putTogether.order_iff _ _).2
        rw [A.putTogether.indexEquiv.apply_symm_apply,
          A.putTogether.indexEquiv.apply_symm_apply]
        exact Or.inr ⟨rfl, hkj⟩
      exact (not_lt_of_ge hjk) hglobal
    · intro hjk
      by_contra hnot
      have hglobal :
          A.putTogether.indexEquiv.symm ⟨i, k⟩ <
            A.putTogether.indexEquiv.symm ⟨i, j⟩ :=
        lt_of_not_ge hnot
      have hlocal := (A.putTogether.order_iff _ _).1 hglobal
      rw [A.putTogether.indexEquiv.apply_symm_apply,
        A.putTogether.indexEquiv.apply_symm_apply] at hlocal
      rcases hlocal with hcomponent | hsame
      · exact (lt_irrefl i hcomponent).elim
      · exact (not_lt_of_ge hjk) hsame.2

/-- Equality of the global order sequences identifies the source component
fiber with the target component fiber, by the identity on global indices. -/
noncomputable def componentFiberTargetOrderIso
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    A.ComponentFiber i ≃o B.ComponentFiber (A.componentMap B i) where
  toFun x := ⟨x.1, by
    rw [A.target_componentIndex_eq_map_source B horders x.1,
      x.property]⟩
  invFun x := ⟨x.1, by
    have hsource := B.target_componentIndex_eq_map_source A
      (fun j ↦ (horders j).symm) x.1
    rw [x.property,
      A.reverse_componentMap_componentMap B horders] at hsource
    exact hsource⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- The local coordinates of corresponding components are canonically order
isomorphic. -/
noncomputable def componentLocalOrderIso
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    Fin (A.splitting.toOrthogonalDecomposition.componentRank i) ≃o
      Fin (B.splitting.toOrthogonalDecomposition.componentRank
        (A.componentMap B i)) :=
  (A.localFiberOrderIso i).trans
    ((A.componentFiberTargetOrderIso B horders i).trans
      ((localFiberOrderIso (A := B) (A.componentMap B i)).symm))

/-- The local order isomorphism is induced by the identity on global
coordinates. -/
theorem componentLocalOrderIso_global_eq
    (horders : ∀ i, a.order i = b.order i) (i : Fin t)
    (j : Fin (A.splitting.toOrthogonalDecomposition.componentRank i)) :
    B.putTogether.indexEquiv.symm
        ⟨A.componentMap B i, (A.componentLocalOrderIso B horders i) j⟩ =
      A.putTogether.indexEquiv.symm ⟨i, j⟩ := by
  let sourceFiber : A.ComponentFiber i :=
    (A.localFiberOrderIso i) j
  let targetFiber : B.ComponentFiber (A.componentMap B i) :=
    (A.componentFiberTargetOrderIso B horders i) sourceFiber
  change ((B.localFiberOrderIso (A.componentMap B i))
      ((A.componentLocalOrderIso B horders i) j)).val =
    A.putTogether.indexEquiv.symm ⟨i, j⟩
  rw [show (A.componentLocalOrderIso B horders i) j =
      (B.localFiberOrderIso (A.componentMap B i)).symm targetFiber by rfl]
  calc
    ((B.localFiberOrderIso (A.componentMap B i))
        ((B.localFiberOrderIso (A.componentMap B i)).symm targetFiber)).val =
        targetFiber.val := congrArg Subtype.val
          ((B.localFiberOrderIso (A.componentMap B i)).apply_symm_apply
            targetFiber)
    _ = sourceFiber.val := rfl
    _ = A.putTogether.indexEquiv.symm ⟨i, j⟩ := rfl

/-- Corresponding maximal-norm components have equal rank. -/
theorem componentRank_map_eq
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    A.splitting.componentRank i =
      B.splitting.componentRank (A.componentMap B i) := by
  have hcard := Fintype.card_congr
    (A.componentLocalOrderIso B horders i).toEquiv
  calc
    A.splitting.componentRank i = Fintype.card
        (Fin (A.splitting.toOrthogonalDecomposition.componentRank i)) := by
      rw [Fintype.card_fin]
      rfl
    _ = Fintype.card
        (Fin (B.splitting.toOrthogonalDecomposition.componentRank
          (A.componentMap B i))) := hcard
    _ = B.splitting.componentRank (A.componentMap B i) := by
      rw [Fintype.card_fin]
      rfl

/-- An order isomorphism between finite initial segments preserves the
numerical coordinate. -/
theorem componentLocalOrderIso_val
    (horders : ∀ i, a.order i = b.order i) (i : Fin t)
    (j : Fin (A.splitting.toOrthogonalDecomposition.componentRank i)) :
    ((A.componentLocalOrderIso B horders i) j).val = j.val := by
  classical
  have hcard := JordanProfileIndexing.orderIso_fin_val_eq_card_Iio
    (A.componentLocalOrderIso B horders i) j
  have htarget : Fintype.card
      {x : Fin (B.splitting.toOrthogonalDecomposition.componentRank
        (A.componentMap B i)) //
          x < (A.componentLocalOrderIso B horders i) j} =
      ((A.componentLocalOrderIso B horders i) j).val := by
    rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  omega

/-- Corresponding local coordinates have the same numerical position. -/
theorem target_localIndex_inverse_source_val
    (horders : ∀ i, a.order i = b.order i) (i : Fin t)
    (j : Fin (A.splitting.toOrthogonalDecomposition.componentRank i)) :
    (B.putTogether.localIndex
      (A.putTogether.indexEquiv.symm ⟨i, j⟩)).val = j.val := by
  have hglobal := A.componentLocalOrderIso_global_eq B horders i j
  have htarget := congrArg B.putTogether.indexEquiv hglobal
  rw [B.putTogether.indexEquiv.apply_symm_apply] at htarget
  have hlocal := congrArg (fun z ↦ z.2.val) htarget
  exact hlocal.symm.trans (A.componentLocalOrderIso_val B horders i j)

/-- Corresponding maximal-norm components have the same norm-ideal order. -/
theorem normGeneratorOrder_map_eq
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    ordUnit K (A.splitting.normGenerator i) =
      ordUnit K (B.splitting.normGenerator (A.componentMap B i)) := by
  let firstA := A.splitting.componentFirstIndex i
  let firstB := (A.componentLocalOrderIso B horders i) firstA
  have hfirstBVal : firstB.val = 0 := by
    have hval := A.componentLocalOrderIso_val B horders i firstA
    change ((A.componentLocalOrderIso B horders i) firstA).val = 0
    simpa only [firstA,
      Lattice.MaximalNormSplitting.componentFirstIndex] using hval
  have hfirstBEq : firstB =
      B.splitting.componentFirstIndex (A.componentMap B i) := by
    apply Fin.ext
    simpa only [Lattice.MaximalNormSplitting.componentFirstIndex] using
      hfirstBVal
  have hglobal := A.componentLocalOrderIso_global_eq B horders i firstA
  calc
    ordUnit K (A.splitting.normGenerator i) =
        (A.componentBONG i).order firstA := by
      exact (A.splitting.componentFirst_order_eq_normGeneratorOrder
        A.componentBONG i).symm
    _ = a.order (A.putTogether.indexEquiv.symm ⟨i, firstA⟩) :=
      (A.putTogether.order_inverse_indexEquiv i firstA).symm
    _ = b.order (A.putTogether.indexEquiv.symm ⟨i, firstA⟩) :=
      horders _
    _ = b.order (B.putTogether.indexEquiv.symm
        ⟨A.componentMap B i, firstB⟩) := by rw [hglobal]
    _ = (B.componentBONG (A.componentMap B i)).order firstB :=
      B.putTogether.order_inverse_indexEquiv _ firstB
    _ = (B.componentBONG (A.componentMap B i)).order
        (B.splitting.componentFirstIndex (A.componentMap B i)) := by
      rw [hfirstBEq]
    _ = ordUnit K
        (B.splitting.normGenerator (A.componentMap B i)) :=
      B.splitting.componentFirst_order_eq_normGeneratorOrder
        B.componentBONG _

/-- Corresponding maximal-norm components have the same scale-ideal order. -/
theorem scaleGeneratorOrder_map_eq
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    ordUnit K (A.splitting.scaleGenerator i) =
      ordUnit K (B.splitting.scaleGenerator (A.componentMap B i)) := by
  let lastA := A.splitting.componentLastIndex i
  let imageLast := (A.componentLocalOrderIso B horders i) lastA
  let lastB := B.splitting.componentLastIndex (A.componentMap B i)
  have hrank := A.componentRank_map_eq B horders i
  have hlastA := A.splitting.componentLastIndex_val i
  have hlastB := B.splitting.componentLastIndex_val (A.componentMap B i)
  have himageVal := A.componentLocalOrderIso_val B horders i lastA
  have hlastA' : lastA.val + 1 = A.splitting.componentRank i := by
    change lastA.val + 1 = A.splitting.componentRank i at hlastA
    exact hlastA
  have hlastB' : lastB.val + 1 =
      B.splitting.componentRank (A.componentMap B i) := by
    change lastB.val + 1 =
      B.splitting.componentRank (A.componentMap B i) at hlastB
    exact hlastB
  have himageVal' : imageLast.val = lastA.val := by
    simpa only [imageLast] using himageVal
  have himageLast : imageLast = lastB := by
    apply Fin.ext
    omega
  have hglobal := A.componentLocalOrderIso_global_eq B horders i lastA
  have hlastOrder :
      (A.componentBONG i).order lastA =
        (B.componentBONG (A.componentMap B i)).order lastB := by
    calc
      (A.componentBONG i).order lastA =
          a.order (A.putTogether.indexEquiv.symm ⟨i, lastA⟩) :=
        (A.putTogether.order_inverse_indexEquiv i lastA).symm
      _ = b.order (A.putTogether.indexEquiv.symm ⟨i, lastA⟩) :=
        horders _
      _ = b.order (B.putTogether.indexEquiv.symm
          ⟨A.componentMap B i, imageLast⟩) := by rw [hglobal]
      _ = (B.componentBONG (A.componentMap B i)).order imageLast :=
        B.putTogether.order_inverse_indexEquiv _ imageLast
      _ = (B.componentBONG (A.componentMap B i)).order lastB := by
        rw [himageLast]
  have hnorm := A.normGeneratorOrder_map_eq B horders i
  rw [A.splitting.componentLast_order_eq A.componentBONG i,
    B.splitting.componentLast_order_eq B.componentBONG
      (A.componentMap B i)] at hlastOrder
  omega

/-- The component counts of two equal good-BONG order sequences agree. -/
theorem componentCount_eq
    (A : GoodMaximalNormData a t) (B : GoodMaximalNormData b s)
    (horders : ∀ i, a.order i = b.order i) : t = s := by
  have hcard := Fintype.card_congr (A.componentEquiv B horders)
  simpa only [Fintype.card_fin] using hcard

/-- The unique order isomorphism between finite initial segments preserves
their numerical positions. -/
theorem componentMap_val_eq
    (horders : ∀ i, a.order i = b.order i) (i : Fin t) :
    (A.componentMap B i).val = i.val := by
  classical
  have hcard := JordanProfileIndexing.orderIso_fin_val_eq_card_Iio
    (A.componentOrderIso B horders) i
  have htarget : Fintype.card
      {x : Fin s // x < A.componentMap B i} =
      (A.componentMap B i).val := by
    rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  change i.val = Fintype.card
    {x : Fin s // x < A.componentMap B i} at hcard
  exact htarget.symm.trans hcard.symm

end GoodMaximalNormData

/-- Two equal order sequences equipped with maximal-norm splittings whose
components have been synchronously indexed. -/
structure GoodMaximalNormAlignment
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r N (m + 1)) (t : Nat) where
  source : GoodMaximalNormData a t
  target : GoodMaximalNormData b t
  componentRank_eq : ∀ i,
    source.splitting.componentRank i = target.splitting.componentRank i
  scaleOrder_eq : ∀ i,
    ordUnit K (source.splitting.scaleGenerator i) =
      ordUnit K (target.splitting.scaleGenerator i)
  normOrder_eq : ∀ i,
    ordUnit K (source.splitting.normGenerator i) =
      ordUnit K (target.splitting.normGenerator i)

/-- Equal good-BONG orders admit synchronously indexed maximal-norm data. -/
theorem GoodBONG.nonempty_goodMaximalNormAlignment
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r N (m + 1))
    (horders : ∀ i, a.order i = b.order i) :
    ∃ t, Nonempty (GoodMaximalNormAlignment a b t) := by
  rcases a.nonempty_goodMaximalNormData with ⟨t, ⟨A⟩⟩
  rcases b.nonempty_goodMaximalNormData with ⟨s, ⟨B⟩⟩
  have hts := GoodMaximalNormData.componentCount_eq A B horders
  subst s
  have hmap (i : Fin t) : A.componentMap B i = i := by
    apply Fin.ext
    exact A.componentMap_val_eq B horders i
  refine ⟨t, ⟨{
    source := A
    target := B
    componentRank_eq := ?_
    scaleOrder_eq := ?_
    normOrder_eq := ?_
  }⟩⟩
  · intro i
    simpa only [hmap i] using A.componentRank_map_eq B horders i
  · intro i
    simpa only [hmap i] using A.scaleGeneratorOrder_map_eq B horders i
  · intro i
    simpa only [hmap i] using A.normGeneratorOrder_map_eq B horders i

/-- Synchronously indexed weak Jordan decompositions together with the
endpoint witnesses carried through equal-scale amalgamation. -/
structure WeakJordanEndpointAlignment
    (a : BONG V q L (m + 1)) (b : BONG W r N (m + 1)) (t : Nat) where
  sourceWeak : Lattice.WeakJordanDecomposition q L t
  targetWeak : Lattice.WeakJordanDecomposition r N t
  sourceParity : sourceWeak.HasImproperEvenRank
  targetParity : targetWeak.HasImproperEvenRank
  sourceEndpoints : WeakJordanEndpointWitness a sourceWeak
  targetEndpoints : WeakJordanEndpointWitness b targetWeak
  componentRankFamily_eq :
    (fun i ↦ finrank K (sourceWeak.component i).carrier) =
      fun i ↦ finrank K (targetWeak.component i).carrier
  scaleOrderFamily_eq : sourceWeak.scaleOrderFamily =
    targetWeak.scaleOrderFamily
  normOrderFamily_eq : sourceWeak.normOrderFamily =
    targetWeak.normOrderFamily

/-- The aligned maximal-norm data give the initial aligned weak Jordan
endpoint witnesses. -/
noncomputable def GoodMaximalNormAlignment.toWeakJordanEndpointAlignment
    {a : GoodBONG q L (m + 1)} {b : GoodBONG r N (m + 1)} {t : Nat}
    (P : GoodMaximalNormAlignment a b t) :
    WeakJordanEndpointAlignment a.toBONG b.toBONG t where
  sourceWeak := P.source.splitting.toWeakJordan P.source.componentBONG
  targetWeak := P.target.splitting.toWeakJordan P.target.componentBONG
  sourceParity := P.source.splitting.toWeakJordan_hasImproperEvenRank
    P.source.componentBONG
  targetParity := P.target.splitting.toWeakJordan_hasImproperEvenRank
    P.target.componentBONG
  sourceEndpoints := P.source.splitting.weakJordanEndpointWitness
    P.source.componentBONG a.toBONG P.source.putTogether
  targetEndpoints := P.target.splitting.weakJordanEndpointWitness
    P.target.componentBONG b.toBONG P.target.putTogether
  componentRankFamily_eq := by
    funext i
    exact P.componentRank_eq i
  scaleOrderFamily_eq := by
    funext i
    exact P.scaleOrder_eq i
  normOrderFamily_eq := by
    funext i
    calc
      ordUnit K
          ((P.source.splitting.toWeakJordan P.source.componentBONG).normGeneratorUnit i) =
          ordUnit K (P.source.splitting.normGenerator i) :=
        P.source.splitting.toWeakJordan_normGeneratorOrder
          P.source.componentBONG i
      _ = ordUnit K (P.target.splitting.normGenerator i) :=
        P.normOrder_eq i
      _ = ordUnit K
          ((P.target.splitting.toWeakJordan P.target.componentBONG).normGeneratorUnit i) :=
        (P.target.splitting.toWeakJordan_normGeneratorOrder
          P.target.componentBONG i).symm

namespace WeakJordanEndpointAlignment

variable {a₀ : BONG V q L (m + 1)} {b₀ : BONG W r N (m + 1)}

/-- Merge the same equal-scale adjacent pair on both sides while preserving
all alignment data. -/
noncomputable def mergeAdjacentAt {t : Nat}
    (P : WeakJordanEndpointAlignment a₀ b₀ (t + 1)) (k : Fin t)
    (heq : ordUnit K (P.sourceWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.sourceWeak.scaleGenerator k.succ)) :
    WeakJordanEndpointAlignment a₀ b₀ t := by
  have heqTarget : ordUnit K (P.targetWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.targetWeak.scaleGenerator k.succ) := by
    have hleft := congrFun P.scaleOrderFamily_eq k.castSucc
    have hright := congrFun P.scaleOrderFamily_eq k.succ
    change ordUnit K (P.sourceWeak.scaleGenerator k.castSucc) =
      ordUnit K (P.targetWeak.scaleGenerator k.castSucc) at hleft
    change ordUnit K (P.sourceWeak.scaleGenerator k.succ) =
      ordUnit K (P.targetWeak.scaleGenerator k.succ) at hright
    exact hleft.symm.trans (heq.trans hright)
  exact {
    sourceWeak := P.sourceWeak.mergeAdjacentAt k heq
    targetWeak := P.targetWeak.mergeAdjacentAt k heqTarget
    sourceParity := P.sourceParity.mergeAdjacentAt P.sourceWeak k heq
    targetParity := P.targetParity.mergeAdjacentAt P.targetWeak k heqTarget
    sourceEndpoints := P.sourceEndpoints.mergeAdjacentAt
      P.sourceParity k heq
    targetEndpoints := P.targetEndpoints.mergeAdjacentAt
      P.targetParity k heqTarget
    componentRankFamily_eq := by
      funext j
      by_cases hj : j = k
      · subst j
        rw [P.sourceWeak.mergeAdjacentAt_componentRank_self k heq,
          P.targetWeak.mergeAdjacentAt_componentRank_self k heqTarget]
        rw [congrFun P.componentRankFamily_eq k.castSucc,
          congrFun P.componentRankFamily_eq k.succ]
      · rw [P.sourceWeak.mergeAdjacentAt_component_of_ne k heq j hj,
          P.targetWeak.mergeAdjacentAt_component_of_ne k heqTarget j hj]
        exact congrFun P.componentRankFamily_eq (k.succ.succAbove j)
    scaleOrderFamily_eq := by
      rw [P.sourceWeak.scaleOrderFamily_mergeAdjacentAt k heq,
        P.targetWeak.scaleOrderFamily_mergeAdjacentAt k heqTarget,
        P.scaleOrderFamily_eq]
    normOrderFamily_eq := by
      rw [P.sourceWeak.normOrderFamily_mergeAdjacentAt k heq,
        P.targetWeak.normOrderFamily_mergeAdjacentAt k heqTarget,
        P.normOrderFamily_eq]
  }

end WeakJordanEndpointAlignment

/-- The result of synchronously amalgamating all equal-scale neighbours. -/
structure StrictJordanEndpointAlignment
    (a : BONG V q L (m + 1)) (b : BONG W r N (m + 1)) where
  componentCount : Nat
  weakAlignment : WeakJordanEndpointAlignment a b componentCount
  sourceStrict : StrictMono (fun i ↦
    ordUnit K (weakAlignment.sourceWeak.scaleGenerator i))
  targetStrict : StrictMono (fun i ↦
    ordUnit K (weakAlignment.targetWeak.scaleGenerator i))

namespace WeakJordanEndpointAlignment

variable {a₀ : BONG V q L (m + 1)} {b₀ : BONG W r N (m + 1)}

/-- Synchronous equal-scale amalgamation terminates with strict Jordan
scale sequences on both sides. -/
theorem exists_strict :
    ∀ (t : Nat) (_P : WeakJordanEndpointAlignment a₀ b₀ t),
      Nonempty (StrictJordanEndpointAlignment a₀ b₀) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro P
      let f : Fin t → Int := fun i ↦
        ordUnit K (P.sourceWeak.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · have htarget : StrictMono (fun i ↦
            ordUnit K (P.targetWeak.scaleGenerator i)) := by
          change StrictMono P.targetWeak.scaleOrderFamily
          rw [← P.scaleOrderFamily_eq]
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
                  P.sourceWeak.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K
                      (P.sourceWeak.scaleGenerator k.castSucc) =
                    ordUnit K (P.sourceWeak.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                exact ih (d + 1) (by omega) (P.mergeAdjacentAt k heq)

end WeakJordanEndpointAlignment

namespace StrictJordanEndpointAlignment

variable {a₀ : BONG V q L (m + 1)} {b₀ : BONG W r N (m + 1)}
  (S : StrictJordanEndpointAlignment a₀ b₀)

/-- The aligned strict source Jordan decomposition. -/
noncomputable def sourceJordan :
    Lattice.JordanDecomposition q L S.componentCount :=
  S.weakAlignment.sourceWeak.toJordan S.sourceStrict

/-- The aligned strict target Jordan decomposition. -/
noncomputable def targetJordan :
    Lattice.JordanDecomposition r N S.componentCount :=
  S.weakAlignment.targetWeak.toJordan S.targetStrict

/-- The aligned strict components have the same ranks, pointwise. -/
theorem componentRankFamily_eq :
    S.sourceJordan.componentRank = S.targetJordan.componentRank := by
  funext i
  exact congrFun S.weakAlignment.componentRankFamily_eq i

/-- The aligned strict components have the same scale orders, pointwise. -/
theorem scaleOrderFamily_eq :
    (fun i ↦ S.sourceJordan.fundamentalScaleOrder i) =
      fun i ↦ S.targetJordan.fundamentalScaleOrder i := by
  funext i
  exact congrFun S.weakAlignment.scaleOrderFamily_eq i

/-- The chosen strict Jordan norm generators have the same orders. -/
theorem normOrderFamily_eq :
    (fun i ↦ ordUnit K (S.sourceJordan.normGenerator i)) =
      fun i ↦ ordUnit K (S.targetJordan.normGenerator i) := by
  funext i
  exact congrFun S.weakAlignment.normOrderFamily_eq i

/-- Equal component ranks force both weak profile enumerations to attach the
same component number and numerical local coordinate to every global BONG
index, even though the two lattices may have different carrier types. -/
theorem profile_coordinates_eq (i : Fin (m + 1)) :
    (S.weakAlignment.sourceEndpoints.profile.indexEquiv i).1 =
        (S.weakAlignment.targetEndpoints.profile.indexEquiv i).1 ∧
      (S.weakAlignment.sourceEndpoints.profile.indexEquiv i).2.val =
        (S.weakAlignment.targetEndpoints.profile.indexEquiv i).2.val := by
  let E := JordanProfileIndexing.lexSigmaRankOrderIso
    (fun k ↦ finrank K (S.weakAlignment.sourceWeak.component k).carrier)
    (fun k ↦ finrank K (S.weakAlignment.targetWeak.component k).carrier)
    S.weakAlignment.componentRankFamily_eq
  have hIso :
      S.weakAlignment.sourceEndpoints.profile.indexOrderIso.trans E =
        S.weakAlignment.targetEndpoints.profile.indexOrderIso :=
    Subsingleton.elim _ _
  have happ := congrArg (fun e ↦ e i) hIso
  have hfirst := congrArg (fun z ↦ (ofLex z).1) happ
  have hsecond := congrArg (fun z ↦ (ofLex z).2.val) happ
  exact ⟨by simpa [E, BONG.WeakJordanOrderProfileWitness.indexOrderIso]
      using hfirst,
    by simpa [E, BONG.WeakJordanOrderProfileWitness.indexOrderIso]
      using hsecond⟩

/-- The retained first endpoint is a norm generator of the source
fundamental lattice at the same scale. -/
theorem sourceFirstGenerator_fundamentalLattice
    (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue q (S.sourceJordan.fundamentalLattice i)
      (S.weakAlignment.sourceEndpoints.profile.endpointFirstValue i) := by
  apply S.sourceJordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.weakAlignment.sourceEndpoints.firstGenerator i
  · change S.weakAlignment.sourceWeak.effectiveNormOrderAt i
        (ordUnit K (S.weakAlignment.sourceWeak.scaleGenerator i)) =
      ordUnit K (S.weakAlignment.sourceWeak.normGeneratorUnit i)
    exact (S.weakAlignment.sourceEndpoints.normOrder_eq_effective i).symm

/-- The retained first endpoint is a norm generator of the target
fundamental lattice at the same scale. -/
theorem targetFirstGenerator_fundamentalLattice
    (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue r (S.targetJordan.fundamentalLattice i)
      (S.weakAlignment.targetEndpoints.profile.endpointFirstValue i) := by
  apply S.targetJordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.weakAlignment.targetEndpoints.firstGenerator i
  · change S.weakAlignment.targetWeak.effectiveNormOrderAt i
        (ordUnit K (S.weakAlignment.targetWeak.scaleGenerator i)) =
      ordUnit K (S.weakAlignment.targetWeak.normGeneratorUnit i)
    exact (S.weakAlignment.targetEndpoints.normOrder_eq_effective i).symm

/-- The retained terminal endpoint is a norm generator of the source
fundamental lattice at the same scale. -/
theorem sourceTerminalGenerator_fundamentalLattice
    (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue q (S.sourceJordan.fundamentalLattice i)
      (S.weakAlignment.sourceEndpoints.profile.endpointTerminalValue i) := by
  apply S.sourceJordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.weakAlignment.sourceEndpoints.terminalGenerator i
  · change S.weakAlignment.sourceWeak.effectiveNormOrderAt i
        (ordUnit K (S.weakAlignment.sourceWeak.scaleGenerator i)) =
      ordUnit K (S.weakAlignment.sourceWeak.normGeneratorUnit i)
    exact (S.weakAlignment.sourceEndpoints.normOrder_eq_effective i).symm

/-- The retained terminal endpoint is a norm generator of the target
fundamental lattice at the same scale. -/
theorem targetTerminalGenerator_fundamentalLattice
    (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue r (S.targetJordan.fundamentalLattice i)
      (S.weakAlignment.targetEndpoints.profile.endpointTerminalValue i) := by
  apply S.targetJordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.weakAlignment.targetEndpoints.terminalGenerator i
  · change S.weakAlignment.targetWeak.effectiveNormOrderAt i
        (ordUnit K (S.weakAlignment.targetWeak.scaleGenerator i)) =
      ordUnit K (S.weakAlignment.targetWeak.normGeneratorUnit i)
    exact (S.weakAlignment.targetEndpoints.normOrder_eq_effective i).symm

/-- A nonempty good BONG cannot yield an empty strict Jordan family. -/
theorem componentCount_pos : 0 < S.componentCount := by
  by_contra hnot
  have hzero : S.componentCount = 0 := by omega
  let first : Fin (m + 1) := 0
  have impossible :=
    (S.weakAlignment.sourceEndpoints.profile.indexEquiv first).1
  have himpossible : impossible.val < S.componentCount := impossible.isLt
  omega

end StrictJordanEndpointAlignment

/-- Equal good-BONG orders admit aligned strict Jordan endpoint data. -/
theorem GoodBONG.nonempty_strictJordanEndpointAlignment
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r N (m + 1))
    (horders : ∀ i, a.order i = b.order i) :
    Nonempty (StrictJordanEndpointAlignment a.toBONG b.toBONG) := by
  rcases a.nonempty_goodMaximalNormAlignment b horders with ⟨t, ⟨P⟩⟩
  exact WeakJordanEndpointAlignment.exists_strict t
    P.toWeakJordanEndpointAlignment

end BONG

end Bong
