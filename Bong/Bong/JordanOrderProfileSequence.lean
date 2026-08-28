/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas45To47
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sigma.Order
import Mathlib.Order.Interval.Finset.Fin

/-!
# Canonical indexing of a Jordan order profile

The index equivalence in `JordanOrderProfileWitness` is not extra
mathematical data.  Its order-preservation condition makes it the unique
order isomorphism from the global finite index to the lexicographically
ordered dependent family of component indices.  This file exposes that
fact so later Jordan calculations can use a canonical, inspectable index
map.
-/

open scoped BigOperators

namespace JordanProfileIndexing

/-- Pointwise equality of the component-rank families induces the canonical
order isomorphism between their lexicographic dependent index sets. -/
noncomputable def lexSigmaRankOrderIso {t : Nat}
    (r s : Fin t → Nat) (h : r = s) :
    Lex (Σ k : Fin t, Fin (r k)) ≃o
      Lex (Σ k : Fin t, Fin (s k)) := by
  subst s
  exact OrderIso.refl _

@[simp]
theorem lexSigmaRankOrderIso_apply_fst {t : Nat}
    (r s : Fin t → Nat) (h : r = s)
    (k : Fin t) (i : Fin (r k)) :
    (ofLex (lexSigmaRankOrderIso r s h (toLex ⟨k, i⟩))).1 = k := by
  subst s
  rfl

@[simp]
theorem lexSigmaRankOrderIso_apply_snd_val {t : Nat}
    (r s : Fin t → Nat) (h : r = s)
    (k : Fin t) (i : Fin (r k)) :
    (ofLex (lexSigmaRankOrderIso r s h (toLex ⟨k, i⟩))).2.val = i.val := by
  subst s
  rfl

@[simp]
theorem lexSigmaRankOrderIso_apply_fst' {t : Nat}
    (r s : Fin t → Nat) (h : r = s)
    (z : Σ k : Fin t, Fin (r k)) :
    (ofLex (lexSigmaRankOrderIso r s h (toLex z))).1 = z.1 := by
  rcases z with ⟨k, i⟩
  exact lexSigmaRankOrderIso_apply_fst r s h k i

@[simp]
theorem lexSigmaRankOrderIso_apply_snd_val' {t : Nat}
    (r s : Fin t → Nat) (h : r = s)
    (z : Σ k : Fin t, Fin (r k)) :
    (ofLex (lexSigmaRankOrderIso r s h (toLex z))).2.val = z.2.val := by
  rcases z with ⟨k, i⟩
  exact lexSigmaRankOrderIso_apply_snd_val r s h k i

/-- The number of lexicographic dependent indices before `(k,i)` is the
sum of all earlier fiber sizes plus the local index `i`. -/
theorem lexSigmaIio_card {t : Nat} (r : Fin t → Nat)
    (k : Fin t) (i : Fin (r k)) :
    Fintype.card {x : Lex (Σ j : Fin t, Fin (r j)) //
      x < toLex ⟨k, i⟩} =
      (∑ j ∈ Finset.Iio k, r j) + i.val := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ x : (Σ j : Fin t, Fin (r j)),
    if toLex x < toLex ⟨k, i⟩ then 1 else 0) = _
  rw [Fintype.sum_sigma]
  simp only [Sigma.Lex.lt_def]
  change (∑ j : Fin t, ∑ a : Fin (r j),
    if j < k ∨ ∃ h : j = k, h ▸ a < i then 1 else 0) = _
  have hinner (j : Fin t) :
      (∑ a : Fin (r j),
        if j < k ∨ ∃ h : j = k, h ▸ a < i then 1 else 0) =
        if j < k then r j else if h : j = k then i.val else 0 := by
    by_cases hjk : j < k
    · simp [hjk]
    · by_cases hEq : j = k
      · subst j
        simp only [lt_self_iff_false, false_or, if_false]
        simp only [exists_true_left]
        rw [dif_pos trivial]
        rw [← Finset.sum_filter, Finset.filter_gt_eq_Iio]
        simpa using Fin.card_Iio i
      · simp [hjk, hEq]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.filter_gt_eq_Iio]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · simp

/-- An order isomorphism from `Fin n` enumerates its finite target by the
cardinality of strict lower intervals. -/
theorem orderIso_fin_val_eq_card_Iio {α : Type*} [LinearOrder α]
    [Fintype α] {n : Nat} (e : Fin n ≃o α) (i : Fin n) :
    i.val = Fintype.card {x : α // x < e i} := by
  classical
  let f : {j : Fin n // j < i} ≃ {x : α // x < e i} := {
    toFun := fun j => ⟨e j, e.lt_iff_lt.mpr j.property⟩
    invFun := fun x => ⟨e.symm x, by
      have hx := e.symm.lt_iff_lt.mpr x.property
      simpa using hx⟩
    left_inv := by
      intro j
      apply Subtype.ext
      exact e.symm_apply_apply j
    right_inv := by
      intro x
      apply Subtype.ext
      exact e.apply_symm_apply x
  }
  calc
    i.val = (Finset.Iio i).card := (Fin.card_Iio i).symm
    _ = Fintype.card {j : Fin n // j < i} := by
      rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio]
    _ = Fintype.card {x : α // x < e i} := Fintype.card_congr f

end JordanProfileIndexing

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG.JordanOrderProfileWitness

/-- `ComponentIndexBefore` is exactly the strict order on the lexicographic
dependent sum. -/
theorem componentIndexBefore_iff_lex_lt
    (D : Lattice.OrthogonalDecomposition q L t)
    (a b : Σ k : Fin t, Fin (D.componentRank k)) :
    BONG.ComponentIndexBefore D a b ↔ toLex a < toLex b := by
  rcases a with ⟨ka, ia⟩
  rcases b with ⟨kb, ib⟩
  simp only [BONG.ComponentIndexBefore, Sigma.Lex.lt_def]
  change (ka.1 < kb.1 ∨ ka = kb ∧ ia.1 < ib.1) ↔
    (ka < kb ∨ ∃ h : ka = kb, h ▸ ia < ib)
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

/-- A Jordan profile witness determines an actual order isomorphism, not
merely an unstructured equivalence of finite index types. -/
noncomputable def indexOrderIso
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) :
    Fin n ≃o Lex (Σ k : Fin t,
      Fin (J.toOrthogonalDecomposition.componentRank k)) where
  toFun i := toLex (w.indexEquiv i)
  invFun a := w.indexEquiv.symm (ofLex a)
  left_inv i := by
    change w.indexEquiv.symm (w.indexEquiv i) = i
    exact w.indexEquiv.symm_apply_apply i
  right_inv a := by
    change toLex (w.indexEquiv (w.indexEquiv.symm (ofLex a))) = a
    rw [w.indexEquiv.apply_symm_apply]
    exact toLex_ofLex a
  map_rel_iff' := by
    intro i j
    change toLex (w.indexEquiv i) ≤ toLex (w.indexEquiv j) ↔ i ≤ j
    constructor
    · intro hij
      apply le_of_not_gt
      intro hji
      have hcomponent := (w.order_iff j i).mp hji
      have hlex := (componentIndexBefore_iff_lex_lt
        J.toOrthogonalDecomposition (w.indexEquiv j) (w.indexEquiv i)).mp
        hcomponent
      exact (not_lt_of_ge hij) hlex
    · intro hij
      apply le_of_not_gt
      intro hlex
      have hcomponent := (componentIndexBefore_iff_lex_lt
        J.toOrthogonalDecomposition (w.indexEquiv j) (w.indexEquiv i)).mpr
        hlex
      have hji := (w.order_iff j i).mpr hcomponent
      exact (not_lt_of_ge hij) hji

/-- For a fixed Jordan decomposition, all profile witnesses use the same
global-to-component index map. -/
theorem indexEquiv_eq
    {b c : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (z : BONG.JordanOrderProfileWitness c J) :
    w.indexEquiv = z.indexEquiv := by
  apply Equiv.ext
  intro i
  have hi : w.indexOrderIso i = z.indexOrderIso i := by
    rw [Subsingleton.elim w.indexOrderIso z.indexOrderIso]
  change toLex (w.indexEquiv i) = toLex (z.indexEquiv i) at hi
  exact toLex_inj.mp hi

/-- Profile witnesses for two Jordan decompositions with pointwise equal
component ranks select the same component and the same numerical local
coordinate at every global index. -/
theorem indexEquiv_coordinates_eq_of_componentRank_eq
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {b : BONG V q L n} {c : BONG W r M n}
    {J : Lattice.JordanDecomposition q L t}
    {H : Lattice.JordanDecomposition r M t}
    (x : BONG.JordanOrderProfileWitness b J)
    (y : BONG.JordanOrderProfileWitness c H)
    (hRank : J.toOrthogonalDecomposition.componentRank =
      H.toOrthogonalDecomposition.componentRank)
    (i : Fin n) :
    (x.indexEquiv i).1 = (y.indexEquiv i).1 ∧
      (x.indexEquiv i).2.val = (y.indexEquiv i).2.val := by
  let E := JordanProfileIndexing.lexSigmaRankOrderIso
    J.toOrthogonalDecomposition.componentRank
    H.toOrthogonalDecomposition.componentRank hRank
  have hIso : x.indexOrderIso.trans E = y.indexOrderIso :=
    Subsingleton.elim _ _
  have happ := congrArg (fun e ↦ e i) hIso
  have hfirst := congrArg (fun z ↦ (ofLex z).1) happ
  have hsecond := congrArg (fun z ↦ (ofLex z).2.val) happ
  exact ⟨by simpa [E, indexOrderIso] using hfirst,
    by simpa [E, indexOrderIso] using hsecond⟩

/-- The profile value at a global index, expressed through the canonical
component index selected by the witness. -/
noncomputable def expectedOrder
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) (i : Fin n) : Int :=
  BONG.jordanExpectedOrder J (w.indexEquiv i).1 (w.indexEquiv i).2

@[simp]
theorem order_eq_expectedOrder
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) (i : Fin n) :
    b.order i = w.expectedOrder i :=
  w.order_eq i

/-- Expected profile values do not depend on which good BONG supplied the
profile witness. -/
theorem expectedOrder_eq
    {b c : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (z : BONG.JordanOrderProfileWitness c J) (i : Fin n) :
    w.expectedOrder i = z.expectedOrder i := by
  rw [expectedOrder, expectedOrder, w.indexEquiv_eq z]

/-- The order-invariance conclusion of Beli's Lemma 4.7 follows from its
Jordan-profile assertion; it is not an independent local law. -/
theorem orders_eq_of_profiles
    {b c : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (z : BONG.JordanOrderProfileWitness c J) (i : Fin n) :
    b.order i = c.order i := by
  rw [w.order_eq_expectedOrder, z.order_eq_expectedOrder,
    w.expectedOrder_eq z]

/-- The numerical global index is the sum of the ranks of all previous
Jordan components and the local index inside the current component. -/
theorem index_val_eq_componentStart_add_local
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) (i : Fin n) :
    i.val =
      (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
        J.toOrthogonalDecomposition.componentRank k) +
      (w.indexEquiv i).2.val := by
  calc
    i.val = Fintype.card {x : Lex (Σ k : Fin t,
        Fin (J.toOrthogonalDecomposition.componentRank k)) //
        x < w.indexOrderIso i} :=
      JordanProfileIndexing.orderIso_fin_val_eq_card_Iio
        w.indexOrderIso i
    _ = _ := by
      change Fintype.card {x : Lex (Σ k : Fin t,
          Fin (J.toOrthogonalDecomposition.componentRank k)) //
          x < toLex (w.indexEquiv i)} = _
      exact JordanProfileIndexing.lexSigmaIio_card
        J.toOrthogonalDecomposition.componentRank
        (w.indexEquiv i).1 (w.indexEquiv i).2

/-- The inverse index map sends a specified component/local position to its
exact prefix-rank offset. -/
theorem inverse_index_val
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (k : Fin t)
    (j : Fin (J.toOrthogonalDecomposition.componentRank k)) :
    (w.indexEquiv.symm ⟨k, j⟩).val =
      (∑ h ∈ Finset.Iio k,
        J.toOrthogonalDecomposition.componentRank h) + j.val := by
  have h := w.index_val_eq_componentStart_add_local
    (w.indexEquiv.symm ⟨k, j⟩)
  have heq : w.indexEquiv (w.indexEquiv.symm ⟨k, j⟩) = ⟨k, j⟩ :=
    w.indexEquiv.apply_symm_apply ⟨k, j⟩
  rw [heq] at h
  exact h

/-- The total of the Jordan component ranks is the length of every BONG
profiled by that decomposition. -/
theorem sum_componentRank_eq_length
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) :
    (∑ k, J.toOrthogonalDecomposition.componentRank k) = n := by
  simpa only [Fintype.card_fin, Fintype.card_sigma] using
    (Fintype.card_congr w.indexEquiv).symm

/-- Two profile witnesses select the same component and numerical local
coordinate at a given global index as soon as the component ranks agree at
that component and their prefix-rank sums agree before it.  This localized
form is what is needed when two Jordan decompositions differ only by an
adjacent transposition of components. -/
theorem indexEquiv_coordinates_eq_of_prefix_and_rank_eq
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {b : BONG V q L n} {c : BONG W r M n}
    {J : Lattice.JordanDecomposition q L t}
    {H : Lattice.JordanDecomposition r M t}
    (x : BONG.JordanOrderProfileWitness b J)
    (y : BONG.JordanOrderProfileWitness c H)
    (i : Fin n)
    (hPrefix :
      (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
          J.toOrthogonalDecomposition.componentRank h) =
        ∑ h ∈ Finset.Iio (x.indexEquiv i).1,
          H.toOrthogonalDecomposition.componentRank h)
    (hRank : J.toOrthogonalDecomposition.componentRank
        (x.indexEquiv i).1 =
      H.toOrthogonalDecomposition.componentRank (x.indexEquiv i).1) :
    (x.indexEquiv i).1 = (y.indexEquiv i).1 ∧
      (x.indexEquiv i).2.val = (y.indexEquiv i).2.val := by
  let j : Fin (H.toOrthogonalDecomposition.componentRank
      (x.indexEquiv i).1) :=
    ⟨(x.indexEquiv i).2.val, by rw [← hRank]; exact (x.indexEquiv i).2.isLt⟩
  let z : Fin n := y.indexEquiv.symm ⟨(x.indexEquiv i).1, j⟩
  have hzVal : z.val = i.val := by
    calc
      z.val =
          (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
            H.toOrthogonalDecomposition.componentRank h) + j.val := by
        exact y.inverse_index_val (x.indexEquiv i).1 j
      _ = (∑ h ∈ Finset.Iio (x.indexEquiv i).1,
            J.toOrthogonalDecomposition.componentRank h) +
          (x.indexEquiv i).2.val := by
        rw [← hPrefix]
      _ = i.val := (x.index_val_eq_componentStart_add_local i).symm
  have hz : z = i := Fin.ext hzVal
  have hy : y.indexEquiv i = ⟨(x.indexEquiv i).1, j⟩ := by
    calc
      y.indexEquiv i = y.indexEquiv z := congrArg y.indexEquiv hz.symm
      _ = ⟨(x.indexEquiv i).1, j⟩ :=
        y.indexEquiv.apply_symm_apply _
  constructor
  · exact (congrArg Sigma.fst hy).symm
  · exact (congrArg (fun a => a.2.val) hy).symm

/-- Consecutive local coordinates in one component correspond to
consecutive global coordinates. -/
theorem inverse_index_val_local_succ
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (k : Fin t)
    (j : Fin (J.toOrthogonalDecomposition.componentRank k))
    (hnext : j.val + 1 < J.toOrthogonalDecomposition.componentRank k) :
    (w.indexEquiv.symm
        ⟨k, ⟨j.val + 1, hnext⟩⟩).val =
      (w.indexEquiv.symm ⟨k, j⟩).val + 1 := by
  rw [w.inverse_index_val, w.inverse_index_val]
  simp only [Fin.val_mk]
  omega

/-- The preceding local coordinate is one global position before the
current coordinate. -/
theorem inverse_index_val_local_pred
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (k : Fin t)
    (j : Fin (J.toOrthogonalDecomposition.componentRank k))
    (hpos : 0 < j.val) :
    (w.indexEquiv.symm
        ⟨k, ⟨j.val - 1, by omega⟩⟩).val + 1 =
      (w.indexEquiv.symm ⟨k, j⟩).val := by
  rw [w.inverse_index_val, w.inverse_index_val]
  simp only [Fin.val_mk]
  omega

/-- The last local coordinate of a component and the first coordinate of
the next component are consecutive global coordinates. -/
theorem inverse_index_val_next_component
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (k k' : Fin t) (hk' : k'.val = k.val + 1)
    (j : Fin (J.toOrthogonalDecomposition.componentRank k))
    (hlast : j.val + 1 =
      J.toOrthogonalDecomposition.componentRank k)
    (hpos : 0 < J.toOrthogonalDecomposition.componentRank k') :
    (w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩).val =
      (w.indexEquiv.symm ⟨k, j⟩).val + 1 := by
  classical
  have hset : Finset.Iio k' = insert k (Finset.Iio k) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change (x.val < k'.val) ↔ x = k ∨ x.val < k.val
    constructor
    · intro hx
      by_cases hxl : x.val < k.val
      · exact Or.inr hxl
      · left
        apply Fin.ext
        omega
    · rintro (rfl | hx)
      · omega
      · omega
  rw [w.inverse_index_val, w.inverse_index_val, hset,
    Finset.sum_insert (by simp)]
  simp only [Fin.val_mk]
  omega

/-- When a local successor exists, its Jordan profile value is the value at
the next global BONG coordinate. -/
theorem order_succ_eq_jordanExpectedOrder_of_local_succ
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (i : Fin n) (hglobal : i.val + 1 < n)
    (hlocal : (w.indexEquiv i).2.val + 1 <
      J.toOrthogonalDecomposition.componentRank (w.indexEquiv i).1) :
    b.order ⟨i.val + 1, hglobal⟩ =
      BONG.jordanExpectedOrder J (w.indexEquiv i).1
        ⟨(w.indexEquiv i).2.val + 1, hlocal⟩ := by
  have hval := w.inverse_index_val_local_succ
    (w.indexEquiv i).1 (w.indexEquiv i).2 hlocal
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val + 1, hglobal⟩ : Fin n) =
      w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩ := by
    have hval' :
        (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1,
            ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩).val =
          i.val + 1 := by
      calc
        _ = (w.indexEquiv.symm (w.indexEquiv i)).val + 1 := by
          simpa using hval
        _ = i.val + 1 := by rw [hcurrent]
    apply Fin.ext
    exact hval'.symm
  rw [hindex]
  have h := w.order_eq
    (w.indexEquiv.symm
      ⟨(w.indexEquiv i).1,
        ⟨(w.indexEquiv i).2.val + 1, hlocal⟩⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- When a local predecessor exists, its Jordan profile value is the value
at the preceding global BONG coordinate. -/
theorem order_pred_eq_jordanExpectedOrder_of_local_pred
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (i : Fin n) (hpos : 0 < (w.indexEquiv i).2.val) :
    b.order ⟨i.val - 1, by
      have := i.isLt
      omega⟩ =
      BONG.jordanExpectedOrder J (w.indexEquiv i).1
        ⟨(w.indexEquiv i).2.val - 1, by omega⟩ := by
  have hval := w.inverse_index_val_local_pred
    (w.indexEquiv i).1 (w.indexEquiv i).2 hpos
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val - 1, by
      have := i.isLt
      omega⟩ : Fin n) =
      w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩ := by
    have hval' :
        (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1,
            ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩).val + 1 =
          i.val := by
      calc
        _ = (w.indexEquiv.symm (w.indexEquiv i)).val := by
          simpa using hval
        _ = i.val := by rw [hcurrent]
    apply Fin.ext
    change i.val - 1 =
      (w.indexEquiv.symm
        ⟨(w.indexEquiv i).1,
          ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩).val
    omega
  rw [hindex]
  have h := w.order_eq
    (w.indexEquiv.symm
      ⟨(w.indexEquiv i).1,
        ⟨(w.indexEquiv i).2.val - 1, by omega⟩⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- At a component endpoint, the first profile value of the next component
is the next global BONG coordinate. -/
theorem order_succ_eq_jordanExpectedOrder_of_next_component
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (i : Fin n) (hglobal : i.val + 1 < n)
    (k' : Fin t) (hk' : k'.val = (w.indexEquiv i).1.val + 1)
    (hlast : (w.indexEquiv i).2.val + 1 =
      J.toOrthogonalDecomposition.componentRank (w.indexEquiv i).1)
    (hpos : 0 < J.toOrthogonalDecomposition.componentRank k') :
    b.order ⟨i.val + 1, hglobal⟩ =
      BONG.jordanExpectedOrder J k' ⟨0, hpos⟩ := by
  have hval := w.inverse_index_val_next_component
    (w.indexEquiv i).1 k' hk' (w.indexEquiv i).2 hlast hpos
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hindex : (⟨i.val + 1, hglobal⟩ : Fin n) =
      w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩ := by
    have hval' : (w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩).val =
        i.val + 1 := by
      calc
        _ = (w.indexEquiv.symm (w.indexEquiv i)).val + 1 := by
          simpa using hval
        _ = i.val + 1 := by rw [hcurrent]
    apply Fin.ext
    exact hval'.symm
  rw [hindex]
  have h := w.order_eq (w.indexEquiv.symm ⟨k', ⟨0, hpos⟩⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- A positive-rank component immediately preceding the current component
forces the current global index to be positive. -/
theorem index_val_pos_of_previous_component
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (i : Fin n) (k : Fin t)
    (hk : (w.indexEquiv i).1.val = k.val + 1)
    (hpos : 0 < J.toOrthogonalDecomposition.componentRank k) :
    0 < i.val := by
  have hindex := w.index_val_eq_componentStart_add_local i
  have hmem : k ∈ Finset.Iio (w.indexEquiv i).1 := by
    simp only [Finset.mem_Iio]
    change k.val < (w.indexEquiv i).1.val
    omega
  have hsumPos : 0 < ∑ j ∈ Finset.Iio (w.indexEquiv i).1,
      J.toOrthogonalDecomposition.componentRank j := by
    exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
      ⟨k, hmem, hpos⟩
  omega

/-- At the first local coordinate of a component, the preceding global BONG
coordinate is the last profile value of the preceding component. -/
theorem order_pred_eq_jordanExpectedOrder_of_previous_component
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (i : Fin n) (hglobal : 0 < i.val)
    (k : Fin t)
    (hk : (w.indexEquiv i).1.val = k.val + 1)
    (hfirst : (w.indexEquiv i).2.val = 0)
    (hpos : 0 < J.toOrthogonalDecomposition.componentRank k)
    (hcurrentPos : 0 <
      J.toOrthogonalDecomposition.componentRank (w.indexEquiv i).1) :
    b.order ⟨i.val - 1, by omega⟩ =
      BONG.jordanExpectedOrder J k
        ⟨J.toOrthogonalDecomposition.componentRank k - 1, by omega⟩ := by
  let last : Fin (J.toOrthogonalDecomposition.componentRank k) :=
    ⟨J.toOrthogonalDecomposition.componentRank k - 1, by omega⟩
  have hlast : last.val + 1 =
      J.toOrthogonalDecomposition.componentRank k := by
    simp only [last]
    omega
  have hval := w.inverse_index_val_next_component
    k (w.indexEquiv i).1 hk last hlast hcurrentPos
  have hzeroInverse :
      (w.indexEquiv.symm
        ⟨(w.indexEquiv i).1, ⟨0, hcurrentPos⟩⟩).val =
        (w.indexEquiv.symm (w.indexEquiv i)).val := by
    rw [w.inverse_index_val, w.inverse_index_val]
    simp only [Fin.val_mk, hfirst, add_zero]
  have hcurrent : w.indexEquiv.symm (w.indexEquiv i) = i :=
    w.indexEquiv.symm_apply_apply i
  have hprevVal :
      (w.indexEquiv.symm ⟨k, last⟩).val + 1 = i.val := by
    calc
      _ = (w.indexEquiv.symm
          ⟨(w.indexEquiv i).1, ⟨0, hcurrentPos⟩⟩).val := hval.symm
      _ = (w.indexEquiv.symm (w.indexEquiv i)).val := hzeroInverse
      _ = i.val := by rw [hcurrent]
  have hindex : (⟨i.val - 1, by omega⟩ : Fin n) =
      w.indexEquiv.symm ⟨k, last⟩ := by
    apply Fin.ext
    change i.val - 1 = (w.indexEquiv.symm ⟨k, last⟩).val
    omega
  rw [hindex]
  have h := w.order_eq (w.indexEquiv.symm ⟨k, last⟩)
  rw [w.indexEquiv.apply_symm_apply] at h
  exact h

/-- At a specified component/local position, the global BONG order is the
corresponding Jordan alternating-profile value. -/
theorem order_inverse_indexEquiv
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J)
    (k : Fin t)
    (j : Fin (J.toOrthogonalDecomposition.componentRank k)) :
    b.order (w.indexEquiv.symm ⟨k, j⟩) =
      BONG.jordanExpectedOrder J k j := by
  have h := w.order_eq (w.indexEquiv.symm ⟨k, j⟩)
  have heq : w.indexEquiv (w.indexEquiv.symm ⟨k, j⟩) = ⟨k, j⟩ :=
    w.indexEquiv.apply_symm_apply ⟨k, j⟩
  rw [heq] at h
  exact h

/-- The prefix-rank start of the current component is no larger than the
global index. -/
theorem componentStart_le_index_val
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) (i : Fin n) :
    (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
      J.toOrthogonalDecomposition.componentRank k) ≤ i.val := by
  rw [w.index_val_eq_componentStart_add_local i]
  exact Nat.le_add_right _ _

/-- A global index lies strictly before the end of its current component. -/
theorem index_val_lt_componentEnd
    {b : BONG V q L n} {J : Lattice.JordanDecomposition q L t}
    (w : BONG.JordanOrderProfileWitness b J) (i : Fin n) :
    i.val <
      (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
        J.toOrthogonalDecomposition.componentRank k) +
      J.toOrthogonalDecomposition.componentRank (w.indexEquiv i).1 := by
  rw [w.index_val_eq_componentStart_add_local i]
  exact Nat.add_lt_add_left (w.indexEquiv i).2.isLt _

end BONG.JordanOrderProfileWitness

end Bong
