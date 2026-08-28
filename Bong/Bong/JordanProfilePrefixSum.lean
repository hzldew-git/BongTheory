/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSums
import Bong.Bong.JordanProfileMerge

/-!
# Prefix sums of weak Jordan order profiles

This file identifies a global BONG prefix sum with the sum of the complete
weak Jordan components lying before the current component and the partial
alternating sum inside the current component.  The statement supplies the
global bookkeeping used in Beli (2019), Lemma 5.13(ii); its arithmetic input
is the local two-step calculation in `JordanProfileOrder`.
-/

open scoped BigOperators

namespace JordanProfileIndexing

/-- Summing a function over the strict lexicographic lower interval of a
dependent component coordinate splits into all complete earlier fibers and
the strict lower interval in the current fiber. -/
theorem lexSigmaIio_sum {t : Nat} (rank : Fin t → Nat)
    (f : (k : Fin t) → Fin (rank k) → Int)
    (k : Fin t) (i : Fin (rank k)) :
    (∑ x : {x : Lex (Σ j : Fin t, Fin (rank j)) //
        x < toLex ⟨k, i⟩},
      f (ofLex x.1).1 (ofLex x.1).2) =
      (∑ j ∈ Finset.Iio k, ∑ a : Fin (rank j), f j a) +
        ∑ a : Fin (rank k), if a < i then f k a else 0 := by
  classical
  let p : Lex (Σ j : Fin t, Fin (rank j)) → Prop :=
    fun x ↦ x < toLex ⟨k, i⟩
  let g : Lex (Σ j : Fin t, Fin (rank j)) → Int :=
    fun x ↦ f (ofLex x).1 (ofLex x).2
  change (∑ x : {x // p x}, g x.1) = _
  rw [show (∑ x : {x // p x}, g x.1) =
      ∑ x ∈ Finset.univ with p x, g x by
    rw [← Finset.subtype_univ p]
    exact Finset.sum_subtype_eq_sum_filter g]
  rw [Finset.sum_filter]
  change (∑ x : (Σ j : Fin t, Fin (rank j)),
      if toLex x < toLex ⟨k, i⟩ then f x.1 x.2 else 0) = _
  rw [Fintype.sum_sigma]
  simp only [Sigma.Lex.lt_def]
  change (∑ j : Fin t, ∑ a : Fin (rank j),
      if j < k ∨ ∃ h : j = k, h ▸ a < i then f j a else 0) = _
  have hinner (j : Fin t) :
      (∑ a : Fin (rank j),
        if j < k ∨ ∃ h : j = k, h ▸ a < i then f j a else 0) =
        if j < k then (∑ a : Fin (rank j), f j a)
        else if h : j = k then
          (∑ a : Fin (rank k), if a < i then f k a else 0)
        else 0 := by
    by_cases hjk : j < k
    · simp [hjk]
    · by_cases hEq : j = k
      · subst j
        simp
      · simp [hjk, hEq]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.filter_gt_eq_Iio]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · simp

end JordanProfileIndexing

namespace Bong

open Dyadic
open Module

namespace JordanProfileOrder

/-- The empty local prefix has zero volume order. -/
@[simp]
theorem localPrefixSum_zero (scale effective : Int) :
    localPrefixSum scale effective 0 = 0 := by
  simp [localPrefixSum]

/-- The filtered sum over the local indices below `i` is the local prefix
sum at `i`. -/
theorem sum_fin_ite_lt_eq_localPrefixSum
    (scale effective : Int) {rank : Nat} (i : Fin rank) :
    (∑ a : Fin rank,
      if a < i then localOrder scale effective a.val else 0) =
      localPrefixSum scale effective i.val := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.filter_gt_eq_Iio]
  calc
    (∑ a ∈ Finset.Iio i, localOrder scale effective a.val) =
        ∑ j ∈ (Finset.Iio i).map Fin.valEmbedding,
          localOrder scale effective j :=
      (Finset.sum_map (Finset.Iio i) Fin.valEmbedding
        (localOrder scale effective)).symm
    _ = ∑ j ∈ Finset.Iio i.val, localOrder scale effective j := by
      rw [Fin.map_valEmbedding_Iio]
    _ = localPrefixSum scale effective i.val := by
      simp [localPrefixSum, Nat.Iio_eq_range]

end JordanProfileOrder

namespace Lattice.WeakJordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- A complete weak Jordan component contributes its rank times its scale.
For an improper component, O'Meara's even-rank invariant is precisely what
closes the alternating pair sum. -/
theorem localPrefixSum_componentRank_eq
    (W : WeakJordanDecomposition q L t) (hW : W.HasImproperEvenRank)
    (k : Fin t) :
    JordanProfileOrder.localPrefixSum
        (ordUnit K (W.scaleGenerator k))
        (W.effectiveNormOrderAt k (ordUnit K (W.scaleGenerator k)))
        (finrank K (W.component k).carrier) =
      (finrank K (W.component k).carrier : Int) *
        ordUnit K (W.scaleGenerator k) := by
  let scale := ordUnit K (W.scaleGenerator k)
  let effective := W.effectiveNormOrderAt k scale
  change JordanProfileOrder.localPrefixSum scale effective
      (finrank K (W.component k).carrier) =
    (finrank K (W.component k).carrier : Int) * scale
  by_cases hproper : scale = effective
  · rw [← hproper]
    simp [JordanProfileOrder.localPrefixSum,
      JordanProfileOrder.localOrder_of_proper]
  · have hstrict : scale < effective :=
      lt_of_le_of_ne (W.targetScale_le_effectiveNormOrderAt k scale) hproper
    have heven : Even (finrank K (W.component k).carrier) :=
      hW.componentRank_even_of_lt_effectiveNormOrderAt W k k hstrict
    exact JordanProfileOrder.localPrefixSum_of_even scale effective heven

end Lattice.WeakJordanDecomposition

namespace BONG.WeakJordanOrderProfileWitness

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

/-- Reindex the first `i` entries of a BONG along its weak Jordan profile
order isomorphism. -/
theorem prefixSum_eq_lexIioSum
    (b : BONG.GoodBONG q L n)
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b.toBONG W) (i : Fin n) :
    b.orderSequence.prefixSum i.val =
      ∑ x : {x : Lex (Σ k : Fin t,
          Fin (finrank K (W.component k).carrier)) //
          x < toLex (w.indexEquiv i)},
        weakJordanExpectedOrder W (ofLex x.1).1 (ofLex x.1).2 := by
  classical
  rw [BeliOrderSequence.prefixSum]
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin i.val ≃
      {x : Lex (Σ k : Fin t,
          Fin (finrank K (W.component k).carrier)) //
          x < toLex (w.indexEquiv i)} := {
    toFun j := ⟨w.indexOrderIso ⟨j.val, by omega⟩, by
      change toLex (w.indexEquiv ⟨j.val, by omega⟩) <
        toLex (w.indexEquiv i)
      exact (w.order_iff _ _).1 j.isLt⟩
    invFun x := ⟨(w.indexOrderIso.symm x.1).val, by
      have hx' : x.1 < w.indexOrderIso i := x.2
      have hx := (w.indexOrderIso.symm.lt_iff_lt).2 hx'
      simpa using hx⟩
    left_inv j := by
      apply Fin.ext
      change (w.indexOrderIso.symm
        (w.indexOrderIso ⟨j.val, by omega⟩)).val = j.val
      rw [w.indexOrderIso.symm_apply_apply]
    right_inv x := by
      apply Subtype.ext
      change w.indexOrderIso (w.indexOrderIso.symm x.1) = x.1
      exact w.indexOrderIso.apply_symm_apply x.1
  }
  apply Fintype.sum_equiv e
  intro j
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
  have horder := w.order_eq ⟨j.val, by omega⟩
  simpa [e, BONG.GoodBONG.order,
    BONG.WeakJordanOrderProfileWitness.indexOrderIso] using horder

/-- A global BONG prefix is the sum of the complete earlier weak Jordan
components plus the local prefix in the current component. -/
theorem prefixSum_eq_componentPrefix_add_localPrefix
    (b : BONG.GoodBONG q L n)
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b.toBONG W) (i : Fin n) :
    b.orderSequence.prefixSum i.val =
      (∑ k ∈ Finset.Iio (w.indexEquiv i).1,
        JordanProfileOrder.localPrefixSum
          (ordUnit K (W.scaleGenerator k))
          (W.effectiveNormOrderAt k (ordUnit K (W.scaleGenerator k)))
          (finrank K (W.component k).carrier)) +
        JordanProfileOrder.localPrefixSum
          (ordUnit K (W.scaleGenerator (w.indexEquiv i).1))
          (W.effectiveNormOrderAt (w.indexEquiv i).1
            (ordUnit K (W.scaleGenerator (w.indexEquiv i).1)))
          (w.indexEquiv i).2.val := by
  rw [w.prefixSum_eq_lexIioSum b i]
  rw [JordanProfileIndexing.lexSigmaIio_sum
    (fun k ↦ finrank K (W.component k).carrier)
    (weakJordanExpectedOrder W) (w.indexEquiv i).1 (w.indexEquiv i).2]
  simp_rw [weakJordanExpectedOrder]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [JordanProfileOrder.localPrefixSum,
      ← Fin.sum_univ_eq_sum_range]
  · exact JordanProfileOrder.sum_fin_ite_lt_eq_localPrefixSum _ _ _

end BONG.WeakJordanOrderProfileWitness

end Bong
