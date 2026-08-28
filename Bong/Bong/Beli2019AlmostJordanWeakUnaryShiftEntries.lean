/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanWeakUnaryShift

/-!
# Entries and certificate for the weak-profile unary shift

This is the endpoint-collision-compatible form of the explicit adjacent
rank-one calculation in Beli (2019), Section 5.4.
-/

open scoped BigOperators

namespace Bong

open Dyadic
open Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Sequence entries depend only on the numerical index, not its bound
proof. -/
theorem weakOrderSequence_entry_eq_of_index_eq {n : Nat}
    (x : BeliOrderSequence n Int) (i j : Nat)
    (hi : i < n) (hj : j < n) (hij : i = j) :
    x.entry i hi = x.entry j hj := by
  subst j
  rfl

/-- The first exceptional entry is the enlarged unary selected order. -/
theorem weakUnaryShift_largeSelected_entry
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M n) :
    a.orderSequence.entry
        (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier)
        (by
          let w := D.largeWeakProfileWitness a
          have hrank := D.weakUnaryShift_largeComponentRank_selected hfin
          let zero : Fin (finrank K
              (D.largeAlmostJordan.component D.largeSelectedPosition).carrier) :=
            ⟨0, by rw [hrank]; omega⟩
          have hz := w.inverse_index_val D.largeSelectedPosition zero
          have _hbound :=
            (w.indexEquiv.symm ⟨D.largeSelectedPosition, zero⟩).isLt
          dsimp only [zero, Fin.val_mk] at hz
          omega) =
      ordUnit K D.input.block.scaleGenerator - 2 := by
  let w := D.largeWeakProfileWitness a
  have hrank := D.weakUnaryShift_largeComponentRank_selected hfin
  let zero : Fin (finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier) :=
    ⟨0, by rw [hrank]; omega⟩
  let I : Fin n := ⟨
    ∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier,
    by
      have hz := w.inverse_index_val D.largeSelectedPosition zero
      have hbound :=
        (w.indexEquiv.symm ⟨D.largeSelectedPosition, zero⟩).isLt
      dsimp only [zero, Fin.val_mk] at hz
      omega⟩
  have hI : I = w.indexEquiv.symm ⟨D.largeSelectedPosition, zero⟩ := by
    apply Fin.ext
    exact (w.inverse_index_val D.largeSelectedPosition zero).symm
  have heffective := D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hfin
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  change a.order I = _
  rw [hI]
  calc
    a.order (w.indexEquiv.symm ⟨D.largeSelectedPosition, zero⟩) =
        BONG.weakJordanExpectedOrder D.largeAlmostJordan
          D.largeSelectedPosition zero :=
      w.order_inverse_indexEquiv D.largeSelectedPosition zero
    _ = JordanProfileOrder.localOrder
          (ordUnit K D.input.block.enlargedScaleGenerator)
          (D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator)) 0 := by
      simp only [BONG.weakJordanExpectedOrder,
        D.largeAlmostJordan_scaleGenerator_selected, zero]
    _ = ordUnit K D.input.block.scaleGenerator - 2 := by
      rw [heffective, JordanProfileOrder.localOrder_of_proper, hscale]

/-- The intermediate common component on the larger side begins one entry
after the interval start. -/
theorem weakUnaryShift_largeCommon_entry
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (j : Nat) (hj : j < finrank K (D.complementStrictWeak.component i₀).carrier) :
    a.orderSequence.entry
        ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) + (j + 1))
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega) =
      JordanProfileOrder.localOrder
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
        (D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) j := by
  let w := D.largeWeakProfileWitness a
  have hrank := D.weakUnaryShift_largeComponentRank_at_smallSelected
    hfin i₀ hi₀
  let ell : Fin
      (finrank K (D.largeAlmostJordan.component D.smallSelectedPosition).carrier) :=
    ⟨j, by rw [hrank]; exact hj⟩
  let I : Fin n := ⟨
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier) + (j + 1),
    by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega⟩
  have hprefix := D.weakUnaryShift_largePrefixRank_at_smallSelected
    hfin i₀ hi₀
  have hI : I = w.indexEquiv.symm ⟨D.smallSelectedPosition, ell⟩ := by
    apply Fin.ext
    have hinverse := w.inverse_index_val D.smallSelectedPosition ell
    dsimp only [ell, Fin.val_mk] at hinverse
    dsimp only [I, Fin.val_mk]
    rw [hinverse, hprefix]
    omega
  have hposition :=
    D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀
  change a.order I = _
  rw [hI]
  calc
    a.order (w.indexEquiv.symm ⟨D.smallSelectedPosition, ell⟩) =
        BONG.weakJordanExpectedOrder D.largeAlmostJordan
          D.smallSelectedPosition ell :=
      w.order_inverse_indexEquiv D.smallSelectedPosition ell
    _ = JordanProfileOrder.localOrder
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
          (D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i₀)
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) j := by
      simp only [BONG.weakJordanExpectedOrder, ell]
      rw [← hposition, D.largeAlmostJordan_scaleGenerator_common]

/-- On the smaller side, the intermediate common component begins at the
interval start. -/
theorem weakUnaryShift_smallCommon_entry
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (j : Nat) (hj : j < finrank K (D.complementStrictWeak.component i₀).carrier) :
    b.orderSequence.entry
        ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) + j)
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega) =
      JordanProfileOrder.localOrder
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
        (D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) j := by
  let w := D.smallWeakProfileWitness b
  have hrank := D.weakUnaryShift_smallComponentRank_at_largeSelected
    hfin i₀ hi₀
  let ell : Fin
      (finrank K (D.smallAlmostJordan.component D.largeSelectedPosition).carrier) :=
    ⟨j, by rw [hrank]; exact hj⟩
  let I : Fin n := ⟨
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier) + j,
    by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega⟩
  have hprefix := D.weakUnaryShift_prefixRank_eq hfin i₀ hi₀
  have hI : I = w.indexEquiv.symm ⟨D.largeSelectedPosition, ell⟩ := by
    apply Fin.ext
    have hinverse := w.inverse_index_val D.largeSelectedPosition ell
    dsimp only [ell, Fin.val_mk] at hinverse
    dsimp only [I, Fin.val_mk]
    rw [hinverse, ← hprefix]
  have hposition :=
    D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
      hfin i₀ hi₀
  have heffective := D.unaryShift_commonEffectiveNormOrder_eq hfin i₀ hi₀
  change b.order I = _
  rw [hI]
  calc
    b.order (w.indexEquiv.symm ⟨D.largeSelectedPosition, ell⟩) =
        BONG.weakJordanExpectedOrder D.smallAlmostJordan
          D.largeSelectedPosition ell :=
      w.order_inverse_indexEquiv D.largeSelectedPosition ell
    _ = JordanProfileOrder.localOrder
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
          (D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i₀)
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) j := by
      simp only [BONG.weakJordanExpectedOrder, ell]
      rw [← hposition, D.smallAlmostJordan_scaleGenerator_common, ← heffective]

/-- The last exceptional entry is the smaller unary selected order. -/
theorem weakUnaryShift_smallSelected_entry
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    b.orderSequence.entry
        ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) +
          finrank K (D.complementStrictWeak.component i₀).carrier)
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega) =
      ordUnit K D.input.block.scaleGenerator := by
  let w := D.smallWeakProfileWitness b
  have hrank := D.weakUnaryShift_smallComponentRank_selected hfin
  let zero : Fin
      (finrank K (D.smallAlmostJordan.component D.smallSelectedPosition).carrier) :=
    ⟨0, by rw [hrank]; omega⟩
  let I : Fin n := ⟨
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier) +
      finrank K (D.complementStrictWeak.component i₀).carrier,
    by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a; omega⟩
  have hprefix := D.weakUnaryShift_smallPrefixRank_at_smallSelected
    hfin i₀ hi₀
  have hI : I = w.indexEquiv.symm ⟨D.smallSelectedPosition, zero⟩ := by
    apply Fin.ext
    have hinverse := w.inverse_index_val D.smallSelectedPosition zero
    dsimp only [I, zero, Fin.val_mk]
    rw [hinverse, hprefix]
    omega
  have heffective := D.smallSelected_effectiveNormOrder_eq_scale_of_rank_one hfin
  change b.order I = _
  rw [hI]
  calc
    b.order (w.indexEquiv.symm ⟨D.smallSelectedPosition, zero⟩) =
        BONG.weakJordanExpectedOrder D.smallAlmostJordan
          D.smallSelectedPosition zero :=
      w.order_inverse_indexEquiv D.smallSelectedPosition zero
    _ = JordanProfileOrder.localOrder
          (ordUnit K D.input.block.scaleGenerator)
          (D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator)) 0 := by
      simp only [BONG.weakJordanExpectedOrder,
        D.smallAlmostJordan_scaleGenerator_selected, zero]
    _ = ordUnit K D.input.block.scaleGenerator := by
      rw [heffective, JordanProfileOrder.localOrder_of_proper]

/-- Coordinates outside the exceptional interval are certified by the
ordinary weak-profile common-component calculation. -/
theorem weakUnaryShift_outside_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (houtside :
      i < (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) ∨
        (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) +
            (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ i) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  rcases houtside with hleft | hright
  · have hcomponent := D.weakUnaryShift_component_before_of_index_lt_start
      a I hleft
    rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
      hselected | ⟨c, hcommon⟩
    · change (x.indexEquiv I).1 < D.largeSelectedPosition at hcomponent
      rw [hselected] at hcomponent
      exact (lt_irrefl _ hcomponent).elim
    · exact D.weakUnaryShift_common_before_coordinate
        hfin i₀ hi₀ a b i hi c hcommon (by
          rw [← hcommon]
          exact hcomponent)
  · have hcomponent :=
      D.weakUnaryShift_component_after_of_interval_end_le_index
        hfin i₀ hi₀ a I hright
    rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
      hselected | ⟨c, hcommon⟩
    · have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      change D.smallSelectedPosition.val < (x.indexEquiv I).1.val at hcomponent
      rw [hselected] at hcomponent
      omega
    · exact D.weakUnaryShift_common_after_coordinate
        hfin i₀ hi₀ a b i hi c hcommon (by
          rw [← hcommon]
          exact hcomponent)

/-- Effective-proper exceptional interval certificate on the uniform weak
profiles. -/
theorem weakUnaryShift_orderCertificate_of_effective_eq_scale
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let k := c - 1
  have hc : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  have hmiddleScale : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.scaleGenerator - 1 := by omega
  refine Beli2019IndexPOrderCertificate.embedIntervalWithOutside start ?_
    (Beli2019IndexPOrderCertificate.indexPUnaryProper
      (ordUnit K D.input.block.scaleGenerator) k) ?_ ?_ ?_
  · have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    dsimp only [start, k, c]
    dsimp only [c] at hc hbound
    omega
  · intro j hj
    simp only [BeliOrderSequence.loweredLeftEndpoint_entry]
    by_cases hj0 : j = 0
    · subst j
      simp only [if_pos]
      simpa only [start, Nat.add_zero] using
        D.weakUnaryShift_largeSelected_entry hfin a
    · rw [if_neg hj0]
      have hjc : j - 1 < c := by
        dsimp only [k] at hj
        omega
      have hentry := D.weakUnaryShift_largeCommon_entry
        hfin i₀ hi₀ a (j - 1) (by simpa only [c] using hjc)
      rw [heffective, JordanProfileOrder.localOrder_of_proper] at hentry
      change a.orderSequence.entry (start + j) _ = _
      have hindex : start + j =
          (∑ p ∈ Finset.Iio D.largeSelectedPosition,
            finrank K (D.largeAlmostJordan.component p).carrier) +
            (j - 1 + 1) := by
        dsimp only [start]
        omega
      calc
        a.orderSequence.entry (start + j) _ =
            a.orderSequence.entry
              ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
                finrank K (D.largeAlmostJordan.component p).carrier) +
                (j - 1 + 1)) _ :=
          weakOrderSequence_entry_eq_of_index_eq _ _ _ _ _ hindex
        _ = ordUnit K (D.complementStrictWeak.scaleGenerator i₀) := hentry
        _ = ordUnit K D.input.block.scaleGenerator - 1 := hmiddleScale
  · intro j hj
    simp only [BeliOrderSequence.raisedRightEndpoint_entry]
    by_cases hlast : j = k + 1
    · rw [if_pos hlast]
      have hjc : j = c := by
        dsimp only [k] at hlast
        omega
      have hentry := D.weakUnaryShift_smallSelected_entry
        hfin i₀ hi₀ a b
      have hindex : start + j =
          (∑ p ∈ Finset.Iio D.largeSelectedPosition,
            finrank K (D.largeAlmostJordan.component p).carrier) +
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        dsimp only [start, c] at hjc ⊢
        omega
      calc
        b.orderSequence.entry (start + j) _ =
            b.orderSequence.entry
              ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
                finrank K (D.largeAlmostJordan.component p).carrier) +
                finrank K (D.complementStrictWeak.component i₀).carrier) _ :=
          weakOrderSequence_entry_eq_of_index_eq _ _ _ _ _ hindex
        _ = ordUnit K D.input.block.scaleGenerator := hentry
    · rw [if_neg hlast]
      have hjc : j < c := by
        dsimp only [k] at hj hlast
        omega
      have hentry := D.weakUnaryShift_smallCommon_entry
        hfin i₀ hi₀ a b j (by simpa only [c] using hjc)
      rw [heffective, JordanProfileOrder.localOrder_of_proper] at hentry
      change b.orderSequence.entry (start + j) _ = _
      exact hentry.trans hmiddleScale
  · intro i hi houtside
    apply D.weakUnaryShift_outside_coordinate hfin i₀ hi₀ a b i hi
    rcases houtside with hleft | hright
    · exact Or.inl hleft
    · right
      dsimp only [start, k, c] at hright ⊢
      dsimp only [c] at hc
      omega

/-- Effective-improper exceptional interval certificate on the uniform weak
profiles. -/
theorem weakUnaryShift_orderCertificate_of_effective_eq_add_one
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence := by
  let start := ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hc : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hevenRank :=
    D.unaryShift_intermediateRank_even_of_effective_eq_add_one i₀ heffective
  change Even c at hevenRank
  rcases hevenRank with ⟨k, hk⟩
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  have hmiddleScale : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.scaleGenerator - 1 := by omega
  refine Beli2019IndexPOrderCertificate.embedIntervalWithOutside start ?_
    (Beli2019IndexPOrderCertificate.indexPUnaryExceptional
      (ordUnit K D.input.block.scaleGenerator) k) ?_ ?_ ?_
  · have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    dsimp only [start, c]
    dsimp only [c] at hc hk hbound
    omega
  · intro j hj
    simp only [BeliOrderSequence.alternatingLowFirst_entry]
    by_cases hj0 : j = 0
    · subst j
      simp only [Nat.zero_mod, if_pos]
      simpa only [start, Nat.add_zero] using
        D.weakUnaryShift_largeSelected_entry hfin a
    · have hjc : j - 1 < c := by
        dsimp only [c] at hk
        omega
      have hentry := D.weakUnaryShift_largeCommon_entry
        hfin i₀ hi₀ a (j - 1) (by simpa only [c] using hjc)
      have hsourceScale :
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
            D.largeAlmostJordan.effectiveNormOrderAt
              (D.largeCommonPosition i₀)
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by
        omega
      by_cases hmod : j % 2 = 0
      · rw [if_pos hmod]
        have hlocalOdd : ¬Even (j - 1) := by
          intro heven
          rcases heven with ⟨m, hm⟩
          omega
        rw [JordanProfileOrder.localOrder_odd_of_scale_le
          hsourceScale hlocalOdd] at hentry
        have hindex : start + j =
            (∑ p ∈ Finset.Iio D.largeSelectedPosition,
              finrank K (D.largeAlmostJordan.component p).carrier) +
              (j - 1 + 1) := by
          dsimp only [start]
          omega
        calc
          a.orderSequence.entry (start + j) _ =
              a.orderSequence.entry
                ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
                  finrank K (D.largeAlmostJordan.component p).carrier) +
                  (j - 1 + 1)) _ :=
            weakOrderSequence_entry_eq_of_index_eq _ _ _ _ _ hindex
          _ = 2 * ordUnit K (D.complementStrictWeak.scaleGenerator i₀) -
                D.largeAlmostJordan.effectiveNormOrderAt
                  (D.largeCommonPosition i₀)
                  (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := hentry
          _ = ordUnit K D.input.block.scaleGenerator - 2 := by omega
      · rw [if_neg hmod]
        have hnotEvenJ : ¬Even j := by
          intro heven
          rcases heven with ⟨m, hm⟩
          have : j % 2 = 0 := by omega
          exact hmod this
        have hlocalEven : Even (j - 1) := by
          rcases Nat.not_even_iff_odd.mp hnotEvenJ with ⟨m, hm⟩
          exact ⟨m, by omega⟩
        rw [JordanProfileOrder.localOrder_even_of_scale_le
          hsourceScale hlocalEven] at hentry
        have hindex : start + j =
            (∑ p ∈ Finset.Iio D.largeSelectedPosition,
              finrank K (D.largeAlmostJordan.component p).carrier) +
              (j - 1 + 1) := by
          dsimp only [start]
          omega
        calc
          a.orderSequence.entry (start + j) _ =
              a.orderSequence.entry
                ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
                  finrank K (D.largeAlmostJordan.component p).carrier) +
                  (j - 1 + 1)) _ :=
            weakOrderSequence_entry_eq_of_index_eq _ _ _ _ _ hindex
          _ = D.largeAlmostJordan.effectiveNormOrderAt
                (D.largeCommonPosition i₀)
                (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := hentry
          _ = ordUnit K D.input.block.scaleGenerator := by omega
  · intro j hj
    simp only [BeliOrderSequence.alternatingHighFirst_entry]
    by_cases hlast : j = c
    · have hmod : j % 2 = 0 := by
        dsimp only [c] at hk hlast
        omega
      rw [if_pos hmod]
      have hentry := D.weakUnaryShift_smallSelected_entry
        hfin i₀ hi₀ a b
      have hindex : start + j =
          (∑ p ∈ Finset.Iio D.largeSelectedPosition,
            finrank K (D.largeAlmostJordan.component p).carrier) +
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        dsimp only [start, c] at hlast ⊢
        omega
      calc
        b.orderSequence.entry (start + j) _ =
            b.orderSequence.entry
              ((∑ p ∈ Finset.Iio D.largeSelectedPosition,
                finrank K (D.largeAlmostJordan.component p).carrier) +
                finrank K (D.complementStrictWeak.component i₀).carrier) _ :=
          weakOrderSequence_entry_eq_of_index_eq _ _ _ _ _ hindex
        _ = ordUnit K D.input.block.scaleGenerator := hentry
    · have hjc : j < c := by
        dsimp only [c] at hk
        omega
      have hentry := D.weakUnaryShift_smallCommon_entry
        hfin i₀ hi₀ a b j (by simpa only [c] using hjc)
      have htargetScale :
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
            D.largeAlmostJordan.effectiveNormOrderAt
              (D.largeCommonPosition i₀)
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by
        omega
      by_cases hmod : j % 2 = 0
      · rw [if_pos hmod]
        have hevenJ : Even j := Nat.even_iff.mpr hmod
        rw [JordanProfileOrder.localOrder_even_of_scale_le
          htargetScale hevenJ] at hentry
        exact hentry.trans (by omega)
      · rw [if_neg hmod]
        have hnotEvenJ : ¬Even j := by
          intro heven
          rcases heven with ⟨m, hm⟩
          have : j % 2 = 0 := by omega
          exact hmod this
        rw [JordanProfileOrder.localOrder_odd_of_scale_le
          htargetScale hnotEvenJ] at hentry
        exact hentry.trans (by omega)
  · intro i hi houtside
    apply D.weakUnaryShift_outside_coordinate hfin i₀ hi₀ a b i hi
    rcases houtside with hleft | hright
    · exact Or.inl hleft
    · right
      dsimp only [start, c] at hright ⊢
      dsimp only [c] at hk
      omega

/-- Complete adjacent unary certificate, including endpoint collisions. -/
theorem weakUnaryShift_orderCertificate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence := by
  rcases D.unaryShift_commonEffectiveNormOrder_cases hfin i₀ hi₀ with
    hproper | himproper
  · exact D.weakUnaryShift_orderCertificate_of_effective_eq_scale
      hfin i₀ hi₀ hproper a b
  · exact D.weakUnaryShift_orderCertificate_of_effective_eq_add_one
      hfin i₀ hi₀ himproper a b

/-- Every rank-one case is certified: either the selected positions align or
the unique intermediate-scale component gives the adjacent unary shift. -/
theorem weakRankOne_orderCertificate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence := by
  rcases D.selectedPositions_unary_alternative hfin with
    hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
  · exact D.weakAligned_orderCertificate hselected a b
  · exact D.weakUnaryShift_orderCertificate hfin i₀ hi₀ a b

/-- Complete Section 5.4 order certificate in ranks one and two, with both
endpoint amalgamation cases included. -/
theorem weakAllRanks_orderCertificate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence := by
  rcases D.rank_one_or_two with hOne | hTwo
  · exact D.weakRankOne_orderCertificate hOne a b
  · exact D.weakAligned_orderCertificate
      (D.selectedPositions_eq_of_rank_two hTwo) a b

end Lattice.Beli2019Lemma51Data

end Bong
