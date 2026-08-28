/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanUnaryShift
import Bong.Bong.Beli2019AlmostJordanWeakAligned

/-!
# The rank-one adjacent shift on uniform weak Jordan profiles

The selected unary component moves across the unique common component whose
scale lies strictly between the two selected scales.  Endpoint equal-scale
amalgamations do not change this component-rank bookkeeping.
-/

namespace Bong

open Dyadic
open Module
open scoped BigOperators

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The selected larger-side weak component has rank one. -/
theorem weakUnaryShift_largeComponentRank_selected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier = 1 := by
  simpa only [D.largeAlmostJordan_finrank_selected] using hfin

/-- The selected smaller-side weak component has rank one. -/
theorem weakUnaryShift_smallComponentRank_selected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    finrank K
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 1 := by
  simpa only [D.smallAlmostJordan_finrank_selected] using hfin

/-- At the left transposition slot, the small weak profile contains the
intermediate common component. -/
theorem weakUnaryShift_smallComponentRank_at_largeSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    finrank K (D.smallAlmostJordan.component D.largeSelectedPosition).carrier =
      finrank K (D.complementStrictWeak.component i₀).carrier := by
  have hposition :=
    D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
      hfin i₀ hi₀
  rw [← hposition, D.smallAlmostJordan_finrank_common]

/-- At the right transposition slot, the large weak profile contains the
intermediate common component. -/
theorem weakUnaryShift_largeComponentRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    finrank K (D.largeAlmostJordan.component D.smallSelectedPosition).carrier =
      finrank K (D.complementStrictWeak.component i₀).carrier := by
  have hposition :=
    D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀
  rw [← hposition, D.largeAlmostJordan_finrank_common]

/-- Component ranks agree pointwise before the adjacent transposition. -/
theorem weakUnaryShift_componentRank_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    finrank K (D.largeAlmostJordan.component p).carrier =
      finrank K (D.smallAlmostJordan.component p).carrier := by
  rcases D.largePosition_eq_selected_or_common p with
    hselected | ⟨j, hcommon⟩
  · subst p
    exact (lt_irrefl _ hp).elim
  · subst p
    have hne : j ≠ i₀ := by
      intro h
      subst j
      have hright :=
        D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      have hrightVal := congrArg Fin.val hright
      change (D.largeCommonPosition i₀).val <
        D.largeSelectedPosition.val at hp
      omega
    have hposition := D.commonPositions_eq_of_intermediate_of_ne
      hfin i₀ j hi₀ hne
    rw [D.largeAlmostJordan_finrank_common, ← hposition,
      D.smallAlmostJordan_finrank_common]

/-- Component ranks agree pointwise after the adjacent transposition. -/
theorem weakUnaryShift_componentRank_eq_after
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : D.smallSelectedPosition < p) :
    finrank K (D.largeAlmostJordan.component p).carrier =
      finrank K (D.smallAlmostJordan.component p).carrier := by
  rcases D.largePosition_eq_selected_or_common p with
    hselected | ⟨j, hcommon⟩
  · subst p
    have hadjacent :=
      D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀
    change D.smallSelectedPosition.val < D.largeSelectedPosition.val at hp
    omega
  · subst p
    have hne : j ≠ i₀ := by
      intro h
      subst j
      have hright :=
        D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
          hfin i₀ hi₀
      exact (lt_irrefl _ (hright ▸ hp)).elim
    have hposition := D.commonPositions_eq_of_intermediate_of_ne
      hfin i₀ j hi₀ hne
    rw [D.largeAlmostJordan_finrank_common, ← hposition,
      D.smallAlmostJordan_finrank_common]

/-- The two weak profiles start the exceptional interval at the same
prefix-rank offset. -/
theorem weakUnaryShift_prefixRank_eq
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) =
      ∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.smallAlmostJordan.component p).carrier := by
  apply Finset.sum_congr rfl
  intro p hp
  exact D.weakUnaryShift_componentRank_eq_before
    hfin i₀ hi₀ p (Finset.mem_Iio.mp hp)

/-- Prefix-rank equality at every position before the transposition. -/
theorem weakUnaryShift_prefixRank_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (k : Fin (D.complementComponentCount + 1))
    (hk : k < D.largeSelectedPosition) :
    (∑ p ∈ Finset.Iio k,
        finrank K (D.largeAlmostJordan.component p).carrier) =
      ∑ p ∈ Finset.Iio k,
        finrank K (D.smallAlmostJordan.component p).carrier := by
  apply Finset.sum_congr rfl
  intro p hp
  exact D.weakUnaryShift_componentRank_eq_before hfin i₀ hi₀ p
    ((Finset.mem_Iio.mp hp).trans hk)

/-- The large-side prefix at the right slot is the common start plus the
rank-one selected component. -/
theorem weakUnaryShift_largePrefixRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.smallSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) =
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) + 1 := by
  rw [sum_Iio_eq_add_of_val_eq_add_one
    (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier)
    D.largeSelectedPosition D.smallSelectedPosition
    (D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀)]
  rw [D.weakUnaryShift_largeComponentRank_selected hfin]

/-- The small-side prefix at the right slot is the common start plus the
rank of the intermediate component. -/
theorem weakUnaryShift_smallPrefixRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.smallSelectedPosition,
        finrank K (D.smallAlmostJordan.component p).carrier) =
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) +
        finrank K (D.complementStrictWeak.component i₀).carrier := by
  rw [sum_Iio_eq_add_of_val_eq_add_one
    (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
    D.largeSelectedPosition D.smallSelectedPosition
    (D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀)]
  rw [D.weakUnaryShift_smallComponentRank_at_largeSelected hfin i₀ hi₀]
  rw [← D.weakUnaryShift_prefixRank_eq hfin i₀ hi₀]

/-- Prefix ranks agree after the adjacent transposition. -/
theorem weakUnaryShift_prefixRank_eq_after
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (k : Fin (D.complementComponentCount + 1))
    (hk : D.smallSelectedPosition < k) :
    (∑ p ∈ Finset.Iio k,
        finrank K (D.largeAlmostJordan.component p).carrier) =
      ∑ p ∈ Finset.Iio k,
        finrank K (D.smallAlmostJordan.component p).carrier := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  apply sum_Iio_eq_of_total_eq_of_eq_on_Ici
  · calc
      (∑ p, finrank K (D.largeAlmostJordan.component p).carrier) = n :=
        x.sum_componentRank_eq_length
      _ = ∑ p, finrank K (D.smallAlmostJordan.component p).carrier :=
        y.sum_componentRank_eq_length.symm
  · intro p hp
    exact D.weakUnaryShift_componentRank_eq_after
      hfin i₀ hi₀ p (hk.trans_le hp)

/-- Before the exceptional interval, the uniform weak profile maps choose
the same component and local coordinate. -/
theorem weakUnaryShift_profile_coordinates_eq_before
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    ((D.largeWeakProfileWitness a).indexEquiv I).1 =
        ((D.smallWeakProfileWitness b).indexEquiv I).1 ∧
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val =
        ((D.smallWeakProfileWitness b).indexEquiv I).2.val := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  apply x.indexEquiv_coordinates_eq_of_prefix_and_rank_eq y I
  · exact D.weakUnaryShift_prefixRank_eq_before
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  · exact D.weakUnaryShift_componentRank_eq_before
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore

/-- After the exceptional interval, the uniform weak profile maps again
choose the same component and local coordinate. -/
theorem weakUnaryShift_profile_coordinates_eq_after
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hafter : D.smallSelectedPosition <
      ((D.largeWeakProfileWitness a).indexEquiv I).1) :
    ((D.largeWeakProfileWitness a).indexEquiv I).1 =
        ((D.smallWeakProfileWitness b).indexEquiv I).1 ∧
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val =
        ((D.smallWeakProfileWitness b).indexEquiv I).2.val := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  apply x.indexEquiv_coordinates_eq_of_prefix_and_rank_eq y I
  · exact D.weakUnaryShift_prefixRank_eq_after
      hfin i₀ hi₀ a b (x.indexEquiv I).1 hafter
  · exact D.weakUnaryShift_componentRank_eq_after
      hfin i₀ hi₀ (x.indexEquiv I).1 hafter

/-- Coordinates in common components before the exceptional interval have
the usual weak-profile Section 5.4 certificate. -/
theorem weakUnaryShift_common_before_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  have hne : c ≠ i₀ := by
    intro h
    subst c
    have hright :=
      D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
        hfin i₀ hi₀
    have hadjacent :=
      D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀
    have hrightVal := congrArg Fin.val hright
    change (D.largeCommonPosition i₀).val <
      D.largeSelectedPosition.val at hbefore
    omega
  have hcommonPositions :=
    D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
  have hsmallBefore :
      D.smallCommonPosition c < D.smallSelectedPosition := by
    have hadjacent :=
      D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
        hfin i₀ hi₀
    rw [hcommonPositions]
    change (D.largeCommonPosition c).val < D.smallSelectedPosition.val
    omega
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_before
    hfin i₀ hi₀ a b I (by rw [hposition]; exact hbefore)
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hnext : (x.indexEquiv I).2.val + 1 <
      finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
  · exact D.weakAligned_common_before_coordinate_of_local_succ_of_alignment
      a b i hi c hposition hcoordinates hcommonPositions hsmallBefore hnext
  · have hlast : (x.indexEquiv I).2.val + 1 =
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      have hbound := (x.indexEquiv I).2.isLt
      omega
    by_cases heven : Even (x.indexEquiv I).2.val
    · exact D.weakAligned_common_before_even_coordinate_of_alignment
        a b i hi c hposition hcoordinates hcommonPositions hsmallBefore heven
    · exact D.weakAligned_common_before_last_odd_coordinate_of_alignment
        a b i hi c hposition hbefore hcoordinates hcommonPositions
          hsmallBefore hlast heven

/-- Coordinates in common components after the exceptional interval have
the usual weak-profile Section 5.4 certificate. -/
theorem weakUnaryShift_common_after_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.smallSelectedPosition < D.largeCommonPosition c) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeWeakProfileWitness a
  have hne : c ≠ i₀ := by
    intro h
    subst c
    have hright :=
      D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
        hfin i₀ hi₀
    exact (lt_irrefl _ (hright ▸ hafter)).elim
  have hcommonPositions :=
    D.commonPositions_eq_of_intermediate_of_ne hfin i₀ c hi₀ hne
  have hsmallAfter :
      D.smallSelectedPosition < D.smallCommonPosition c := by
    rw [hcommonPositions]
    exact hafter
  have hadjacent :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hlargeAfter :
      D.largeSelectedPosition < D.largeCommonPosition c := by
    change D.largeSelectedPosition.val < (D.largeCommonPosition c).val
    change D.smallSelectedPosition.val <
      (D.largeCommonPosition c).val at hafter
    omega
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_after
    hfin i₀ hi₀ a b I (by rw [hposition]; exact hafter)
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hfirst : (x.indexEquiv I).2.val = 0
  · exact D.weakAligned_common_after_first_coordinate_of_alignment
      a b i hi c hposition hlargeAfter hcoordinates
        hcommonPositions hsmallAfter hfirst
  · by_cases hnext : (x.indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
    · exact D.weakAligned_common_after_coordinate_of_local_neighbors_of_alignment
        a b i hi c hposition hlargeAfter hcoordinates
          hcommonPositions (Nat.pos_of_ne_zero hfirst) hnext
    · have hlast : (x.indexEquiv I).2.val + 1 =
          finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
        have hbound := (x.indexEquiv I).2.isLt
        omega
      exact D.weakAligned_common_after_last_coordinate_of_alignment
        a b i hi c hposition hlargeAfter hcoordinates hcommonPositions hlast

/-- The adjacent exceptional interval fits in the global weak profile. -/
theorem weakUnaryShift_interval_bound
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) :
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n := by
  let w := D.largeWeakProfileWitness a
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hc : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hrank : finrank K
      (D.largeAlmostJordan.component D.smallSelectedPosition).carrier = c :=
    D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀
  let last : Fin
      (finrank K (D.largeAlmostJordan.component D.smallSelectedPosition).carrier) :=
    ⟨c - 1, by rw [hrank]; omega⟩
  have hlast :
      (∑ p ∈ Finset.Iio D.smallSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) +
          (c - 1) < n := by
    calc
      _ = (w.indexEquiv.symm ⟨D.smallSelectedPosition, last⟩).val := by
        symm
        simpa only [last, Fin.val_mk] using
          w.inverse_index_val D.smallSelectedPosition last
      _ < n := (w.indexEquiv.symm ⟨D.smallSelectedPosition, last⟩).isLt
  rw [D.weakUnaryShift_largePrefixRank_at_smallSelected hfin i₀ hi₀] at hlast
  dsimp only [c] at hc hlast ⊢
  omega

/-- A global coordinate below the exceptional interval belongs to a weak
component strictly before the larger selected component. -/
theorem weakUnaryShift_component_before_of_index_lt_start
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hindex : I.val <
      ∑ p ∈ Finset.Iio D.largeSelectedPosition,
        finrank K (D.largeAlmostJordan.component p).carrier) :
    ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition := by
  let x := D.largeWeakProfileWitness a
  by_contra hnot
  have hselectedLe : D.largeSelectedPosition ≤ (x.indexEquiv I).1 :=
    le_of_not_gt hnot
  have hsubset : Finset.Iio D.largeSelectedPosition ⊆
      Finset.Iio (x.indexEquiv I).1 := by
    intro p hp
    exact Finset.mem_Iio.mpr
      ((Finset.mem_Iio.mp hp).trans_le hselectedLe)
  have hprefixLe :
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) ≤
        ∑ p ∈ Finset.Iio (x.indexEquiv I).1,
          finrank K (D.largeAlmostJordan.component p).carrier :=
    Finset.sum_le_sum_of_subset hsubset
  have hglobal := x.index_val_eq_componentStart_add_local I
  omega

/-- A global coordinate beyond the exceptional interval belongs to a weak
component strictly after the intermediate common component. -/
theorem weakUnaryShift_component_after_of_interval_end_le_index
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hindex :
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) +
          (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
        I.val) :
    D.smallSelectedPosition <
      ((D.largeWeakProfileWitness a).indexEquiv I).1 := by
  let x := D.largeWeakProfileWitness a
  let k := (x.indexEquiv I).1
  by_contra hnot
  have hk : k ≤ D.smallSelectedPosition := le_of_not_gt hnot
  have hsubset : Finset.Iic k ⊆ Finset.Iic D.smallSelectedPosition := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans hk)
  have hendLe :
      (∑ p ∈ Finset.Iio k,
          finrank K (D.largeAlmostJordan.component p).carrier) +
          finrank K (D.largeAlmostJordan.component k).carrier ≤
        (∑ p ∈ Finset.Iio D.smallSelectedPosition,
          finrank K (D.largeAlmostJordan.component p).carrier) +
          finrank K
            (D.largeAlmostJordan.component D.smallSelectedPosition).carrier := by
    rw [← sum_Iic_eq_sum_Iio_add, ← sum_Iic_eq_sum_Iio_add]
    exact Finset.sum_le_sum_of_subset hsubset
  have hglobal := x.index_val_lt_componentEnd I
  have hprefix := D.weakUnaryShift_largePrefixRank_at_smallSelected hfin i₀ hi₀
  have hrank := D.weakUnaryShift_largeComponentRank_at_smallSelected hfin i₀ hi₀
  change I.val <
      (∑ p ∈ Finset.Iio k,
        finrank K (D.largeAlmostJordan.component p).carrier) +
      finrank K (D.largeAlmostJordan.component k).carrier at hglobal
  omega

end Lattice.Beli2019Lemma51Data

end Bong
