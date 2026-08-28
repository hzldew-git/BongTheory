/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanProfile
import Bong.Bong.Beli2019IndexPOrderSpecialCertificates

/-!
# The adjacent unary shift in Beli (2019), Section 5.4

When the distinguished block has rank one and the common complement has a
component at the unique intermediate scale, the two collision-free almost
Jordan decompositions differ by one adjacent transposition.  This file records
the component-rank and prefix-rank bookkeeping needed to embed the explicit
proper or improper local order certificate into the global BONG profile.
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

/-- Summing over the strict lower interval of the next finite index adds
exactly the value at the current index. -/
theorem sum_Iio_eq_add_of_val_eq_add_one {t : Nat}
    (f : Fin t → Nat) (p next : Fin t)
    (hnext : next.val = p.val + 1) :
    (∑ i ∈ Finset.Iio next, f i) =
      (∑ i ∈ Finset.Iio p, f i) + f p := by
  classical
  have hset : Finset.Iio next = insert p (Finset.Iio p) := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change i.val < next.val ↔ i = p ∨ i.val < p.val
    constructor
    · intro hi
      by_cases hip : i = p
      · exact Or.inl hip
      · exact Or.inr (by omega)
    · rintro (rfl | hi)
      · omega
      · omega
  rw [hset, Finset.sum_insert (by simp)]
  omega

/-- The sum on a closed lower interval is the strict-prefix sum plus the
last term. -/
theorem sum_Iic_eq_sum_Iio_add {t : Nat}
    (f : Fin t → Nat) (k : Fin t) :
    (∑ i ∈ Finset.Iic k, f i) =
      (∑ i ∈ Finset.Iio k, f i) + f k := by
  classical
  have hset : Finset.Iic k = insert k (Finset.Iio k) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    constructor
    · intro hi
      rcases hi.eq_or_lt with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (rfl | hi)
      · exact le_rfl
      · exact hi.le
  rw [hset, Finset.sum_insert (by simp)]
  omega

/-- Equal total sums and pointwise equality on a final interval force equal
strict-prefix sums. -/
theorem sum_Iio_eq_of_total_eq_of_eq_on_Ici {t : Nat}
    (f g : Fin t → Nat) (k : Fin t)
    (htotal : (∑ i, f i) = ∑ i, g i)
    (hsuffix : ∀ i, k ≤ i → f i = g i) :
    (∑ i ∈ Finset.Iio k, f i) = ∑ i ∈ Finset.Iio k, g i := by
  classical
  have hIio :
      (Finset.univ.filter fun i : Fin t => i < k) = Finset.Iio k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
  have hIci :
      (Finset.univ.filter fun i : Fin t => ¬i < k) = Finset.Ici k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ici]
    exact not_lt
  have hsuffixSum :
      (∑ i ∈ Finset.Ici k, f i) = ∑ i ∈ Finset.Ici k, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsuffix i (Finset.mem_Ici.mp hi)
  have hsplitF :
      (∑ i ∈ Finset.Iio k, f i) + (∑ i ∈ Finset.Ici k, f i) =
        ∑ i, f i := by
    rw [← hIio, ← hIci]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin t => i < k) f
  have hsplitG :
      (∑ i ∈ Finset.Iio k, g i) + (∑ i ∈ Finset.Ici k, g i) =
        ∑ i, g i := by
    rw [← hIio, ← hIci]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin t => i < k) g
  omega

/-- In the intermediate-scale unary case, the effective norm order of the
common component is the same in the two almost Jordan decompositions. -/
theorem unaryShift_commonEffectiveNormOrder_eq
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      D.smallAlmostJordan.effectiveNormOrderAt (D.smallCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  apply le_antisymm
  · exact D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition i₀) (D.smallCommonPosition i₀)
      (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) (by omega)
  · exact D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      (D.smallCommonPosition i₀) (D.largeCommonPosition i₀)
      (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) (by omega)

/-- The common effective norm order lies between the intermediate scale
and the next integer. -/
theorem unaryShift_commonEffectiveNormOrder_bounds
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
        D.largeAlmostJordan.effectiveNormOrderAt
          (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) ∧
      D.largeAlmostJordan.effectiveNormOrderAt
          (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) ≤
        ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1 := by
  have hlargeNorm :=
    D.largeSelected_normOrder_eq_scaleOrder_of_rank_one (by
      simpa only [D.largeAlmostJordan_finrank_selected] using hfin)
  constructor
  · exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition i₀)
      (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
  · calc
      D.largeAlmostJordan.effectiveNormOrderAt
            (D.largeCommonPosition i₀)
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) ≤
          JordanProfileOrder.adjustedAt
            D.largeAlmostJordan.scaleOrderFamily
            D.largeAlmostJordan.normOrderFamily
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))
            D.largeSelectedPosition :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1 := by
        simp only [JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily,
          D.largeAlmostJordan_scaleGenerator_selected, hlargeNorm]
        rw [if_pos]
        · omega
        · omega

/-- There are exactly the two cases listed in the final paragraph of
Section 5.4: the intermediate component is effective-proper, or its
effective norm order is one above its scale. -/
theorem unaryShift_commonEffectiveNormOrder_cases
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    D.largeAlmostJordan.effectiveNormOrderAt
          (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
        ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ∨
      D.largeAlmostJordan.effectiveNormOrderAt
          (D.largeCommonPosition i₀)
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
        ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1 := by
  have hbounds := D.unaryShift_commonEffectiveNormOrder_bounds hfin i₀ hi₀
  omega

/-- In the second effective-norm case, O'Meara's improper modular parity
theorem forces the intermediate common component to have even rank. -/
theorem unaryShift_intermediateRank_even_of_effective_eq_add_one
    (D : Beli2019Lemma51Data q M N)
    (i₀ : Fin D.complementComponentCount)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1) :
    Even (finrank K (D.complementStrictWeak.component i₀).carrier) := by
  have hstrict : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) <
      D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by
    omega
  simpa only [D.largeAlmostJordan_finrank_common] using
    D.largeCommon_componentRank_even_of_scale_lt_effective i₀ hstrict

/-- The selected component has rank one on the larger side. -/
theorem unaryShift_largeComponentRank_selected
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
        D.largeSelectedPosition = 1 := by
  change finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier = 1
  simpa only [D.largeAlmostJordan_finrank_selected] using hfin

/-- The selected component has rank one on the smaller side. -/
theorem unaryShift_smallComponentRank_selected
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank
        D.smallSelectedPosition = 1 := by
  change finrank K
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier = 1
  simpa only [D.smallAlmostJordan_finrank_selected] using hfin

/-- At the left slot of the adjacent transposition, the smaller
decomposition contains the intermediate common component. -/
theorem unaryShift_smallComponentRank_at_largeSelected
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank
        D.largeSelectedPosition =
      finrank K (D.complementStrictWeak.component i₀).carrier := by
  have hposition :=
    D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
      hfin i₀ hi₀
  change finrank K
      (D.smallAlmostJordan.component D.largeSelectedPosition).carrier = _
  rw [← hposition, D.smallAlmostJordan_finrank_common]

/-- At the right slot of the adjacent transposition, the larger
decomposition contains the intermediate common component. -/
theorem unaryShift_largeComponentRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
        D.smallSelectedPosition =
      finrank K (D.complementStrictWeak.component i₀).carrier := by
  have hposition :=
    D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀
  change finrank K
      (D.largeAlmostJordan.component D.smallSelectedPosition).carrier = _
  rw [← hposition, D.largeAlmostJordan_finrank_common]

/-- Components strictly before the adjacent transposition have identical
ranks at the same numerical component position. -/
theorem unaryShift_componentRank_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p < D.largeSelectedPosition) :
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p =
      (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p := by
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
    change finrank K
        (D.largeAlmostJordan.component (D.largeCommonPosition j)).carrier =
      finrank K
        (D.smallAlmostJordan.component (D.largeCommonPosition j)).carrier
    rw [D.largeAlmostJordan_finrank_common, ← hposition,
      D.smallAlmostJordan_finrank_common]

/-- Components strictly after the adjacent transposition have identical
ranks at the same numerical component position. -/
theorem unaryShift_componentRank_eq_after
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hp : D.smallSelectedPosition < p) :
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p =
      (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p := by
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
    change finrank K
        (D.largeAlmostJordan.component (D.largeCommonPosition j)).carrier =
      finrank K
        (D.smallAlmostJordan.component (D.largeCommonPosition j)).carrier
    rw [D.largeAlmostJordan_finrank_common, ← hposition,
      D.smallAlmostJordan_finrank_common]

/-- The two global profiles begin the adjacent exceptional interval at the
same prefix-rank offset. -/
theorem unaryShift_prefixRank_eq
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) =
      ∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p := by
  apply Finset.sum_congr rfl
  intro p hp
  exact D.unaryShift_componentRank_eq_before
    hsmall hlarge hfin i₀ hi₀ p (Finset.mem_Iio.mp hp)

/-- Prefix-rank equality at every component strictly before the adjacent
transposition. -/
theorem unaryShift_prefixRank_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (k : Fin (D.complementComponentCount + 1))
    (hk : k < D.largeSelectedPosition) :
    (∑ p ∈ Finset.Iio k,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) =
      ∑ p ∈ Finset.Iio k,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p := by
  apply Finset.sum_congr rfl
  intro p hp
  exact D.unaryShift_componentRank_eq_before hsmall hlarge hfin i₀ hi₀ p
    ((Finset.mem_Iio.mp hp).trans hk)

/-- On the larger side, the prefix of the right slot is the common start
plus the rank-one selected block. -/
theorem unaryShift_largePrefixRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.smallSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) =
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) + 1 := by
  rw [sum_Iio_eq_add_of_val_eq_add_one
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
    D.largeSelectedPosition D.smallSelectedPosition
    (D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀)]
  rw [D.unaryShift_largeComponentRank_selected hlarge hfin]

/-- On the smaller side, the prefix of the right slot is the common start
plus the full rank of the intermediate component. -/
theorem unaryShift_smallPrefixRank_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (∑ p ∈ Finset.Iio D.smallSelectedPosition,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p) =
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
        finrank K (D.complementStrictWeak.component i₀).carrier := by
  rw [sum_Iio_eq_add_of_val_eq_add_one
    (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank
    D.largeSelectedPosition D.smallSelectedPosition
    (D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀)]
  rw [D.unaryShift_smallComponentRank_at_largeSelected hsmall hfin i₀ hi₀]
  rw [← D.unaryShift_prefixRank_eq hsmall hlarge hfin i₀ hi₀]

/-- Every component prefix strictly after the adjacent transposition has
the same total rank in the two decompositions. -/
theorem unaryShift_prefixRank_eq_after
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (k : Fin (D.complementComponentCount + 1))
    (hk : D.smallSelectedPosition < k) :
    (∑ p ∈ Finset.Iio k,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) =
      ∑ p ∈ Finset.Iio k,
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  apply sum_Iio_eq_of_total_eq_of_eq_on_Ici
  · calc
      (∑ p,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) =
          n := x.sum_componentRank_eq_length
      _ = ∑ p,
          (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank p :=
        y.sum_componentRank_eq_length.symm
  · intro p hp
    exact D.unaryShift_componentRank_eq_after
      hsmall hlarge hfin i₀ hi₀ p (hk.trans_le hp)

/-- Before the exceptional interval, the two canonical Jordan profile maps
choose the same component and local coordinate. -/
theorem unaryShift_profile_coordinates_eq_before
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 <
        D.largeSelectedPosition) :
    ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).1 ∧
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).2.val =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).2.val := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  apply x.indexEquiv_coordinates_eq_of_prefix_and_rank_eq y I
  · exact D.unaryShift_prefixRank_eq_before
      hsmall hlarge hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  · exact D.unaryShift_componentRank_eq_before
      hsmall hlarge hfin i₀ hi₀ (x.indexEquiv I).1 hbefore

/-- After the exceptional interval, the two canonical Jordan profile maps
again choose the same component and local coordinate. -/
theorem unaryShift_profile_coordinates_eq_after
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hafter : D.smallSelectedPosition <
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1) :
    ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).1 ∧
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).2.val =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).2.val := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  apply x.indexEquiv_coordinates_eq_of_prefix_and_rank_eq y I
  · exact D.unaryShift_prefixRank_eq_after
      hsmall hlarge hfin i₀ hi₀ a b (x.indexEquiv I).1 hafter
  · exact D.unaryShift_componentRank_eq_after
      hsmall hlarge hfin i₀ hi₀ (x.indexEquiv I).1 hafter

/-- Every coordinate in a common component strictly before the adjacent
exceptional interval has the usual Section 5.4 certificate. -/
theorem unaryShift_common_before_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
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
  have hcoordinates := D.unaryShift_profile_coordinates_eq_before
    hsmall hlarge hfin i₀ hi₀ a b I (by
      rw [hposition]
      exact hbefore)
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hnext : (x.indexEquiv I).2.val + 1 <
      (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
        (x.indexEquiv I).1
  · exact D.noCollision_common_before_coordinate_of_local_succ_of_alignment
      hsmall hlarge a b i hi c hposition hbefore hcoordinates
        hcommonPositions hsmallBefore hnext
  · have hlast : (x.indexEquiv I).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1 := by
      have hbound := (x.indexEquiv I).2.isLt
      omega
    by_cases heven : Even (x.indexEquiv I).2.val
    · exact D.noCollision_common_before_even_coordinate_of_alignment
        hsmall hlarge a b i hi c hposition hbefore hcoordinates
          hcommonPositions hsmallBefore heven
    · exact D.noCollision_common_before_last_odd_coordinate_of_alignment
        hsmall hlarge a b i hi c hposition hbefore hcoordinates
          hcommonPositions hsmallBefore hlast heven

/-- Every coordinate in a common component strictly after the adjacent
exceptional interval has the usual Section 5.4 certificate. -/
theorem unaryShift_common_after_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.smallSelectedPosition < D.largeCommonPosition c) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
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
  have hcoordinates := D.unaryShift_profile_coordinates_eq_after
    hsmall hlarge hfin i₀ hi₀ a b I (by
      rw [hposition]
      exact hafter)
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hfirst : (x.indexEquiv I).2.val = 0
  · exact D.noCollision_common_after_first_coordinate_of_alignment
      hsmall hlarge a b i hi c hposition hlargeAfter hcoordinates
        hcommonPositions hsmallAfter hfirst
  · by_cases hnext : (x.indexEquiv I).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1
    · exact D.noCollision_common_after_coordinate_of_local_neighbors_of_alignment
        hsmall hlarge a b i hi c hposition hlargeAfter hcoordinates
          hcommonPositions hsmallAfter (Nat.pos_of_ne_zero hfirst) hnext
    · have hlast : (x.indexEquiv I).2.val + 1 =
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
            (x.indexEquiv I).1 := by
        have hbound := (x.indexEquiv I).2.isLt
        omega
      exact D.noCollision_common_after_last_coordinate_of_alignment
        hsmall hlarge a b i hi c hposition hlargeAfter hcoordinates
          hcommonPositions hlast

/-- The adjacent exceptional interval, consisting of the selected rank-one
block and the intermediate common block, fits in the global BONG sequence. -/
theorem unaryShift_interval_bound
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) :
    (∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n := by
  let w := D.largeNoCollisionProfileWitness hlarge a
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hc : 0 < c := by
    exact D.complementStrictWeak.component_finrank_pos i₀
  have hrank :
      (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          D.smallSelectedPosition = c := by
    exact D.unaryShift_largeComponentRank_at_smallSelected
      hlarge hfin i₀ hi₀
  let last : Fin
      ((D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
        D.smallSelectedPosition) :=
    ⟨c - 1, by rw [hrank]; omega⟩
  have hlast :
      (∑ p ∈ Finset.Iio D.smallSelectedPosition,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
          (c - 1) < n := by
    calc
      _ = (w.indexEquiv.symm ⟨D.smallSelectedPosition, last⟩).val := by
        symm
        simpa only [last, Fin.val_mk] using
          w.inverse_index_val D.smallSelectedPosition last
      _ < n := (w.indexEquiv.symm ⟨D.smallSelectedPosition, last⟩).isLt
  rw [D.unaryShift_largePrefixRank_at_smallSelected
    hlarge hfin i₀ hi₀] at hlast
  dsimp only [c] at hc hlast ⊢
  omega

/-- A global coordinate below the exceptional interval start belongs to a
component strictly before the larger selected component. -/
theorem unaryShift_component_before_of_index_lt_start
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (I : Fin n)
    (hindex : I.val <
      ∑ p ∈ Finset.Iio D.largeSelectedPosition,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) :
    ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 <
      D.largeSelectedPosition := by
  let x := D.largeNoCollisionProfileWitness hlarge a
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
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) ≤
        ∑ p ∈ Finset.Iio (x.indexEquiv I).1,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p :=
    Finset.sum_le_sum_of_subset hsubset
  have hglobal := x.index_val_eq_componentStart_add_local I
  omega

/-- A global coordinate at or beyond the end of the exceptional interval
belongs to a component strictly after the intermediate common component. -/
theorem unaryShift_component_after_of_interval_end_le_index
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (I : Fin n)
    (hindex :
      (∑ p ∈ Finset.Iio D.largeSelectedPosition,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
          (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
        I.val) :
    D.smallSelectedPosition <
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let k := (x.indexEquiv I).1
  by_contra hnot
  have hk : k ≤ D.smallSelectedPosition := le_of_not_gt hnot
  have hsubset : Finset.Iic k ⊆ Finset.Iic D.smallSelectedPosition := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans hk)
  have hendLe :
      (∑ p ∈ Finset.Iio k,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank k ≤
        (∑ p ∈ Finset.Iio D.smallSelectedPosition,
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
            D.smallSelectedPosition := by
    rw [← sum_Iic_eq_sum_Iio_add, ← sum_Iic_eq_sum_Iio_add]
    exact Finset.sum_le_sum_of_subset hsubset
  have hglobal := x.index_val_lt_componentEnd I
  have hprefix := D.unaryShift_largePrefixRank_at_smallSelected
    hlarge hfin i₀ hi₀
  have hrank := D.unaryShift_largeComponentRank_at_smallSelected
    hlarge hfin i₀ hi₀
  change I.val <
      (∑ p ∈ Finset.Iio k,
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank p) +
      (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank k
    at hglobal
  omega

end Lattice.Beli2019Lemma51Data

end Bong
