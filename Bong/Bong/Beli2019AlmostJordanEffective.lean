/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanPosition

/-!
# Effective norm comparison for the two almost Jordan decompositions

The two sorted decompositions contain the same common components, but their
selected components have different scale and norm orders.  This file proves
the finite-minimum comparisons used in Beli (2019), Section 5.4.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- In the unary case the selected smaller component itself realizes the
minimum at its scale, so the effective norm order equals the scale order. -/
theorem smallSelected_effectiveNormOrder_eq_scale_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) =
      ordUnit K D.input.block.scaleGenerator := by
  apply le_antisymm
  · calc
      D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) ≤
          JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily
            (ordUnit K D.input.block.scaleGenerator)
            D.smallSelectedPosition :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = ordUnit K D.input.block.scaleGenerator := by
        have hnorm := D.smallSelected_normOrder_eq_scaleOrder_of_rank_one (by
          simpa only [D.smallAlmostJordan_finrank_selected] using hfin)
        simp [JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily, hnorm]
  · exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      D.smallSelectedPosition (ordUnit K D.input.block.scaleGenerator)

/-- If a common component is effective-improper on the larger side, its
rank is even.  This transports the parity invariant retained during
O'Meara amalgamation through the sorted almost-Jordan decomposition. -/
theorem largeCommon_componentRank_even_of_scale_lt_effective
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hstrict : ordUnit K (D.complementStrictWeak.scaleGenerator i) <
      D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i))) :
    Even (finrank K
      (D.largeAlmostJordan.component (D.largeCommonPosition i)).carrier) := by
  have heffectiveStrict :
      ordUnit K (D.largeAlmostJordan.scaleGenerator
          (D.largeCommonPosition i)) <
        D.largeAlmostJordan.effectiveNormOrderAt (D.largeCommonPosition i)
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (D.largeCommonPosition i))) := by
    simpa only [D.largeAlmostJordan_scaleGenerator_common] using hstrict
  have hnormStrict :
      ordUnit K (D.largeAlmostJordan.scaleGenerator
          (D.largeCommonPosition i)) <
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          (D.largeCommonPosition i)) :=
    heffectiveStrict.trans_le
      (D.largeAlmostJordan.effectiveNormOrderAt_scale_le_normOrder
        (D.largeCommonPosition i))
  have hcomplementStrict :
      ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
    simpa only [D.largeAlmostJordan_scaleGenerator_common,
      D.largeAlmostJordan_normOrder_common_eq_complement] using hnormStrict
  rw [D.largeAlmostJordan_finrank_common]
  exact D.complementStrictWeak_hasImproperEvenRank i hcomplementStrict

/-- The corresponding effective-improper parity statement on the smaller
side. -/
theorem smallCommon_componentRank_even_of_scale_lt_effective
    (D : Beli2019Lemma51Data q M N)
    (i : Fin D.complementComponentCount)
    (hstrict : ordUnit K (D.complementStrictWeak.scaleGenerator i) <
      D.smallAlmostJordan.effectiveNormOrderAt (D.smallCommonPosition i)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i))) :
    Even (finrank K
      (D.smallAlmostJordan.component (D.smallCommonPosition i)).carrier) := by
  have heffectiveStrict :
      ordUnit K (D.smallAlmostJordan.scaleGenerator
          (D.smallCommonPosition i)) <
        D.smallAlmostJordan.effectiveNormOrderAt (D.smallCommonPosition i)
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (D.smallCommonPosition i))) := by
    simpa only [D.smallAlmostJordan_scaleGenerator_common] using hstrict
  have hnormStrict :
      ordUnit K (D.smallAlmostJordan.scaleGenerator
          (D.smallCommonPosition i)) <
        ordUnit K (D.smallAlmostJordan.normGeneratorUnit
          (D.smallCommonPosition i)) :=
    heffectiveStrict.trans_le
      (D.smallAlmostJordan.effectiveNormOrderAt_scale_le_normOrder
        (D.smallCommonPosition i))
  have hcomplementStrict :
      ordUnit K (D.complementStrictWeak.scaleGenerator i) <
        ordUnit K (D.complementStrictWeak.normGeneratorUnit i) := by
    simpa only [D.smallAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_normOrder_common_eq_complement] using hnormStrict
  rw [D.smallAlmostJordan_finrank_common]
  exact D.complementStrictWeak_hasImproperEvenRank i hcomplementStrict

/-- The analogous unary equality on the enlarged side. -/
theorem largeSelected_effectiveNormOrder_eq_scale_of_rank_one
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1) :
    D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator) =
      ordUnit K D.input.block.enlargedScaleGenerator := by
  apply le_antisymm
  · calc
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) ≤
          JordanProfileOrder.adjustedAt
            D.largeAlmostJordan.scaleOrderFamily
            D.largeAlmostJordan.normOrderFamily
            (ordUnit K D.input.block.enlargedScaleGenerator)
            D.largeSelectedPosition :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = ordUnit K D.input.block.enlargedScaleGenerator := by
        have hnorm := D.largeSelected_normOrder_eq_scaleOrder_of_rank_one (by
          simpa only [D.largeAlmostJordan_finrank_selected] using hfin)
        simp [JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily, hnorm]
  · exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      D.largeSelectedPosition
      (ordUnit K D.input.block.enlargedScaleGenerator)

/-- At a target scale strictly below the smaller selected scale, the
selected contribution on the larger side is no greater. -/
theorem largeSelected_adjusted_le_smallSelected_of_target_lt
    (D : Beli2019Lemma51Data q M N) (target : Int)
    (htarget : target < ordUnit K D.input.block.scaleGenerator) :
    JordanProfileOrder.adjustedAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily target
        D.largeSelectedPosition ≤
      JordanProfileOrder.adjustedAt
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily target
        D.smallSelectedPosition := by
  rcases D.rank_one_or_two with hOne | hTwo
  · have hlargeNorm :=
      D.largeSelected_normOrder_eq_scaleOrder_of_rank_one (by
        simpa only [D.largeAlmostJordan_finrank_selected] using hOne)
    have hsmallNorm :=
      D.smallSelected_normOrder_eq_scaleOrder_of_rank_one (by
        simpa only [D.smallAlmostJordan_finrank_selected] using hOne)
    have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        h | h
      · exact h.2
      · omega
    simp only [JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected,
      hlargeNorm, hsmallNorm]
    split <;> split <;> omega
  · have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 1 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        h | h
      · omega
      · exact h.2
    have hnorm := D.largeSelected_normOrder_le_smallSelected
    simp only [JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected]
    split <;> split <;> omega

/-- At a target scale strictly above the larger selected scale, the
selected contribution on the smaller side is no greater. -/
theorem smallSelected_adjusted_le_largeSelected_of_large_lt_target
    (D : Beli2019Lemma51Data q M N) (target : Int)
    (htarget : ordUnit K D.input.block.enlargedScaleGenerator < target) :
    JordanProfileOrder.adjustedAt
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily target
        D.smallSelectedPosition ≤
      JordanProfileOrder.adjustedAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily target
        D.largeSelectedPosition := by
  rcases D.rank_one_or_two with hOne | hTwo
  · have hlargeNorm :=
      D.largeSelected_normOrder_eq_scaleOrder_of_rank_one (by
        simpa only [D.largeAlmostJordan_finrank_selected] using hOne)
    have hsmallNorm :=
      D.smallSelected_normOrder_eq_scaleOrder_of_rank_one (by
        simpa only [D.smallAlmostJordan_finrank_selected] using hOne)
    have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        h | h
      · exact h.2
      · omega
    simp only [JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected,
      hlargeNorm, hsmallNorm]
    split <;> omega
  · have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 1 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        h | h
      · omega
      · exact h.2
    have hnorm := D.smallSelected_normOrder_le_largeSelected_add_two
    simp only [JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected]
    split <;> omega

/-- Before the smaller selected scale, effective norm orders on the larger
side are no greater than those on the smaller side. -/
theorem large_effectiveNormOrderAt_le_small_of_target_lt
    (D : Beli2019Lemma51Data q M N)
    (largeAnchor : Fin (D.complementComponentCount + 1))
    (smallAnchor : Fin (D.complementComponentCount + 1))
    (target : Int)
    (htarget : target < ordUnit K D.input.block.scaleGenerator) :
    D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target ≤
      D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target := by
  let e := D.largeToSmallPositionEquiv
  rw [WeakJordanDecomposition.effectiveNormOrderAt,
    WeakJordanDecomposition.effectiveNormOrderAt,
    ← JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e largeAnchor smallAnchor target]
  apply JordanProfileOrder.effectiveAt_mono
  intro p
  rcases D.largePosition_eq_selected_or_common p with hp | ⟨i, hp⟩
  · subst p
    simpa only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
      largeToSmallPositionEquiv_selected] using
      D.largeSelected_adjusted_le_smallSelected_of_target_lt
        target htarget
  · subst p
    simp only [e, Function.comp_apply, largeToSmallPositionEquiv_common,
      JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_common,
      D.common_normOrder_eq]
    exact le_rfl

/-- After the larger selected scale, effective norm orders on the smaller
side are no greater than those on the larger side. -/
theorem small_effectiveNormOrderAt_le_large_of_large_lt_target
    (D : Beli2019Lemma51Data q M N)
    (smallAnchor : Fin (D.complementComponentCount + 1))
    (largeAnchor : Fin (D.complementComponentCount + 1))
    (target : Int)
    (htarget : ordUnit K D.input.block.enlargedScaleGenerator < target) :
    D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target ≤
      D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target := by
  let e := D.largeToSmallPositionEquiv
  rw [WeakJordanDecomposition.effectiveNormOrderAt,
    WeakJordanDecomposition.effectiveNormOrderAt,
    ← JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e largeAnchor smallAnchor target]
  apply JordanProfileOrder.effectiveAt_mono
  intro p
  rcases D.largePosition_eq_selected_or_common p with hp | ⟨i, hp⟩
  · subst p
    simpa only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
      largeToSmallPositionEquiv_selected] using
      D.smallSelected_adjusted_le_largeSelected_of_large_lt_target
        target htarget
  · subst p
    simp only [e, Function.comp_apply, largeToSmallPositionEquiv_common,
      JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_common,
      D.common_normOrder_eq]
    exact le_rfl

/-- At the two selected scales themselves, the larger-lattice effective
norm is no greater than the smaller-lattice effective norm. -/
theorem largeSelected_effectiveNormOrder_le_smallSelected
    (D : Beli2019Lemma51Data q M N) :
    D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator) ≤
      D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) := by
  let e := D.largeToSmallPositionEquiv
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator ≤
      ordUnit K D.input.block.scaleGenerator := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with h | h <;>
      omega
  rw [WeakJordanDecomposition.effectiveNormOrderAt,
    WeakJordanDecomposition.effectiveNormOrderAt,
    ← JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e D.largeSelectedPosition
      D.smallSelectedPosition
      (ordUnit K D.input.block.scaleGenerator)]
  apply JordanProfileOrder.effectiveAt_mono_cross
  intro p
  rcases D.largePosition_eq_selected_or_common p with hp | ⟨i, hp⟩
  · subst p
    have hnorm := D.largeSelected_normOrder_le_smallSelected
    simpa only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
      largeToSmallPositionEquiv_selected,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected,
      lt_self_iff_false, if_false] using hnorm
  · subst p
    have hmono := JordanProfileOrder.adjustedAt_mono_target
      D.largeAlmostJordan.scaleOrderFamily
      D.largeAlmostJordan.normOrderFamily hscale
      (D.largeCommonPosition i)
    simpa only [e, Function.comp_apply,
      largeToSmallPositionEquiv_common,
      JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_common,
      D.common_normOrder_eq] using hmono

/-- In the binary case the effective norm at the smaller selected scale is
at most two above the effective norm at the enlarged selected scale. -/
theorem smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 2) :
    D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) ≤
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator) + 2 := by
  have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 1 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · omega
    · exact hTwo.2
  calc
    D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) ≤
        D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.scaleGenerator) :=
      D.small_effectiveNormOrderAt_le_large_of_large_lt_target
        D.smallSelectedPosition D.largeSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) (by omega)
    _ ≤ D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) +
          2 * (ordUnit K D.input.block.scaleGenerator -
            ordUnit K D.input.block.enlargedScaleGenerator) := by
      exact JordanProfileOrder.effectiveAt_target_le_add_two_mul_sub
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily
        D.largeSelectedPosition D.largeSelectedPosition (by omega)
    _ = D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) + 2 := by
      omega

/-- If the left-side effective comparison is strict, its minimum is attained
by the selected component of the larger lattice. -/
theorem large_effectiveNormOrderAt_eq_selected_of_lt
    (D : Beli2019Lemma51Data q M N)
    (largeAnchor smallAnchor : Fin (D.complementComponentCount + 1))
    (target : Int)
    (hlt : D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target <
      D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target) :
    D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target =
      JordanProfileOrder.adjustedAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily target
        D.largeSelectedPosition := by
  let e := D.largeToSmallPositionEquiv
  have hlt' : JordanProfileOrder.effectiveAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily largeAnchor target <
      JordanProfileOrder.effectiveAt
        (D.smallAlmostJordan.scaleOrderFamily ∘ e)
        (D.smallAlmostJordan.normOrderFamily ∘ e) largeAnchor target := by
    rw [JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e largeAnchor smallAnchor target]
    exact hlt
  change JordanProfileOrder.effectiveAt
      D.largeAlmostJordan.scaleOrderFamily
      D.largeAlmostJordan.normOrderFamily largeAnchor target = _
  apply JordanProfileOrder.effectiveAt_eq_distinguished_of_lt
    D.largeAlmostJordan.scaleOrderFamily
    D.largeAlmostJordan.normOrderFamily
    (D.smallAlmostJordan.scaleOrderFamily ∘ e)
    (D.smallAlmostJordan.normOrderFamily ∘ e)
    largeAnchor largeAnchor D.largeSelectedPosition target
  · intro p hp
    rcases D.largePosition_eq_selected_or_common p with hselected | ⟨i, hcommon⟩
    · exact (hp hselected).elim
    · subst p
      simp only [e, Function.comp_apply,
        largeToSmallPositionEquiv_common,
        JordanProfileOrder.adjustedAt,
        WeakJordanDecomposition.scaleOrderFamily,
        WeakJordanDecomposition.normOrderFamily,
        D.largeAlmostJordan_scaleGenerator_common,
        D.smallAlmostJordan_scaleGenerator_common,
        D.common_normOrder_eq]
  · exact hlt'

/-- If the right-side comparison is strict, its minimum is attained by the
selected component of the smaller lattice. -/
theorem small_effectiveNormOrderAt_eq_selected_of_lt
    (D : Beli2019Lemma51Data q M N)
    (smallAnchor largeAnchor : Fin (D.complementComponentCount + 1))
    (target : Int)
    (hlt : D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target <
      D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target) :
    D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target =
      JordanProfileOrder.adjustedAt
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily target
        D.smallSelectedPosition := by
  let e := D.largeToSmallPositionEquiv
  have hlt' : JordanProfileOrder.effectiveAt
        (D.smallAlmostJordan.scaleOrderFamily ∘ e)
        (D.smallAlmostJordan.normOrderFamily ∘ e) largeAnchor target <
      JordanProfileOrder.effectiveAt
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily largeAnchor target := by
    rw [JordanProfileOrder.effectiveAt_comp_equiv
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily e largeAnchor smallAnchor target]
    exact hlt
  have hforce := JordanProfileOrder.effectiveAt_eq_distinguished_of_lt
    (D.smallAlmostJordan.scaleOrderFamily ∘ e)
    (D.smallAlmostJordan.normOrderFamily ∘ e)
    D.largeAlmostJordan.scaleOrderFamily
    D.largeAlmostJordan.normOrderFamily
    largeAnchor largeAnchor D.largeSelectedPosition target (by
      intro p hp
      rcases D.largePosition_eq_selected_or_common p with
        hselected | ⟨i, hcommon⟩
      · exact (hp hselected).elim
      · subst p
        simp only [e, Function.comp_apply,
          largeToSmallPositionEquiv_common,
          JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily,
          D.largeAlmostJordan_scaleGenerator_common,
          D.smallAlmostJordan_scaleGenerator_common,
          D.common_normOrder_eq]) hlt'
  calc
    D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target =
        JordanProfileOrder.effectiveAt
          (D.smallAlmostJordan.scaleOrderFamily ∘ e)
          (D.smallAlmostJordan.normOrderFamily ∘ e)
          largeAnchor target := by
      exact (JordanProfileOrder.effectiveAt_comp_equiv
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily e largeAnchor smallAnchor target).symm
    _ = JordanProfileOrder.adjustedAt
          (D.smallAlmostJordan.scaleOrderFamily ∘ e)
          (D.smallAlmostJordan.normOrderFamily ∘ e) target
          D.largeSelectedPosition := hforce
    _ = JordanProfileOrder.adjustedAt
          D.smallAlmostJordan.scaleOrderFamily
          D.smallAlmostJordan.normOrderFamily target
          D.smallSelectedPosition := by
      simp only [JordanProfileOrder.adjustedAt, e, Function.comp_apply,
        largeToSmallPositionEquiv_selected]

/-- A strict comparison before the larger selected scale forces all later
effective norms up to that scale to remain equal to the selected norm
order.  This is the propagation used at the last coordinate of a common
Jordan block in the left half of Section 5.4. -/
theorem large_effectiveNormOrderAt_eq_selectedNorm_of_lt
    (D : Beli2019Lemma51Data q M N)
    (largeAnchor smallAnchor laterAnchor :
      Fin (D.complementComponentCount + 1))
    (target later : Int)
    (htargetLater : target ≤ later)
    (hlater : later ≤ ordUnit K D.input.block.enlargedScaleGenerator)
    (hlt : D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target <
      D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target) :
    D.largeAlmostJordan.effectiveNormOrderAt laterAnchor later =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
  have htarget : target ≤
      ordUnit K D.input.block.enlargedScaleGenerator :=
    htargetLater.trans hlater
  have hforce := D.large_effectiveNormOrderAt_eq_selected_of_lt
    largeAnchor smallAnchor target hlt
  have hforce' : D.largeAlmostJordan.effectiveNormOrderAt
        largeAnchor target =
      ordUnit K (D.largeAlmostJordan.normGeneratorUnit
        D.largeSelectedPosition) := by
    simpa only [JordanProfileOrder.adjustedAt,
      WeakJordanDecomposition.scaleOrderFamily,
      WeakJordanDecomposition.normOrderFamily,
      D.largeAlmostJordan_scaleGenerator_selected,
      if_neg (not_lt_of_ge htarget)] using hforce
  apply le_antisymm
  · calc
      D.largeAlmostJordan.effectiveNormOrderAt laterAnchor later ≤
          JordanProfileOrder.adjustedAt
            D.largeAlmostJordan.scaleOrderFamily
            D.largeAlmostJordan.normOrderFamily later
            D.largeSelectedPosition :=
        JordanProfileOrder.effectiveAt_le
          D.largeAlmostJordan.scaleOrderFamily
          D.largeAlmostJordan.normOrderFamily laterAnchor
          D.largeSelectedPosition later
      _ = ordUnit K (D.largeAlmostJordan.normGeneratorUnit
            D.largeSelectedPosition) := by
        simp only [JordanProfileOrder.adjustedAt,
          WeakJordanDecomposition.scaleOrderFamily,
          WeakJordanDecomposition.normOrderFamily,
          D.largeAlmostJordan_scaleGenerator_selected,
          if_neg (not_lt_of_ge hlater)]
  · rw [← hforce']
    exact JordanProfileOrder.effectiveAt_mono_target
      D.largeAlmostJordan.scaleOrderFamily
      D.largeAlmostJordan.normOrderFamily largeAnchor laterAnchor
      htargetLater

/-- A strict comparison after the smaller selected scale propagates
backwards to every intervening target scale.  The selected contribution has
slope two, so once it is minimal at the right endpoint it remains minimal
when the target scale is lowered. -/
theorem small_effectiveNormOrderAt_eq_selectedAdjusted_of_lt
    (D : Beli2019Lemma51Data q M N)
    (smallAnchor largeAnchor earlierAnchor :
      Fin (D.complementComponentCount + 1))
    (earlier target : Int)
    (hselectedEarlier : ordUnit K D.input.block.scaleGenerator ≤ earlier)
    (hearlierTarget : earlier ≤ target)
    (hlt : D.smallAlmostJordan.effectiveNormOrderAt smallAnchor target <
      D.largeAlmostJordan.effectiveNormOrderAt largeAnchor target) :
    D.smallAlmostJordan.effectiveNormOrderAt earlierAnchor earlier =
      JordanProfileOrder.adjustedAt
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily earlier
        D.smallSelectedPosition := by
  have hforce := D.small_effectiveNormOrderAt_eq_selected_of_lt
    smallAnchor largeAnchor target hlt
  apply le_antisymm
  · exact JordanProfileOrder.effectiveAt_le
      D.smallAlmostJordan.scaleOrderFamily
      D.smallAlmostJordan.normOrderFamily earlierAnchor
      D.smallSelectedPosition earlier
  · apply JordanProfileOrder.le_effectiveAt
    intro p
    rcases D.smallPosition_eq_selected_or_common p with
      hselected | ⟨i, hcommon⟩
    · subst p
      exact le_rfl
    · subst p
      apply JordanProfileOrder.adjustedAt_le_of_le_at_larger_target_of_scale_le
        D.smallAlmostJordan.scaleOrderFamily
        D.smallAlmostJordan.normOrderFamily
        D.smallSelectedPosition (D.smallCommonPosition i)
        (by simpa only [WeakJordanDecomposition.scaleOrderFamily,
          D.smallAlmostJordan_scaleGenerator_selected] using
            hselectedEarlier)
        hearlierTarget
      have hlargeComponent := JordanProfileOrder.effectiveAt_le
        D.largeAlmostJordan.scaleOrderFamily
        D.largeAlmostJordan.normOrderFamily largeAnchor
        (D.largeCommonPosition i) target
      have hstrict : JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily target
            D.smallSelectedPosition <
          JordanProfileOrder.adjustedAt
            D.smallAlmostJordan.scaleOrderFamily
            D.smallAlmostJordan.normOrderFamily target
            (D.smallCommonPosition i) := by
        calc
          JordanProfileOrder.adjustedAt
              D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily target
              D.smallSelectedPosition =
              D.smallAlmostJordan.effectiveNormOrderAt
                smallAnchor target := hforce.symm
          _ < D.largeAlmostJordan.effectiveNormOrderAt
                largeAnchor target := hlt
          _ ≤ JordanProfileOrder.adjustedAt
                D.largeAlmostJordan.scaleOrderFamily
                D.largeAlmostJordan.normOrderFamily target
                (D.largeCommonPosition i) := hlargeComponent
          _ = JordanProfileOrder.adjustedAt
                D.smallAlmostJordan.scaleOrderFamily
              D.smallAlmostJordan.normOrderFamily target
                (D.smallCommonPosition i) := by
            simp only [JordanProfileOrder.adjustedAt,
              WeakJordanDecomposition.scaleOrderFamily,
              WeakJordanDecomposition.normOrderFamily,
              D.largeAlmostJordan_scaleGenerator_common,
              D.smallAlmostJordan_scaleGenerator_common,
              D.common_normOrder_eq]
      exact hstrict.le

end Lattice.Beli2019Lemma51Data

end Bong
