/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517CollisionProfiles

/-!
# The unary adjacent shift in Beli (2019), Lemma 5.17(i)

When the distinguished component has rank one, the enlarged component can
move one Jordan slot to the left across the unique component of intermediate
scale.  The range in Lemma 5.17 stops before that transposition.  Consequently
the two weak profiles have the same coordinates and scales throughout the
relevant range, while possible equal-scale endpoint amalgamations are handled
by the strict resolutions constructed in
`Beli2019Lemma517CollisionProfiles`.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Lemma 5.17(i) before the unary transposition when the large coordinate
is internal after resolving a possible equal-scale collision. -/
theorem weakUnaryShift_prefixAlphaCap_le_of_internalResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      let g : Fin (n + 1) := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1))
    (hinternal :
      let g : Fin (n + 1) := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).2.val + 1 <
          finrank K (D.largeAlmostJordan.component
            ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1).carrier ∨
        ∃ c : Fin D.complementComponentCount,
          ordUnit K (D.complementStrictWeak.scaleGenerator c) =
              ordUnit K D.input.block.enlargedScaleGenerator ∧
            ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 =
              D.largeCommonPosition c) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  let g : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    have := i.pos
    omega⟩
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 < D.largeSelectedPosition at hbefore
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_before
    hfin i₀ hi₀ a b I hbefore
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hadjacent :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    change (y.indexEquiv I).1.val < D.smallSelectedPosition.val
    have hcoordinateVal := congrArg Fin.val hcoordinates.1
    change (x.indexEquiv I).1.val < D.largeSelectedPosition.val at hbefore
    omega
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBefore.le
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hbefore.le hinternal
  have hweakScale := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  have hscale : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      Rsmall.jordan.fundamentalScaleOrder
        (Rsmall.profile.indexEquiv I).1 := by
    rw [Rlarge.scaleOrder_eq, Rsmall.scaleOrder_eq, ← hcoordinates.1]
    exact hweakScale.le
  have hbound : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    rw [Rlarge.scaleOrder_eq]
    have h := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using h
  have hweight := D.largeFundamentalWeightOrder_le_small_of_scale_le
    (J := Rsmall.jordan) (H := Rlarge.jordan)
    (Rsmall.profile.indexEquiv I).1
    (Rlarge.profile.indexEquiv I).1 hscale hbound
  have hlargeFormula :=
    Rlarge.profile.internal_weightOrder_eq_order_add_alpha g Rlarge.internal
  have hsmallUpper :=
    Rsmall.profile.fundamentalWeightOrder_le_order_add_alpha g
  have hweightQ :
      (Rlarge.jordan.fundamentalWeightOrder
          (Rlarge.profile.indexEquiv I).1 : ℚ) ≤
        (Rsmall.jordan.fundamentalWeightOrder
          (Rsmall.profile.indexEquiv I).1 : ℚ) := by
    exact_mod_cast hweight
  have hcurrent' : a.order I = b.order I := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega)] at hcurrent
    have hraw :
        a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ =
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
      simpa only [BONG.GoodBONG.orderSequence_at] using hcurrent
    have hindex : I =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hraw
  have hcurrentQ : (a.order I : ℚ) = (b.order I : ℚ) := by
    exact_mod_cast hcurrent'
  have halpha : a.alphaValue g ≤ b.alphaValue g := by
    linarith
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large]
  exact_mod_cast halpha

/-- Lemma 5.17(i) at a strict boundary before the unary transposition.
The successor weak component may be the left slot of the transposition;
there the large scale is `r'` and the small scale is the intermediate
scale `r' + 1`. -/
theorem weakUnaryShift_prefixAlphaCap_le_of_boundaryResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      let g : Fin (n + 1) := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 <
        D.largeSelectedPosition)
    (hlast :
      let g : Fin (n + 1) := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).2.val + 1 =
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1).carrier)
    (hnotCollisionLeft :
      let g : Fin (n + 1) := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ¬ ∃ c : Fin D.complementComponentCount,
        ordUnit K (D.complementStrictWeak.scaleGenerator c) =
            ordUnit K D.input.block.enlargedScaleGenerator ∧
          ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 =
            D.largeCommonPosition c) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  let g : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    have := i.pos
    omega⟩
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (x.indexEquiv I).1 < D.largeSelectedPosition at hbefore
  change (x.indexEquiv I).2.val + 1 =
    finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      at hlast
  change ¬ ∃ c : Fin D.complementComponentCount,
    ordUnit K (D.complementStrictWeak.scaleGenerator c) =
        ordUnit K D.input.block.enlargedScaleGenerator ∧
      (x.indexEquiv I).1 = D.largeCommonPosition c at hnotCollisionLeft
  have hcoordinates := D.weakUnaryShift_profile_coordinates_eq_before
    hfin i₀ hi₀ a b I hbefore
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hadjacent :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    change (y.indexEquiv I).1.val < D.smallSelectedPosition.val
    have hcoordinateVal := congrArg Fin.val hcoordinates.1
    change (x.indexEquiv I).1.val < D.largeSelectedPosition.val at hbefore
    omega
  have hsmallLast : (y.indexEquiv I).2.val + 1 =
      finrank K (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier := by
    have hrank := D.weakUnaryShift_componentRank_eq_before
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
    have hrank' : finrank K (D.largeAlmostJordan.component
          (x.indexEquiv I).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv I).1).carrier := by
      calc
        finrank K (D.largeAlmostJordan.component
            (x.indexEquiv I).1).carrier =
            finrank K (D.smallAlmostJordan.component
              (x.indexEquiv I).1).carrier := hrank
        _ = finrank K (D.smallAlmostJordan.component
              (y.indexEquiv I).1).carrier := by rw [hcoordinates.1]
    omega
  obtain ⟨Rlarge⟩ := D.nonempty_largeStrictBoundaryResolution
    a g hbefore hlast hnotCollisionLeft
  obtain ⟨Rsmall⟩ := D.nonempty_smallStrictBoundaryResolution
    b g hsmallBefore hsmallLast
  have hnextEq : Rlarge.weakNext = Rsmall.weakNext := by
    apply Fin.ext
    rw [Rlarge.weakNext_val, Rsmall.weakNext_val]
    exact congrArg (fun p : Fin (D.complementComponentCount + 1) ↦ p.val + 1)
      hcoordinates.1
  have hleftWeak :
      ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1) =
        ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1) := by
    have h := D.weakUnaryShift_scaleOrder_eq_before_selected
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
    rw [← hcoordinates.1]
    exact h
  have hnextLe : Rlarge.weakNext ≤ D.largeSelectedPosition := by
    change Rlarge.weakNext.val ≤ D.largeSelectedPosition.val
    have hnextVal := Rlarge.weakNext_val
    change Rlarge.weakNext.val = (x.indexEquiv I).1.val + 1 at hnextVal
    rw [hnextVal]
    change (x.indexEquiv I).1.val < D.largeSelectedPosition.val at hbefore
    omega
  have hrightWeak :
      ordUnit K (D.largeAlmostJordan.scaleGenerator Rlarge.weakNext) ≤
        ordUnit K (D.smallAlmostJordan.scaleGenerator Rsmall.weakNext) := by
    by_cases hnextBefore : Rlarge.weakNext < D.largeSelectedPosition
    · have h := D.weakUnaryShift_scaleOrder_eq_before_selected
        hfin i₀ hi₀ Rlarge.weakNext hnextBefore
      rw [← hnextEq]
      exact h.le
    · have hnextPosition : Rlarge.weakNext = D.largeSelectedPosition :=
        le_antisymm hnextLe (le_of_not_gt hnextBefore)
      have hsmallNextPosition :
          Rsmall.weakNext = D.largeSelectedPosition := by
        calc
          Rsmall.weakNext = Rlarge.weakNext := hnextEq.symm
          _ = D.largeSelectedPosition := hnextPosition
      have hcommon :=
        D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
          hfin i₀ hi₀
      rw [hnextPosition, hsmallNextPosition,
        D.largeAlmostJordan_scaleGenerator_selected, ← hcommon,
        D.smallAlmostJordan_scaleGenerator_common, hi₀]
      omega
  have hleftBound :
      ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1) ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
    have h := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using h
  have hrightBound :
      ordUnit K (D.largeAlmostJordan.scaleGenerator Rlarge.weakNext) ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
    have h := D.largeAlmostJordan.scaleOrder_mono hnextLe
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using h
  let lSmall := Lattice.JordanDecomposition.boundaryLeftIndex Rsmall.boundary
  let rSmall := Lattice.JordanDecomposition.boundaryRightIndex Rsmall.boundary
  let lLarge := Lattice.JordanDecomposition.boundaryLeftIndex Rlarge.boundary
  let rLarge := Lattice.JordanDecomposition.boundaryRightIndex Rlarge.boundary
  have hleftScale : Rsmall.jordan.fundamentalScaleOrder lSmall =
      Rlarge.jordan.fundamentalScaleOrder lLarge := by
    rw [Rsmall.leftScaleOrder_eq, Rlarge.leftScaleOrder_eq]
    exact hleftWeak.symm
  have hrightScale : Rlarge.jordan.fundamentalScaleOrder rLarge ≤
      Rsmall.jordan.fundamentalScaleOrder rSmall := by
    rw [Rlarge.rightScaleOrder_eq, Rsmall.rightScaleOrder_eq]
    exact hrightWeak
  have hleftLattice : Rsmall.jordan.fundamentalLattice lSmall ≤
      Rlarge.jordan.fundamentalLattice lLarge := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan) lSmall lLarge
    · exact hleftScale.symm.le
    · rw [Rlarge.leftScaleOrder_eq]
      exact hleftBound
  have hrightLattice : Rsmall.jordan.fundamentalLattice rSmall ≤
      Rlarge.jordan.fundamentalLattice rLarge := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan) rSmall rLarge
    · exact hrightScale
    · rw [Rlarge.rightScaleOrder_eq]
      exact hrightBound
  have halpha := BONG.alphaValue_le_of_boundary_fundamentalLattices_le_at
    a b Rsmall.profile Rlarge.profile Rsmall.boundary Rlarge.boundary
      hleftScale hleftLattice hrightLattice
  rw [Rlarge.boundaryIndex_eq, Rsmall.boundaryIndex_eq] at halpha
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large]
  exact_mod_cast halpha

/-- Complete Lemma 5.17(i) in the exceptional unary adjacent-transposition
case.  The rank-one cutoff forces the relevant coordinate to occur strictly
before the transposed interval. -/
theorem weakUnaryShift_prefixAlphaCap_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  have hnpos : 0 < n := by
    have hiPos := i.pos
    have hiLt := i.lt_large
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  let g : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    have := i.pos
    omega⟩
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  have hbeforeIndex : I.val < D.largeSelectedStart := by
    change i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hi
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hi
    have hIval : I.val = i.val - 1 := rfl
    rw [hIval]
    have := i.pos
    omega
  have hbefore : (x.indexEquiv I).1 < D.largeSelectedPosition :=
    D.weakUnaryShift_component_before_of_index_lt_start a I (by
      simpa only [largeSelectedStart] using hbeforeIndex)
  by_cases hinternal : (x.indexEquiv I).2.val + 1 <
      finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
  · exact D.weakUnaryShift_prefixAlphaCap_le_of_internalResolution
      hfin i₀ hi₀ a b i hbefore hcurrent (Or.inl hinternal)
  · have hlast : (x.indexEquiv I).2.val + 1 =
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      have hlocal := (x.indexEquiv I).2.isLt
      omega
    by_cases hcollisionLeft : ∃ c : Fin D.complementComponentCount,
        ordUnit K (D.complementStrictWeak.scaleGenerator c) =
            ordUnit K D.input.block.enlargedScaleGenerator ∧
          (x.indexEquiv I).1 = D.largeCommonPosition c
    · exact D.weakUnaryShift_prefixAlphaCap_le_of_internalResolution
        hfin i₀ hi₀ a b i hbefore hcurrent (Or.inr hcollisionLeft)
    · exact D.weakUnaryShift_prefixAlphaCap_le_of_boundaryResolution
        hfin i₀ hi₀ a b i hbefore hlast hcollisionLeft

/-- Beli (2019), Lemma 5.17(i), uniformly for distinguished blocks of
rank one or two and for every possible weak-profile collision. -/
theorem weakAllRanks_prefixAlphaCap_le_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  rcases D.rank_one_or_two with hOne | hTwo
  · rcases D.selectedPositions_unary_alternative hOne with
      hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
    · exact D.weakAligned_prefixAlphaCap_le
        hselected a b i hi hcurrent
    · exact D.weakUnaryShift_prefixAlphaCap_le
        hOne i₀ hi₀ a b i hi hcurrent
  · exact D.weakAligned_prefixAlphaCap_le
      (D.selectedPositions_eq_of_rank_two hTwo) a b i hi hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
