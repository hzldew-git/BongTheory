/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlmostJordanEffective
import Bong.Bong.Beli2019IndexPOrderAlignedBlock
import Bong.Bong.JordanOrderProfileSequence
import Bong.Bong.JordanProfileMerge

/-!
# Jordan profiles for Beli's almost Jordan decompositions

This file connects the sorted decompositions from Section 5.4 with the
canonical global coordinates in Beli's Lemma 4.7.  It first treats the
no-collision case, where both almost Jordan decompositions are already
strict and the distinguished insertion positions agree.
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

/-- In the absence of a small-side scale collision, the sorted weak
decomposition is already a genuine Jordan decomposition. -/
noncomputable def smallNoCollisionJordan
    (D : Beli2019Lemma51Data q M N) (h : ¬D.SmallScaleCollision) :
    JordanDecomposition q N (D.complementComponentCount + 1) :=
  D.smallAlmostJordan.toJordan
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision h)

/-- In the absence of a large-side scale collision, the sorted weak
decomposition is already a genuine Jordan decomposition. -/
noncomputable def largeNoCollisionJordan
    (D : Beli2019Lemma51Data q M N) (h : ¬D.LargeScaleCollision) :
    JordanDecomposition q M (D.complementComponentCount + 1) :=
  D.largeAlmostJordan.toJordan
    (D.largeAlmostJordan_scaleOrder_strict_of_noCollision h)

/-- Local-order formula with the no-collision wrapper left opaque. -/
theorem largeNoCollisionJordan_expectedOrder
    (D : Beli2019Lemma51Data q M N) (h : ¬D.LargeScaleCollision)
    (k : Fin (D.complementComponentCount + 1))
    (i : Fin ((D.largeNoCollisionJordan h).toOrthogonalDecomposition.componentRank k)) :
    BONG.jordanExpectedOrder (D.largeNoCollisionJordan h) k i =
      JordanProfileOrder.localOrder
        (ordUnit K (D.largeAlmostJordan.scaleGenerator k))
        (D.largeAlmostJordan.effectiveNormOrderAt k
          (ordUnit K (D.largeAlmostJordan.scaleGenerator k))) i.val := by
  unfold largeNoCollisionJordan
  exact D.largeAlmostJordan.jordanExpectedOrder_toJordan
    (D.largeAlmostJordan_scaleOrder_strict_of_noCollision h) k i

/-- The analogous opaque-wrapper formula on the smaller side. -/
theorem smallNoCollisionJordan_expectedOrder
    (D : Beli2019Lemma51Data q M N) (h : ¬D.SmallScaleCollision)
    (k : Fin (D.complementComponentCount + 1))
    (i : Fin ((D.smallNoCollisionJordan h).toOrthogonalDecomposition.componentRank k)) :
    BONG.jordanExpectedOrder (D.smallNoCollisionJordan h) k i =
      JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator k))
        (D.smallAlmostJordan.effectiveNormOrderAt k
          (ordUnit K (D.smallAlmostJordan.scaleGenerator k))) i.val := by
  unfold smallNoCollisionJordan
  exact D.smallAlmostJordan.jordanExpectedOrder_toJordan
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision h) k i

/-- If the distinguished insertion positions agree, the two strict
no-collision Jordan decompositions have equal component-rank families. -/
theorem noCollision_componentRank_eq
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition) :
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank =
      (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank := by
  funext p
  change finrank K (D.largeAlmostJordan.component p).carrier =
    finrank K (D.smallAlmostJordan.component p).carrier
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨i, hposition⟩
  · subst p
    calc
      finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier =
          finrank K D.input.block.component.carrier :=
        D.largeAlmostJordan_finrank_selected
      _ = finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier :=
        D.smallAlmostJordan_finrank_selected.symm
      _ = finrank K
          (D.smallAlmostJordan.component D.largeSelectedPosition).carrier := by
        rw [hselected]
  · subst p
    have hcommon := D.commonPositions_eq_of_selectedPositions_eq hselected i
    calc
      finrank K
          (D.largeAlmostJordan.component (D.largeCommonPosition i)).carrier =
          finrank K (D.complementStrictWeak.component i).carrier :=
        D.largeAlmostJordan_finrank_common i
      _ = finrank K
          (D.smallAlmostJordan.component (D.smallCommonPosition i)).carrier :=
        (D.smallAlmostJordan_finrank_common i).symm
      _ = finrank K
          (D.smallAlmostJordan.component (D.largeCommonPosition i)).carrier := by
        rw [hcommon]

/-- Lemma 4.7's profile witness for the larger no-collision Jordan
decomposition. -/
noncomputable def largeNoCollisionProfileWitness
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision) {n : Nat}
    (a : BONG.GoodBONG q M n) :
    BONG.JordanOrderProfileWitness a.toBONG
      (D.largeNoCollisionJordan hlarge) :=
  Classical.choice
    (a.toBONG.beliLemma47_profile a.good
      (D.largeNoCollisionJordan hlarge))

/-- Lemma 4.7's profile witness for the smaller no-collision Jordan
decomposition. -/
noncomputable def smallNoCollisionProfileWitness
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision) {n : Nat}
    (b : BONG.GoodBONG q N n) :
    BONG.JordanOrderProfileWitness b.toBONG
      (D.smallNoCollisionJordan hsmall) :=
  Classical.choice
    (b.toBONG.beliLemma47_profile b.good
      (D.smallNoCollisionJordan hsmall))

/-- Lemma 4.7, transported through the possible equal-scale amalgamation,
gives a profile indexed uniformly by the original larger almost-Jordan
family. -/
noncomputable def largeWeakProfileWitness
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N) {n : Nat}
    (a : BONG.GoodBONG q M n) :
    BONG.WeakJordanOrderProfileWitness a.toBONG D.largeAlmostJordan := by
  classical
  by_cases hcollision : D.LargeScaleCollision
  · let i := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent i hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    let S := D.largeAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt i hscale k hk)
    let w : BONG.JordanOrderProfileWitness a.toBONG
        (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    exact BONG.WeakJordanOrderProfileWitness.ofMerge
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank
      k heq hstrict w
  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let w : BONG.JordanOrderProfileWitness a.toBONG
        (D.largeAlmostJordan.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good
          (D.largeAlmostJordan.toJordan hstrict))
    exact BONG.WeakJordanOrderProfileWitness.ofStrict
      D.largeAlmostJordan hstrict w

/-- The analogous uniform profile on the smaller almost-Jordan family. -/
noncomputable def smallWeakProfileWitness
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N) {n : Nat}
    (b : BONG.GoodBONG q N n) :
    BONG.WeakJordanOrderProfileWitness b.toBONG D.smallAlmostJordan := by
  classical
  by_cases hcollision : D.SmallScaleCollision
  · let i := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.smallCollision_adjacent i hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    have heq : ordUnit K
          (D.smallAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.smallAlmostJordan.scaleGenerator k.succ) := by
      rw [hk.1, hk.2]
      simpa only [D.smallAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_common] using hscale
    let S := D.smallAlmostJordan.mergeAdjacentAt k heq
    have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.smallAlmostJordan k heq
          (D.smallOnlyScaleCollisionAt i hscale k hk)
    let w : BONG.JordanOrderProfileWitness b.toBONG
        (S.toJordan hstrict) :=
      Classical.choice
        (b.toBONG.beliLemma47_profile b.good (S.toJordan hstrict))
    exact BONG.WeakJordanOrderProfileWitness.ofMerge
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank
      k heq hstrict w
  · let hstrict := D.smallAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let w : BONG.JordanOrderProfileWitness b.toBONG
        (D.smallAlmostJordan.toJordan hstrict) :=
      Classical.choice
        (b.toBONG.beliLemma47_profile b.good
          (D.smallAlmostJordan.toJordan hstrict))
    exact BONG.WeakJordanOrderProfileWitness.ofStrict
      D.smallAlmostJordan hstrict w

/-- Equal distinguished insertion positions align the component-rank
families of the two original almost-Jordan decompositions, independently of
whether either adjacent equal-scale pair is amalgamated. -/
theorem almostJordan_componentRank_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition) :
    (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier) =
      fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier := by
  funext p
  rcases D.largePosition_eq_selected_or_common p with
    hposition | ⟨i, hposition⟩
  · subst p
    calc
      finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier =
          finrank K D.input.block.component.carrier :=
        D.largeAlmostJordan_finrank_selected
      _ = finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier :=
        D.smallAlmostJordan_finrank_selected.symm
      _ = finrank K
          (D.smallAlmostJordan.component D.largeSelectedPosition).carrier := by
        rw [hselected]
  · subst p
    have hcommon := D.commonPositions_eq_of_selectedPositions_eq hselected i
    calc
      finrank K
          (D.largeAlmostJordan.component (D.largeCommonPosition i)).carrier =
          finrank K (D.complementStrictWeak.component i).carrier :=
        D.largeAlmostJordan_finrank_common i
      _ = finrank K
          (D.smallAlmostJordan.component (D.smallCommonPosition i)).carrier :=
        (D.smallAlmostJordan_finrank_common i).symm
      _ = finrank K
          (D.smallAlmostJordan.component (D.largeCommonPosition i)).carrier := by
        rw [hcommon]

/-- The two uniform weak profiles choose identical component numbers and
local coordinates when the distinguished insertion positions agree. -/
theorem weakProfile_coordinates_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Fin n) :
    ((D.largeWeakProfileWitness a).indexEquiv i).1 =
        ((D.smallWeakProfileWitness b).indexEquiv i).1 ∧
      ((D.largeWeakProfileWitness a).indexEquiv i).2.val =
        ((D.smallWeakProfileWitness b).indexEquiv i).2.val :=
  (D.largeWeakProfileWitness a).indexEquiv_coordinates_eq_of_componentRank_eq
    (D.smallWeakProfileWitness b) (D.almostJordan_componentRank_eq hselected) i

/-- Uniform local-order formula on the larger almost-Jordan family. -/
theorem largeWeak_order_eq_localOrder
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N) {n : Nat}
    (a : BONG.GoodBONG q M n) (i : Fin n) :
    a.order i = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator
        ((D.largeWeakProfileWitness a).indexEquiv i).1))
      (D.largeAlmostJordan.effectiveNormOrderAt
        ((D.largeWeakProfileWitness a).indexEquiv i).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator
          ((D.largeWeakProfileWitness a).indexEquiv i).1)))
      ((D.largeWeakProfileWitness a).indexEquiv i).2.val := by
  exact (D.largeWeakProfileWitness a).order_eq i

/-- Uniform local-order formula on the smaller almost-Jordan family. -/
theorem smallWeak_order_eq_localOrder
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N) {n : Nat}
    (b : BONG.GoodBONG q N n) (i : Fin n) :
    b.order i = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator
        ((D.smallWeakProfileWitness b).indexEquiv i).1))
      (D.smallAlmostJordan.effectiveNormOrderAt
        ((D.smallWeakProfileWitness b).indexEquiv i).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          ((D.smallWeakProfileWitness b).indexEquiv i).1)))
      ((D.smallWeakProfileWitness b).indexEquiv i).2.val := by
  exact (D.smallWeakProfileWitness b).order_eq i

/-- A common component strictly before the smaller selected component has
strictly smaller scale, even when the endpoint collision is allowed. -/
theorem smallCommon_scale_lt_selected_of_position_lt
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hpos : D.smallCommonPosition c < D.smallSelectedPosition) :
    ordUnit K (D.complementStrictWeak.scaleGenerator c) <
      ordUnit K D.input.block.scaleGenerator := by
  have hle := D.smallAlmostJordan.scaleOrder_mono hpos.le
  have hle' : ordUnit K (D.complementStrictWeak.scaleGenerator c) ≤
      ordUnit K D.input.block.scaleGenerator := by
    simpa only [D.smallAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_selected] using hle
  apply lt_of_le_of_ne hle'
  intro heq
  have hreverse := D.smallSelectedPosition_lt_common_of_scaleOrder_eq c heq.symm
  exact (lt_asymm hpos hreverse).elim

/-- A common component strictly after the larger selected component has
strictly larger scale, even when the endpoint collision is allowed. -/
theorem largeSelected_scale_lt_common_of_position_lt
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hpos : D.largeSelectedPosition < D.largeCommonPosition c) :
    ordUnit K D.input.block.enlargedScaleGenerator <
      ordUnit K (D.complementStrictWeak.scaleGenerator c) := by
  have hle := D.largeAlmostJordan.scaleOrder_mono hpos.le
  have hle' : ordUnit K D.input.block.enlargedScaleGenerator ≤
      ordUnit K (D.complementStrictWeak.scaleGenerator c) := by
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hle
  apply lt_of_le_of_ne hle'
  intro heq
  have hreverse := D.largeCommonPosition_lt_selected_of_scaleOrder_eq c heq.symm
  exact (lt_asymm hpos hreverse).elim

/-- Equal insertion positions align both the component and the numerical
local coordinate selected by the two Lemma 4.7 profile witnesses. -/
theorem noCollision_profile_coordinates_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Fin n) :
    ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1 ∧
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val :=
  (D.largeNoCollisionProfileWitness hlarge a).indexEquiv_coordinates_eq_of_componentRank_eq
      (D.smallNoCollisionProfileWitness hsmall b)
      (D.noCollision_componentRank_eq hsmall hlarge hselected) i

/-- The order of the larger good BONG at a global coordinate is the local
alternating value of the corresponding almost-Jordan component. -/
theorem largeNoCollision_order_eq_localOrder
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision) {n : Nat}
    (a : BONG.GoodBONG q M n) (i : Fin n) :
    a.order i = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1))
      (D.largeAlmostJordan.effectiveNormOrderAt
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1)))
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val := by
  let w := D.largeNoCollisionProfileWitness hlarge a
  change a.toBONG.order i = _
  rw [w.order_eq]
  exact D.largeAlmostJordan.jordanExpectedOrder_toJordan
    (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
    (w.indexEquiv i).1 (w.indexEquiv i).2

/-- The analogous local-order formula on the smaller side. -/
theorem smallNoCollision_order_eq_localOrder
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision) {n : Nat}
    (b : BONG.GoodBONG q N n) (i : Fin n) :
    b.order i = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1))
      (D.smallAlmostJordan.effectiveNormOrderAt
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1)))
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val := by
  let w := D.smallNoCollisionProfileWitness hsmall b
  change b.toBONG.order i = _
  rw [w.order_eq]
  exact D.smallAlmostJordan.jordanExpectedOrder_toJordan
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
    (w.indexEquiv i).1 (w.indexEquiv i).2

/-- At a coordinate belonging to the distinguished component, the larger
lattice order is directly bounded by the smaller lattice order.  In rank
two the odd coordinate uses the sharp two-step effective-norm bound. -/
theorem noCollision_selected_order_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Fin n)
    (hi : ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 =
      D.largeSelectedPosition) :
    a.order i ≤ b.order i := by
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b i
  have hy :
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1 =
        D.smallSelectedPosition := by
    calc
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1 =
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 :=
        hcoordinates.1.symm
      _ = D.largeSelectedPosition := hi
      _ = D.smallSelectedPosition := hselected.symm
  rw [D.largeNoCollision_order_eq_localOrder hlarge a i,
    D.smallNoCollision_order_eq_localOrder hsmall b i]
  simp only [hi, hy, D.largeAlmostJordan_scaleGenerator_selected,
    D.smallAlmostJordan_scaleGenerator_selected]
  rcases D.rank_one_or_two with hOne | hTwo
  · have hlargeEffective :=
      D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hOne
    have hsmallEffective :=
      D.smallSelected_effectiveNormOrder_eq_scale_of_rank_one hOne
    rw [hlargeEffective, hsmallEffective]
    simp only [JordanProfileOrder.localOrder_of_proper]
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hRankOne | hRankTwo
    · omega
    · omega
  · have hlargeLe := D.largeSelected_effectiveNormOrder_le_smallSelected
    have hsmallLe :=
      D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
        hTwo
    have hlargeScale :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
        D.largeSelectedPosition
        (ordUnit K D.input.block.enlargedScaleGenerator)
    have hsmallScale :=
      D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
        D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator)
    have hrank :
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 = 2 := by
      change finrank K (D.largeAlmostJordan.component
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1).carrier = 2
      rw [hi, D.largeAlmostJordan_finrank_selected, hTwo]
    have hjlt :
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val < 2 := by
      simpa only [hrank] using
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.isLt
    have hscale : ordUnit K D.input.block.enlargedScaleGenerator =
        ordUnit K D.input.block.scaleGenerator - 1 := by
      rcases D.input.block.componentRank_and_enlargedScaleOrder with
        hRankOne | hRankTwo
      · omega
      · exact hRankTwo.2
    interval_cases hlocal :
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val
    · have hsmallLocal :
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val = 0 := by
        omega
      simp only [hsmallLocal]
      rw [JordanProfileOrder.localOrder_even_of_scale_le hlargeScale (by simp),
        JordanProfileOrder.localOrder_even_of_scale_le hsmallScale (by simp)]
      exact hlargeLe
    · have hsmallLocal :
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val = 1 := by
        omega
      simp only [hsmallLocal]
      rw [JordanProfileOrder.localOrder_odd_of_scale_le hlargeScale (by simp),
        JordanProfileOrder.localOrder_odd_of_scale_le hsmallScale (by simp)]
      omega

/-- Before the distinguished component, a common block with a remaining
local successor supplies the direct/equal-pair coordinate certificate of
Section 5.4.  The only omitted case is the last odd coordinate of the block,
whose successor lies in the next component. -/
theorem noCollision_common_before_coordinate_of_local_succ_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore :
      D.smallCommonPosition c < D.smallSelectedPosition)
    (hlocalNext :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change (x.indexEquiv I).2.val + 1 <
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
      (x.indexEquiv I).1 at hlocalNext
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    have h := D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
      hsmallBefore
    simpa only [scale, D.smallAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_selected] using h
  have heffective : sourceEffective ≤ targetEffective := by
    exact D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt] at h
    rw [← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_le
    a.orderSequence b.orderSequence i hi localIndex scale
      sourceEffective targetEffective hsourceScale htargetScale heffective
      hsourceCurrent htargetCurrent
  intro hodd
  have hlocalPos : 0 < localIndex := by
    by_contra hnot
    have hzero : localIndex = 0 := Nat.eq_zero_of_not_pos hnot
    subst localIndex
    exact hodd ⟨0, by omega⟩
  have hi0 : 0 < i := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change i = _ at hindex
    omega
  have hiNext : i + 1 < n := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
    have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hnextBound :=
      (x.indexEquiv.symm
        ⟨(x.indexEquiv I).1,
          ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
    have hcurrentVal :
        (x.indexEquiv.symm (x.indexEquiv I)).val = i := by
      rw [hcurrent]
    have hval' :
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          simpa using hval
        _ = i + 1 := by rw [hcurrentVal]
    exact hval' ▸ hnextBound
  have hevenNext : Even (localIndex + 1) :=
    (Nat.even_add_one).2 hodd
  have hevenPrevious : Even (localIndex - 1) := by
    rcases (Nat.not_even_iff_odd.mp hodd) with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hsourceNext :
      a.orderSequence.entry (i + 1) hiNext = sourceEffective := by
    change a.order ⟨i + 1, hiNext⟩ = sourceEffective
    have h := x.order_succ_eq_jordanExpectedOrder_of_local_succ
      I hiNext hlocalNext
    rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    simp only [I] at h
    change a.order ⟨i + 1, hiNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsourceScale hevenNext] at h
    exact h
  have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    change 0 < localIndex
    exact hlocalPos
  have htargetPrevious :
      b.orderSequence.entry (i - 1) (by omega) = targetEffective := by
    change b.order ⟨i - 1, by omega⟩ = targetEffective
    have h := y.order_pred_eq_jordanExpectedOrder_of_local_pred
      I hsmallLocalPos
    rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
    rw [htargetScaleAt, htargetEffectiveAt] at h
    simp only [I] at h
    have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by
      omega
    change b.order ⟨i - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val - 1) at h
    rw [hprev, JordanProfileOrder.localOrder_even_of_scale_le
      htargetScale hevenPrevious] at h
    exact h
  exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- The aligned-position specialization of
`noCollision_common_before_coordinate_of_local_succ_of_alignment`. -/
theorem noCollision_common_before_coordinate_of_local_succ
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hlocalNext :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.noCollision_common_before_coordinate_of_local_succ_of_alignment
    hsmall hlarge a b i hi c hposition hbefore
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact hlocalNext

/-- The last odd coordinate of a common block before the distinguished
component.  If the effective norms are unequal, the selected larger-side
norm remains minimal through the next component scale, providing the
cross-component adjacent-pair equality from Section 5.4. -/
theorem noCollision_common_before_last_odd_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore :
      D.smallCommonPosition c < D.smallSelectedPosition)
    (hlast :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1)
    (hodd : ¬Even
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let p := D.largeCommonPosition c
  let pNext : Fin (D.complementComponentCount + 1) :=
    ⟨p.val + 1, by
      exact lt_of_le_of_lt (Nat.succ_le_of_lt hbefore)
        D.largeSelectedPosition.isLt⟩
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let nextScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)
  let sourceEffective :=
    D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = p at hposition
  change (x.indexEquiv I).2.val + 1 =
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
      (x.indexEquiv I).1 at hlast
  change ¬Even (x.indexEquiv I).2.val at hodd
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = p := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    have h := D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
      hsmallBefore
    simpa only [scale, D.smallAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_selected] using h
  have heffective : sourceEffective ≤ targetEffective := by
    exact D.large_effectiveNormOrderAt_le_small_of_target_lt
      p (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition]
    exact D.largeAlmostJordan_scaleGenerator_common c ▸ rfl
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  by_cases heq : sourceEffective = targetEffective
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent, heq]
  · have hlt : sourceEffective < targetEffective := lt_of_le_of_ne
      heffective heq
    apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_le
      a.orderSequence b.orderSequence i hi localIndex scale
        sourceEffective targetEffective hsourceScale htargetScale heffective
        hsourceCurrent htargetCurrent
    intro _
    have hlocalPos : 0 < localIndex := by
      by_contra hnot
      have hzero : localIndex = 0 := Nat.eq_zero_of_not_pos hnot
      subst localIndex
      exact hodd ⟨0, by omega⟩
    have hi0 : 0 < i := by
      have hindex := x.index_val_eq_componentStart_add_local I
      change i = _ at hindex
      omega
    have hpNextVal : pNext.val = p.val + 1 := rfl
    have hpNextLeSelected : pNext ≤ D.largeSelectedPosition := by
      change p.val + 1 ≤ D.largeSelectedPosition.val
      omega
    have hpLeNext : p ≤ pNext := by
      change p.val ≤ p.val + 1
      omega
    have hscaleNext : scale ≤ nextScale := by
      have hmono := D.largeAlmostJordan.scaleOrder_mono hpLeNext
      change scale ≤ nextScale
      simpa only [p, scale, nextScale,
        D.largeAlmostJordan_scaleGenerator_common] using hmono
    have hnextScaleSelected : nextScale ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
      have hmono := D.largeAlmostJordan.scaleOrder_mono hpNextLeSelected
      simpa only [nextScale,
        D.largeAlmostJordan_scaleGenerator_selected] using hmono
    have hsourceSelected : sourceEffective =
        ordUnit K (D.largeAlmostJordan.normGeneratorUnit
          D.largeSelectedPosition) := by
      exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
        p (D.smallCommonPosition c) p scale scale le_rfl
          (hscaleNext.trans hnextScaleSelected) hlt
    have hnextEffective :
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale =
          sourceEffective := by
      calc
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale =
            ordUnit K (D.largeAlmostJordan.normGeneratorUnit
              D.largeSelectedPosition) :=
          D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
            p (D.smallCommonPosition c) pNext scale nextScale hscaleNext
              hnextScaleSelected hlt
        _ = sourceEffective := hsourceSelected.symm
    have hnextRankPos : 0 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          pNext := by
      change 0 < finrank K (D.largeAlmostJordan.component pNext).carrier
      exact D.largeAlmostJordan.component_finrank_pos pNext
    have hiNext : i + 1 < n := by
      have hval := x.inverse_index_val_next_component
        (x.indexEquiv I).1 pNext (by rw [hposition])
          (x.indexEquiv I).2 hlast hnextRankPos
      have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
        x.indexEquiv.symm_apply_apply I
      have hbound := (x.indexEquiv.symm
        ⟨pNext, ⟨0, hnextRankPos⟩⟩).isLt
      have hval' :
          (x.indexEquiv.symm ⟨pNext, ⟨0, hnextRankPos⟩⟩).val = i + 1 := by
        calc
          _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
            simpa using hval
          _ = i + 1 := by rw [hcurrent]
      exact hval' ▸ hbound
    have hnextScaleLower : nextScale ≤
        D.largeAlmostJordan.effectiveNormOrderAt pNext nextScale :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt pNext nextScale
    have hsourceNext :
        a.orderSequence.entry (i + 1) hiNext = sourceEffective := by
      change a.toBONG.order ⟨i + 1, hiNext⟩ = sourceEffective
      have h := x.order_succ_eq_jordanExpectedOrder_of_next_component
        I hiNext pNext (by rw [hposition]) hlast hnextRankPos
      rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
      rw [hnextEffective] at h hnextScaleLower
      rw [JordanProfileOrder.localOrder_even_of_scale_le hnextScaleLower
        (by simp)] at h
      simpa only [I] using h
    have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
      rw [← hcoordinates.2]
      exact hlocalPos
    have hevenPrevious : Even (localIndex - 1) := by
      rcases (Nat.not_even_iff_odd.mp hodd) with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have htargetPrevious :
        b.orderSequence.entry (i - 1) (by omega) = targetEffective := by
      change b.order ⟨i - 1, by omega⟩ = targetEffective
      have h := y.order_pred_eq_jordanExpectedOrder_of_local_pred
        I hsmallLocalPos
      rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
      rw [htargetScaleAt, htargetEffectiveAt] at h
      simp only [I] at h
      have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by
        omega
      change b.order ⟨i - 1, by omega⟩ =
        JordanProfileOrder.localOrder scale targetEffective
          ((y.indexEquiv I).2.val - 1) at h
      rw [hprev, JordanProfileOrder.localOrder_even_of_scale_le
        htargetScale hevenPrevious] at h
      exact h
    exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- The aligned-position specialization of
`noCollision_common_before_last_odd_coordinate_of_alignment`. -/
theorem noCollision_common_before_last_odd_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hlast :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1)
    (hodd : ¬Even
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.noCollision_common_before_last_odd_coordinate_of_alignment
    hsmall hlarge a b i hi c hposition hbefore
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact hlast
  · exact hodd

/-- After the distinguished component, an interior even coordinate of a
common block is certified by the two adjacent odd coordinates.  This is the
right-hand counterpart of `noCollision_common_before_coordinate_of_local_succ`;
the effective-norm inequality is reversed. -/
theorem noCollision_common_after_coordinate_of_local_neighbors_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallAfter :
      D.smallSelectedPosition < D.smallCommonPosition c)
    (hlocalPos : 0 <
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val)
    (hlocalNext :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change 0 < (x.indexEquiv I).2.val at hlocalPos
  change (x.indexEquiv I).2.val + 1 <
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
      (x.indexEquiv I).1 at hlocalNext
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    have h := D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge hafter
    simpa only [scale, D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using h
  have heffective : targetEffective ≤ sourceEffective := by
    exact D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      (D.smallCommonPosition c) (D.largeCommonPosition c) scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_ge
    a.orderSequence b.orderSequence i hi localIndex scale
      sourceEffective targetEffective hsourceScale htargetScale heffective
      hsourceCurrent htargetCurrent
  intro heven
  have hi0 : 0 < i := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change i = _ at hindex
    change 0 < localIndex at hlocalPos
    omega
  have hiNext : i + 1 < n := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
    have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hnextBound :=
      (x.indexEquiv.symm
        ⟨(x.indexEquiv I).1,
          ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
    have hval' :
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
      calc
        _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          simpa using hval
        _ = i + 1 := by rw [hcurrent]
    exact hval' ▸ hnextBound
  have hoddNext : ¬Even (localIndex + 1) := by
    intro h
    exact (Nat.even_add_one.mp h) heven
  have hoddPrevious : ¬Even (localIndex - 1) := by
    rcases heven with ⟨k, hk⟩
    intro h
    rcases h with ⟨l, hl⟩
    change 0 < localIndex at hlocalPos
    omega
  have hsourceNext :
      a.orderSequence.entry (i + 1) hiNext =
        2 * scale - sourceEffective := by
    change a.order ⟨i + 1, hiNext⟩ = _
    have h := x.order_succ_eq_jordanExpectedOrder_of_local_succ
      I hiNext hlocalNext
    rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    simp only [I] at h
    change a.order ⟨i + 1, hiNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_odd_of_scale_le
      hsourceScale hoddNext] at h
    exact h
  have hsmallLocalPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    exact hlocalPos
  have htargetPrevious :
      b.orderSequence.entry (i - 1) (by omega) =
        2 * scale - targetEffective := by
    change b.order ⟨i - 1, by omega⟩ = _
    have h := y.order_pred_eq_jordanExpectedOrder_of_local_pred
      I hsmallLocalPos
    rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
    rw [htargetScaleAt, htargetEffectiveAt] at h
    simp only [I] at h
    have hprev : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by
      omega
    change b.order ⟨i - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val - 1) at h
    rw [hprev, JordanProfileOrder.localOrder_odd_of_scale_le
      htargetScale hoddPrevious] at h
    exact h
  exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- The aligned-position specialization of
`noCollision_common_after_coordinate_of_local_neighbors_of_alignment`. -/
theorem noCollision_common_after_coordinate_of_local_neighbors
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hlocalPos : 0 <
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val)
    (hlocalNext :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.noCollision_common_after_coordinate_of_local_neighbors_of_alignment
    hsmall hlarge a b i hi c hposition hafter
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hafter
  · exact hlocalPos
  · exact hlocalNext

/-- The first coordinate of a common block after the distinguished block.
When the effective norms are strict, O'Meara's improper-even-rank property
provides the source successor, while the selected smaller-side contribution
propagates to the preceding component and identifies its last coordinate. -/
theorem noCollision_common_after_first_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallAfter :
      D.smallSelectedPosition < D.smallCommonPosition c)
    (hfirst :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val = 0) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let pLarge := D.largeCommonPosition c
  let pSmall := D.smallCommonPosition c
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt pLarge scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt pSmall scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = pLarge at hposition
  change (x.indexEquiv I).2.val = 0 at hfirst
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hpEq : pLarge = pSmall := by
    simpa only [pLarge, pSmall] using hcommonPositions.symm
  have hsmallPosition : (y.indexEquiv I).1 = pSmall := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = pLarge := hposition
      _ = pSmall := hpEq
  have hsmallFirst : (y.indexEquiv I).2.val = 0 := by
    omega
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    have h := D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge hafter
    simpa only [scale, D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using h
  have hsmallSelectedScaleLt :
      ordUnit K D.input.block.scaleGenerator < scale := by
    have h := D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
      hsmallAfter
    simpa only [pSmall, scale,
      D.smallAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_common] using h
  have heffective : targetEffective ≤ sourceEffective := by
    exact D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      pSmall pLarge scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt pLarge scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt pSmall scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition]
    simp only [pLarge, scale, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition]
    simp only [pSmall, scale, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  by_cases heq : sourceEffective = targetEffective
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent, heq]
  · have hlt : targetEffective < sourceEffective :=
      lt_of_le_of_ne heffective (Ne.symm heq)
    apply Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_ge
      a.orderSequence b.orderSequence i hi localIndex scale
        sourceEffective targetEffective hsourceScale htargetScale heffective
        hsourceCurrent htargetCurrent
    intro _
    have hsourceStrict : scale < sourceEffective :=
      htargetScale.trans_lt hlt
    have hrankEven := D.largeCommon_componentRank_even_of_scale_lt_effective
      c (by simpa only [pLarge, scale, sourceEffective] using hsourceStrict)
    have hcurrentRankPos : 0 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1 := by
      change 0 < finrank K (D.largeAlmostJordan.component
        (x.indexEquiv I).1).carrier
      exact D.largeAlmostJordan.component_finrank_pos (x.indexEquiv I).1
    have hlocalNext : (x.indexEquiv I).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1 := by
      change (x.indexEquiv I).2.val + 1 < finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
      rw [hfirst, hposition]
      have hrankEven' : Even (finrank K
          (D.largeAlmostJordan.component pLarge).carrier) := by
        simpa only [pLarge] using hrankEven
      rcases hrankEven' with ⟨k, hk⟩
      have hpos := D.largeAlmostJordan.component_finrank_pos pLarge
      omega
    have hiNext : i + 1 < n := by
      have hval := x.inverse_index_val_local_succ
        (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalNext
      have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
        x.indexEquiv.symm_apply_apply I
      have hnextBound :=
        (x.indexEquiv.symm
          ⟨(x.indexEquiv I).1,
            ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).isLt
      have hval' :
          (x.indexEquiv.symm
            ⟨(x.indexEquiv I).1,
              ⟨(x.indexEquiv I).2.val + 1, hlocalNext⟩⟩).val = i + 1 := by
        calc
          _ = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
            simpa using hval
          _ = i + 1 := by rw [hcurrent]
      exact hval' ▸ hnextBound
    have hsourceNext :
        a.orderSequence.entry (i + 1) hiNext =
          2 * scale - sourceEffective := by
      change a.order ⟨i + 1, hiNext⟩ = _
      have h := x.order_succ_eq_jordanExpectedOrder_of_local_succ
        I hiNext hlocalNext
      rw [D.largeNoCollisionJordan_expectedOrder hlarge] at h
      rw [hsourceScaleAt, hsourceEffectiveAt] at h
      simp only [I] at h
      change a.order ⟨i + 1, hiNext⟩ =
        JordanProfileOrder.localOrder scale sourceEffective
          (localIndex + 1) at h
      have hodd : ¬Even (localIndex + 1) := by
        rw [show localIndex = 0 by exact hfirst]
        simp
      rw [JordanProfileOrder.localOrder_odd_of_scale_le
        hsourceScale hodd] at h
      exact h
    have hpSmallPos : 0 < pSmall.val := by
      have := hsmallAfter
      omega
    let pPrev : Fin (D.complementComponentCount + 1) :=
      ⟨pSmall.val - 1, by
        have := pSmall.isLt
        omega⟩
    have hpPrevNext : pSmall.val = pPrev.val + 1 := by
      simp only [pPrev]
      omega
    have hpSelectedPrev : D.smallSelectedPosition ≤ pPrev := by
      change D.smallSelectedPosition.val ≤ pSmall.val - 1
      omega
    have hpPrevCurrent : pPrev ≤ pSmall := by
      change pSmall.val - 1 ≤ pSmall.val
      omega
    let prevScale := ordUnit K (D.smallAlmostJordan.scaleGenerator pPrev)
    let prevEffective :=
      D.smallAlmostJordan.effectiveNormOrderAt pPrev prevScale
    have hselectedScalePrev :
        ordUnit K D.input.block.scaleGenerator ≤ prevScale := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono hpSelectedPrev
      simpa only [prevScale,
        D.smallAlmostJordan_scaleGenerator_selected] using hmono
    have hprevScaleCurrent : prevScale ≤ scale := by
      have hmono := D.smallAlmostJordan.scaleOrder_mono hpPrevCurrent
      simpa only [prevScale, pSmall, scale,
        D.smallAlmostJordan_scaleGenerator_common] using hmono
    have htargetSelectedAdjusted : targetEffective =
        JordanProfileOrder.adjustedAt
          D.smallAlmostJordan.scaleOrderFamily
          D.smallAlmostJordan.normOrderFamily scale
          D.smallSelectedPosition := by
      exact D.small_effectiveNormOrderAt_eq_selected_of_lt
        pSmall pLarge scale hlt
    have hprevSelectedAdjusted : prevEffective =
        JordanProfileOrder.adjustedAt
          D.smallAlmostJordan.scaleOrderFamily
          D.smallAlmostJordan.normOrderFamily prevScale
          D.smallSelectedPosition := by
      exact D.small_effectiveNormOrderAt_eq_selectedAdjusted_of_lt
        pSmall pLarge pPrev prevScale scale hselectedScalePrev
          hprevScaleCurrent hlt
    have hcomplementary : 2 * prevScale - prevEffective =
        2 * scale - targetEffective := by
      rw [hprevSelectedAdjusted, htargetSelectedAdjusted]
      simp only [JordanProfileOrder.adjustedAt,
        WeakJordanDecomposition.scaleOrderFamily,
        WeakJordanDecomposition.normOrderFamily,
        D.smallAlmostJordan_scaleGenerator_selected]
      rw [if_pos hsmallSelectedScaleLt]
      by_cases hprevLt :
          ordUnit K D.input.block.scaleGenerator < prevScale
      · rw [if_pos hprevLt]
        omega
      · rw [if_neg hprevLt]
        omega
    have hprevRankPos : 0 <
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank
          pPrev := by
      change 0 < finrank K (D.smallAlmostJordan.component pPrev).carrier
      exact D.smallAlmostJordan.component_finrank_pos pPrev
    have hcurrentSmallRankPos : 0 <
        (D.smallNoCollisionJordan hsmall).toOrthogonalDecomposition.componentRank
          (y.indexEquiv I).1 := by
      change 0 < finrank K (D.smallAlmostJordan.component
        (y.indexEquiv I).1).carrier
      exact D.smallAlmostJordan.component_finrank_pos (y.indexEquiv I).1
    have hi0 : 0 < i := by
      exact y.index_val_pos_of_previous_component I pPrev
        (by rw [hsmallPosition]; exact hpPrevNext) hprevRankPos
    have htargetPrevious :
        b.orderSequence.entry (i - 1) (by omega) =
          2 * scale - targetEffective := by
      change b.toBONG.order ⟨i - 1, by omega⟩ = _
      have h := y.order_pred_eq_jordanExpectedOrder_of_previous_component
        I hi0 pPrev (by rw [hsmallPosition]; exact hpPrevNext)
          hsmallFirst hprevRankPos hcurrentSmallRankPos
      rw [D.smallNoCollisionJordan_expectedOrder hsmall] at h
      change b.toBONG.order ⟨i - 1, by omega⟩ =
        JordanProfileOrder.localOrder prevScale prevEffective
          (finrank K (D.smallAlmostJordan.component pPrev).carrier - 1) at h
      have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
        D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pPrev
      change JordanProfileOrder.localOrder prevScale prevEffective
          (finrank K (D.smallAlmostJordan.component pPrev).carrier - 1) =
        2 * prevScale - prevEffective at hlast
      rw [hlast, hcomplementary] at h
      exact h
    exact ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩

/-- The aligned-position specialization of
`noCollision_common_after_first_coordinate_of_alignment`. -/
theorem noCollision_common_after_first_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hfirst :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val = 0) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.noCollision_common_after_first_coordinate_of_alignment
    hsmall hlarge a b i hi c hposition hafter
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hafter
  · exact hfirst

/-- The last coordinate of a common block after the distinguished block is
always a direct comparison.  Odd last coordinates compare by reversing the
effective norms; an even last coordinate cannot be strict because O'Meara's
parity invariant would force the component rank to be even. -/
theorem noCollision_common_after_last_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hlast :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change (x.indexEquiv I).2.val + 1 =
    (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
      (x.indexEquiv I).1 at hlast
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleGt :
      ordUnit K D.input.block.enlargedScaleGenerator < scale := by
    have h := D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge hafter
    simpa only [scale, D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using h
  have heffective : targetEffective ≤ sourceEffective := by
    exact D.small_effectiveNormOrderAt_le_large_of_large_lt_target
      (D.smallCommonPosition c) (D.largeCommonPosition c) scale hscaleGt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.direct
  rw [hsourceCurrent, htargetCurrent]
  apply JordanProfileOrder.localOrder_le_of_effective_ge_at_last
    hsourceScale htargetScale heffective
  · intro hstrict
    have hparity := D.largeCommon_componentRank_even_of_scale_lt_effective
      c hstrict
    change Even (finrank K
      (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier)
    rw [hposition]
    exact hparity
  · exact hlast

/-- The aligned-position specialization of
`noCollision_common_after_last_coordinate_of_alignment`. -/
theorem noCollision_common_after_last_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c)
    (hlast :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  apply D.noCollision_common_after_last_coordinate_of_alignment
    hsmall hlarge a b i hi c hposition hafter
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    (D.commonPositions_eq_of_selectedPositions_eq hselected c)
    hlast

/-- Complete coordinate certificate for every common component after the
distinguished component in the aligned no-collision case. -/
theorem noCollision_common_after_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hafter : D.largeSelectedPosition < D.largeCommonPosition c) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let I : Fin n := ⟨i, hi⟩
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hfirst : (x.indexEquiv I).2.val = 0
  · exact D.noCollision_common_after_first_coordinate
      hsmall hlarge hselected a b i hi c hposition hafter hfirst
  · by_cases hnext : (x.indexEquiv I).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1
    · exact D.noCollision_common_after_coordinate_of_local_neighbors
        hsmall hlarge hselected a b i hi c hposition hafter
          (Nat.pos_of_ne_zero hfirst) hnext
    · have hlast : (x.indexEquiv I).2.val + 1 =
          (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
            (x.indexEquiv I).1 := by
        have hbound := (x.indexEquiv I).2.isLt
        omega
      exact D.noCollision_common_after_last_coordinate
        hsmall hlarge hselected a b i hi c hposition hafter hlast

/-- Before the distinguished component, every even local coordinate is a
direct comparison of the two effective norm orders. -/
theorem noCollision_common_before_even_coordinate_of_alignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (hcoordinates :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).1 ∧
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val =
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv ⟨i, hi⟩).2.val)
    (hcommonPositions :
      D.smallCommonPosition c = D.largeCommonPosition c)
    (hsmallBefore :
      D.smallCommonPosition c < D.smallSelectedPosition)
    (heven : Even
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  let y := D.smallNoCollisionProfileWitness hsmall b
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator c)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition c) scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (D.smallCommonPosition c) scale
  let localIndex := (x.indexEquiv I).2.val
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  change Even (x.indexEquiv I).2.val at heven
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallPosition : (y.indexEquiv I).1 = D.smallCommonPosition c := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ = D.largeCommonPosition c := hposition
      _ = D.smallCommonPosition c := hcommonPositions.symm
  have hscaleLt : scale < ordUnit K D.input.block.scaleGenerator := by
    have h := D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall
      hsmallBefore
    simpa only [scale, D.smallAlmostJordan_scaleGenerator_common,
      D.smallAlmostJordan_scaleGenerator_selected] using h
  have heffective : sourceEffective ≤ targetEffective := by
    exact D.large_effectiveNormOrderAt_le_small_of_target_lt
      (D.largeCommonPosition c) (D.smallCommonPosition c) scale hscaleLt
  have hsourceScale : scale ≤ sourceEffective := by
    exact D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.largeCommonPosition c) scale
  have htargetScale : scale ≤ targetEffective := by
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (D.smallCommonPosition c) scale
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := by
    rw [hposition, D.largeAlmostJordan_scaleGenerator_common]
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1 scale =
        sourceEffective := by
    rw [hposition]
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1 scale =
        targetEffective := by
    rw [hsmallPosition]
  have hsourceCurrent : a.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I = _
    have h := D.largeNoCollision_order_eq_localOrder hlarge a I
    change a.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
      (D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)))
      (x.indexEquiv I).2.val at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    exact h
  have htargetCurrent : b.orderSequence.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change b.order I = _
    have h := D.smallNoCollision_order_eq_localOrder hsmall b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)))
      (y.indexEquiv I).2.val at h
    rw [htargetScaleAt, htargetEffectiveAt, ← hcoordinates.2] at h
    exact h
  apply Beli2019IndexPOrderCoordinateCertificate.direct
  rw [hsourceCurrent, htargetCurrent,
    JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven,
    JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  exact heffective

/-- The aligned-position specialization of
`noCollision_common_before_even_coordinate_of_alignment`. -/
theorem noCollision_common_before_even_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition)
    (heven : Even
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).2.val) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  have hcommonPositions :=
    D.commonPositions_eq_of_selectedPositions_eq hselected c
  apply D.noCollision_common_before_even_coordinate_of_alignment
    hsmall hlarge a b i hi c hposition hbefore
    (D.noCollision_profile_coordinates_eq
      hsmall hlarge hselected a b ⟨i, hi⟩)
    hcommonPositions
  · rw [hcommonPositions, hselected]
    exact hbefore
  · exact heven

/-- Complete coordinate certificate for every common component before the
distinguished component in the aligned no-collision case. -/
theorem noCollision_common_before_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n)
    (c : Fin D.complementComponentCount)
    (hposition :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv ⟨i, hi⟩).1 =
        D.largeCommonPosition c)
    (hbefore : D.largeCommonPosition c < D.largeSelectedPosition) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let x := D.largeNoCollisionProfileWitness hlarge a
  let I : Fin n := ⟨i, hi⟩
  change (x.indexEquiv I).1 = D.largeCommonPosition c at hposition
  by_cases hnext : (x.indexEquiv I).2.val + 1 <
      (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
        (x.indexEquiv I).1
  · exact D.noCollision_common_before_coordinate_of_local_succ
      hsmall hlarge hselected a b i hi c hposition hbefore hnext
  · have hlast : (x.indexEquiv I).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).toOrthogonalDecomposition.componentRank
          (x.indexEquiv I).1 := by
      have hbound := (x.indexEquiv I).2.isLt
      omega
    by_cases heven : Even (x.indexEquiv I).2.val
    · exact D.noCollision_common_before_even_coordinate
        hsmall hlarge hselected a b i hi c hposition hbefore heven
    · exact D.noCollision_common_before_last_odd_coordinate
        hsmall hlarge hselected a b i hi c hposition hbefore hlast heven

/-- Every coordinate is certified when both sorted decompositions are
collision-free and their distinguished insertion positions agree. -/
theorem noCollision_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi := by
  let I : Fin n := ⟨i, hi⟩
  let x := D.largeNoCollisionProfileWitness hlarge a
  rcases D.largePosition_eq_selected_or_common (x.indexEquiv I).1 with
    hposition | ⟨c, hposition⟩
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    exact D.noCollision_selected_order_le hsmall hlarge hselected a b I hposition
  · rcases lt_or_gt_of_ne
        (D.largeSelectedPosition_ne_common c).symm with hbefore | hafter
    · exact D.noCollision_common_before_coordinate
        hsmall hlarge hselected a b i hi c hposition hbefore
    · exact D.noCollision_common_after_coordinate
        hsmall hlarge hselected a b i hi c hposition hafter

/-- The complete Section 5.4 order certificate in the aligned,
no-collision case. -/
theorem noCollision_orderCertificate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n) :
    Beli2019IndexPOrderCertificate a.orderSequence b.orderSequence where
  coordinate i hi :=
    D.noCollision_coordinate hsmall hlarge hselected a b i hi

end Lattice.Beli2019Lemma51Data

end Bong
