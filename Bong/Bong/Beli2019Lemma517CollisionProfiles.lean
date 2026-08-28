/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517Boundary
import Bong.Bong.Beli2009JordanProfileWeightUpper
import Bong.Bong.JordanProfileMergeResolution
import Bong.Lattice.JordanAmalgamationPrefixCarrier

/-!
# Strict resolutions of the weak profiles in Beli (2019), Lemma 5.17

The almost-Jordan families in Section 5 can have one adjacent equal-scale
pair.  This file resolves that pair and records the strict component seen
by a coordinate in the Lemma 5.17 range.  The construction is deliberately
coordinate-local: the two sides may have different strict component
counts.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V}

namespace BONG

/-- Component-count reindexing is definitionally invisible to prefix
carriers.  This belongs here rather than in the lattice layer because
`JordanDecomposition.castComponentCount` is introduced in the BONG
development. -/
private theorem castComponentCount_prefixCarrier
    {c d : Nat} (J : Lattice.JordanDecomposition q L c)
    (h : c = d) (cut : Nat) :
    (J.castComponentCount h).toOrthogonalDecomposition.prefixCarrier cut =
      J.toOrthogonalDecomposition.prefixCarrier cut := by
  subst d
  rfl

end BONG

namespace Lattice.WeakJordanDecomposition

/-- Reindex the number of components along a numerical equality.  The
construction is kept in the BONG layer because the corresponding Jordan
operation is introduced there. -/
noncomputable def castComponentCount
    {c d : Nat} (W : WeakJordanDecomposition q L c) (h : c = d) :
    WeakJordanDecomposition q L d := by
  subst d
  exact W

/-- Strictness transports through component-count reindexing. -/
theorem castComponentCount_scaleOrder_strict
    {c d : Nat} (W : WeakJordanDecomposition q L c) (h : c = d)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i))) :
    StrictMono (fun i ↦
      ordUnit K ((W.castComponentCount h).scaleGenerator i)) := by
  subst d
  exact hstrict

/-- O'Meara's improper-even-rank invariant transports through
component-count reindexing. -/
theorem HasImproperEvenRank.castComponentCount
    {c d : Nat} (W : WeakJordanDecomposition q L c)
    (hW : W.HasImproperEvenRank) (h : c = d) :
    (W.castComponentCount h).HasImproperEvenRank := by
  subst d
  exact hW

/-- Reindexing before or after choosing the Jordan norm generators gives
the same strict Jordan decomposition. -/
theorem castComponentCount_toJordan
    {c d : Nat} (W : WeakJordanDecomposition q L c) (h : c = d)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i))) :
    (W.castComponentCount h).toJordan
        (W.castComponentCount_scaleOrder_strict h hstrict) =
      (W.toJordan hstrict).castComponentCount h := by
  subst d
  rfl

end Lattice.WeakJordanDecomposition

namespace BONG

/-- A strict Jordan/profile resolution of one coordinate of a weak Jordan
profile, retaining the equality of its fundamental scale with the old weak
component scale. -/
structure StrictCoordinateResolution
    {n t : Nat} (b : BONG V q L n)
    (W : Lattice.WeakJordanDecomposition q L t)
    (x : WeakJordanOrderProfileWitness b W) (I : Fin n) where
  componentCount : Nat
  strictWeak : Lattice.WeakJordanDecomposition q L componentCount
  scaleOrder_strict : StrictMono
    (fun i ↦ ordUnit K (strictWeak.scaleGenerator i))
  hasImproperEvenRank : strictWeak.HasImproperEvenRank
  profile : JordanOrderProfileWitness b
    (strictWeak.toJordan scaleOrder_strict)
  /-- The number of old coordinates absorbed on the left when `I` belongs
  to the right member of the merged pair.  It is zero in every unchanged
  or left-member branch. -/
  localCoordinateOffset : Nat
  localCoordinate_eq :
    (profile.indexEquiv I).2.val =
      localCoordinateOffset + (x.indexEquiv I).2.val
  component_val_eq_of_offset_zero : localCoordinateOffset = 0 →
    (profile.indexEquiv I).1.val = (x.indexEquiv I).1.val
  prefixComponent_eq (j : Fin componentCount)
      (hj : j < (profile.indexEquiv I).1) :
    ∃ old : Fin t, old.val = j.val ∧
      strictWeak.component j = W.component old
  scaleOrder_eq :
    (strictWeak.toJordan scaleOrder_strict).fundamentalScaleOrder
        (profile.indexEquiv I).1 =
      ordUnit K (W.scaleGenerator (x.indexEquiv I).1)
  effectiveNormOrder_eq :
    BONG.jordanEffectiveNormOrderAt
        (strictWeak.toJordan scaleOrder_strict) (profile.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) =
      W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))

namespace StrictCoordinateResolution

/-- The strict Jordan decomposition carried by a coordinate resolution. -/
noncomputable abbrev jordan
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : WeakJordanOrderProfileWitness b W} {I : Fin n}
    (R : StrictCoordinateResolution b W x I) :
    Lattice.JordanDecomposition q L R.componentCount :=
  R.strictWeak.toJordan R.scaleOrder_strict

end StrictCoordinateResolution

/-- A resolution whose selected strict coordinate is internal. -/
structure InternalStrictCoordinateResolution
    {n t : Nat} (b : BONG V q L n)
    (W : Lattice.WeakJordanDecomposition q L t)
    (x : WeakJordanOrderProfileWitness b W) (I : Fin n)
    extends StrictCoordinateResolution b W x I where
  internal : (profile.indexEquiv I).2.val + 1 <
    finrank K (strictWeak.component (profile.indexEquiv I).1).carrier

/-- A strict Jordan boundary resolving a terminal coordinate of a weak
profile. -/
structure StrictBoundaryResolution
    {m t : Nat} (a : GoodBONG q L (m + 1))
    (W : Lattice.WeakJordanDecomposition q L t)
    (x : WeakJordanOrderProfileWitness a.toBONG W) (g : Fin m) where
  boundaryCount : Nat
  strictWeak : Lattice.WeakJordanDecomposition q L (boundaryCount + 1)
  scaleOrder_strict : StrictMono
    (fun i ↦ ordUnit K (strictWeak.scaleGenerator i))
  hasImproperEvenRank : strictWeak.HasImproperEvenRank
  jordan : Lattice.JordanDecomposition q L (boundaryCount + 1)
  jordan_eq : jordan = strictWeak.toJordan scaleOrder_strict
  profile : JordanOrderProfileWitness a.toBONG jordan
  boundary : Fin boundaryCount
  weakNext : Fin t
  weakNext_val : weakNext.val = (x.indexEquiv g.castSucc).1.val + 1
  boundaryIndex_eq : profile.boundaryIndex boundary = g
  /-- The strict prefix through the resolved left component is the original
  weak prefix through the terminal weak component. -/
  prefixCarrier_eq :
    jordan.toOrthogonalDecomposition.prefixCarrier (boundary.val + 1) =
      W.toOrthogonalDecomposition.prefixCarrier weakNext.val
  leftScaleOrder_eq :
    jordan.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex boundary) =
      ordUnit K (W.scaleGenerator (x.indexEquiv g.castSucc).1)
  rightScaleOrder_eq :
    jordan.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryRightIndex boundary) =
      ordUnit K (W.scaleGenerator weakNext)

end BONG

namespace Lattice.Beli2019Lemma51Data

/-- Resolve the small weak profile at every coordinate at or before its
selected component. -/
noncomputable def smallStrictCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (b : BONG.GoodBONG q N n) (I : Fin n)
    (hle : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition) :
    BONG.StrictCoordinateResolution b.toBONG D.smallAlmostJordan
      (D.smallWeakProfileWitness b) I := by
  classical
  let x := D.smallWeakProfileWitness b
  by_cases hcollision : D.SmallScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.smallCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.smallAlmostJordan k heq
          (D.smallOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness b.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (b.toBONG.beliLemma47_profile b.good (S.toJordan hstrict))
    have hlePair : (x.indexEquiv I).1 ≤ k.castSucc := by
      rw [hk.1]
      exact hle
    by_cases hbefore : (x.indexEquiv I).1 < k.castSucc
    · have hcoordinates := x.strict_coordinates_of_before
        D.smallAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
      let p := Classical.choose hcoordinates
      have hp := (Classical.choose_spec hcoordinates).1
      have hpOld := (Classical.choose_spec hcoordinates).2.1
      have hpCoordinate := (Classical.choose_spec hcoordinates).2.2.1
      have hpLocal := (Classical.choose_spec hcoordinates).2.2.2
      refine
        { componentCount := D.complementComponentCount
          strictWeak := S
          scaleOrder_strict := hstrict
          hasImproperEvenRank :=
            D.smallAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
              D.smallAlmostJordan k heq
          profile := P
          localCoordinateOffset := 0
          localCoordinate_eq := by simpa only [Nat.zero_add] using hpLocal
          component_val_eq_of_offset_zero := by
            intro _
            calc
              (P.indexEquiv I).1.val = p.val := congrArg Fin.val hpCoordinate
              _ = (x.indexEquiv I).1.val := congrArg Fin.val hpOld
          prefixComponent_eq := by
            intro j hj
            refine ⟨j.castSucc, rfl, ?_⟩
            apply D.smallAlmostJordan.mergeAdjacentAt_component_of_lt k heq
            rw [hpCoordinate] at hj
            exact hj.trans hp
          scaleOrder_eq := ?_
          effectiveNormOrder_eq := ?_ }
      · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hpCoordinate, Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
        have hskip : k.succ.succAbove p = p.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr hp.le
        rw [hskip, hpOld]
      · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hpCoordinate]
        exact D.smallAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq p (x.indexEquiv I).1 _
    · have hleft : (x.indexEquiv I).1 = k.castSucc :=
        le_antisymm hlePair (le_of_not_gt hbefore)
      have hcoordinates := x.strict_coordinates_of_left
        D.smallAlmostJordan_hasImproperEvenRank k heq hstrict P I hleft
      refine
        { componentCount := D.complementComponentCount
          strictWeak := S
          scaleOrder_strict := hstrict
          hasImproperEvenRank :=
            D.smallAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
              D.smallAlmostJordan k heq
          profile := P
          localCoordinateOffset := 0
          localCoordinate_eq := by
            simpa only [Nat.zero_add] using hcoordinates.2
          component_val_eq_of_offset_zero := by
            intro _
            calc
              (P.indexEquiv I).1.val = k.val :=
                congrArg Fin.val hcoordinates.1
              _ = (x.indexEquiv I).1.val :=
                (congrArg Fin.val hleft).symm
          prefixComponent_eq := by
            intro j hj
            refine ⟨j.castSucc, rfl, ?_⟩
            apply D.smallAlmostJordan.mergeAdjacentAt_component_of_lt k heq
            rw [hcoordinates.1] at hj
            exact hj
          scaleOrder_eq := ?_
          effectiveNormOrder_eq := ?_ }
      · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hcoordinates.1,
          Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
        have hskip : k.succ.succAbove k = k.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
        rw [hskip, hleft]
      · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hcoordinates.1]
        exact D.smallAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq k (x.indexEquiv I).1 _
  · let hstrict := D.smallAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.smallNoCollisionProfileWitness hcollision b
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    refine
      { componentCount := D.complementComponentCount + 1
        strictWeak := D.smallAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.smallAlmostJordan_hasImproperEvenRank
        profile := P
        localCoordinateOffset := 0
        localCoordinate_eq := by
          simpa only [Nat.zero_add] using
            (congrArg (fun z ↦ z.2.val) hcoordinates).symm
        component_val_eq_of_offset_zero := by
          intro _
          exact congrArg Fin.val (congrArg Sigma.fst hcoordinates).symm
        prefixComponent_eq := by
          intro j _hj
          exact ⟨j, rfl, rfl⟩
        scaleOrder_eq := ?_
        effectiveNormOrder_eq := ?_ }
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
      exact congrArg (fun p ↦ ordUnit K
        (D.smallAlmostJordan.scaleGenerator p))
          (congrArg Sigma.fst hcoordinates).symm
    · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan]
      exact D.smallAlmostJordan.effectiveNormOrderAt_anchor_irrel
        (P.indexEquiv I).1 (x.indexEquiv I).1 _

/-- Resolve the large weak profile at every coordinate at or before its
selected component. -/
noncomputable def largeStrictCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition) :
    BONG.StrictCoordinateResolution a.toBONG D.largeAlmostJordan
      (D.largeWeakProfileWitness a) I := by
  classical
  let x := D.largeWeakProfileWitness a
  by_cases hcollision : D.LargeScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hlePair : (x.indexEquiv I).1 ≤ k.succ := by
      rw [hk.2]
      exact hle
    by_cases hbefore : (x.indexEquiv I).1 < k.castSucc
    · have hcoordinates := x.strict_coordinates_of_before
        D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
      let p := Classical.choose hcoordinates
      have hp := (Classical.choose_spec hcoordinates).1
      have hpOld := (Classical.choose_spec hcoordinates).2.1
      have hpCoordinate := (Classical.choose_spec hcoordinates).2.2.1
      have hpLocal := (Classical.choose_spec hcoordinates).2.2.2
      refine
        { componentCount := D.complementComponentCount
          strictWeak := S
          scaleOrder_strict := hstrict
          hasImproperEvenRank :=
            D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
              D.largeAlmostJordan k heq
          profile := P
          localCoordinateOffset := 0
          localCoordinate_eq := by simpa only [Nat.zero_add] using hpLocal
          component_val_eq_of_offset_zero := by
            intro _
            calc
              (P.indexEquiv I).1.val = p.val := congrArg Fin.val hpCoordinate
              _ = (x.indexEquiv I).1.val := congrArg Fin.val hpOld
          prefixComponent_eq := by
            intro j hj
            refine ⟨j.castSucc, rfl, ?_⟩
            apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
            rw [hpCoordinate] at hj
            exact hj.trans hp
          scaleOrder_eq := ?_
          effectiveNormOrder_eq := ?_ }
      · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hpCoordinate, Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
        have hskip : k.succ.succAbove p = p.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr hp.le
        rw [hskip, hpOld]
      · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hpCoordinate]
        exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq p (x.indexEquiv I).1 _
    · by_cases hleft : (x.indexEquiv I).1 = k.castSucc
      · have hcoordinates := x.strict_coordinates_of_left
          D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hleft
        refine
          { componentCount := D.complementComponentCount
            strictWeak := S
            scaleOrder_strict := hstrict
            hasImproperEvenRank :=
              D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan k heq
            profile := P
            localCoordinateOffset := 0
            localCoordinate_eq := by
              simpa only [Nat.zero_add] using hcoordinates.2
            component_val_eq_of_offset_zero := by
              intro _
              calc
                (P.indexEquiv I).1.val = k.val :=
                  congrArg Fin.val hcoordinates.1
                _ = (x.indexEquiv I).1.val :=
                  (congrArg Fin.val hleft).symm
            prefixComponent_eq := by
              intro j hj
              refine ⟨j.castSucc, rfl, ?_⟩
              apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
              rw [hcoordinates.1] at hj
              exact hj
            scaleOrder_eq := ?_
            effectiveNormOrder_eq := ?_ }
        · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
          rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            hcoordinates.1,
            Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
          have hskip : k.succ.succAbove k = k.castSucc := by
            rw [Fin.succAbove_of_castSucc_lt]
            exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
          rw [hskip, hleft]
        · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
            hcoordinates.1]
          exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
            k heq k (x.indexEquiv I).1 _
      · have hright : (x.indexEquiv I).1 = k.succ := by
          apply Fin.ext
          change (x.indexEquiv I).1.val = k.val + 1
          change ¬(x.indexEquiv I).1.val < k.val at hbefore
          have hneVal : (x.indexEquiv I).1.val ≠ k.val := by
            intro hval
            apply hleft
            apply Fin.ext
            exact hval
          change (x.indexEquiv I).1.val ≤ k.val + 1 at hlePair
          omega
        have hcoordinates := x.strict_coordinates_of_right
          D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
        refine
          { componentCount := D.complementComponentCount
            strictWeak := S
            scaleOrder_strict := hstrict
            hasImproperEvenRank :=
              D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan k heq
            profile := P
            localCoordinateOffset :=
              finrank K (D.largeAlmostJordan.component k.castSucc).carrier
            localCoordinate_eq := hcoordinates.2
            component_val_eq_of_offset_zero := by
              intro hoffset
              have hpos :=
                D.largeAlmostJordan.component_finrank_pos k.castSucc
              omega
            prefixComponent_eq := by
              intro j hj
              refine ⟨j.castSucc, rfl, ?_⟩
              apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
              rw [hcoordinates.1] at hj
              exact hj
            scaleOrder_eq := ?_
            effectiveNormOrder_eq := ?_ }
        · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
          rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            hcoordinates.1,
            Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
          have hskip : k.succ.succAbove k = k.castSucc := by
            rw [Fin.succAbove_of_castSucc_lt]
            exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
          rw [hskip, hright]
          exact heq
        · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
            hcoordinates.1]
          exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
            k heq k (x.indexEquiv I).1 _
  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    refine
      { componentCount := D.complementComponentCount + 1
        strictWeak := D.largeAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.largeAlmostJordan_hasImproperEvenRank
        profile := P
        localCoordinateOffset := 0
        localCoordinate_eq := by
          simpa only [Nat.zero_add] using
            (congrArg (fun z ↦ z.2.val) hcoordinates).symm
        component_val_eq_of_offset_zero := by
          intro _
          exact congrArg Fin.val (congrArg Sigma.fst hcoordinates).symm
        prefixComponent_eq := by
          intro j _hj
          exact ⟨j, rfl, rfl⟩
        scaleOrder_eq := ?_
        effectiveNormOrder_eq := ?_ }
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
      exact congrArg (fun p ↦ ordUnit K
        (D.largeAlmostJordan.scaleGenerator p))
          (congrArg Sigma.fst hcoordinates).symm
    · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan]
      exact D.largeAlmostJordan.effectiveNormOrderAt_anchor_irrel
        (P.indexEquiv I).1 (x.indexEquiv I).1 _

/-- If a weak large-side coordinate is already internal, or is the last
coordinate of the common block which collides with the selected block, it
becomes an internal coordinate in a strict resolution. -/
theorem nonempty_largeInternalStrictCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition)
    (hinternal :
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val + 1 <
          finrank K (D.largeAlmostJordan.component
            ((D.largeWeakProfileWitness a).indexEquiv I).1).carrier ∨
        ∃ c : Fin D.complementComponentCount,
          ordUnit K (D.complementStrictWeak.scaleGenerator c) =
              ordUnit K D.input.block.enlargedScaleGenerator ∧
            ((D.largeWeakProfileWitness a).indexEquiv I).1 =
              D.largeCommonPosition c) :
    Nonempty (BONG.InternalStrictCoordinateResolution a.toBONG
      D.largeAlmostJordan (D.largeWeakProfileWitness a) I) := by
  classical
  let x := D.largeWeakProfileWitness a
  by_cases hcollision : D.LargeScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hlePair : (x.indexEquiv I).1 ≤ k.succ := by
      rw [hk.2]
      exact hle
    have hweakInternal_of_not_left
        (hnotLeft : (x.indexEquiv I).1 ≠ k.castSucc) :
        (x.indexEquiv I).2.val + 1 <
          finrank K (D.largeAlmostJordan.component
            (x.indexEquiv I).1).carrier := by
      rcases hinternal with hweak | ⟨c', hscale', hpCommon⟩
      · exact hweak
      · have hc : c' = c :=
          D.complementStrictWeak_scaleOrder_strict.injective
            (hscale'.trans hscale.symm)
        subst c'
        exfalso
        apply hnotLeft
        exact hpCommon.trans hk.1.symm
    by_cases hbefore : (x.indexEquiv I).1 < k.castSucc
    · have hweakInternal := hweakInternal_of_not_left (ne_of_lt hbefore)
      have hcoordinates := x.strict_coordinates_of_before
        D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
      rcases hcoordinates with ⟨p, hp, hpOld, hpCoordinate, hlocal⟩
      have hskip : k.succ.succAbove p = p.castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        exact Fin.castSucc_lt_succ_iff.mpr hp.le
      have hrank :
          (S.toJordan hstrict).componentRank (P.indexEquiv I).1 =
            finrank K (D.largeAlmostJordan.component
              (x.indexEquiv I).1).carrier := by
        change finrank K (S.component (P.indexEquiv I).1).carrier = _
        rw [hpCoordinate,
          D.largeAlmostJordan.mergeAdjacentAt_component_of_ne
            k heq p (Fin.ne_of_lt hp), hskip, hpOld]
      refine ⟨
        { componentCount := D.complementComponentCount
          strictWeak := S
          scaleOrder_strict := hstrict
          hasImproperEvenRank :=
            D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
              D.largeAlmostJordan k heq
          profile := P
          localCoordinateOffset := 0
          localCoordinate_eq := by simpa only [Nat.zero_add] using hlocal
          component_val_eq_of_offset_zero := by
            intro _
            calc
              (P.indexEquiv I).1.val = p.val := congrArg Fin.val hpCoordinate
              _ = (x.indexEquiv I).1.val := congrArg Fin.val hpOld
          prefixComponent_eq := by
            intro j hj
            refine ⟨j.castSucc, rfl, ?_⟩
            apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
            rw [hpCoordinate] at hj
            exact hj.trans hp
          scaleOrder_eq := ?_
          effectiveNormOrder_eq := ?_
          internal := ?_ }⟩
      · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hpCoordinate,
          Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator,
          hskip, hpOld]
      · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hpCoordinate]
        exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq p (x.indexEquiv I).1 _
      · change (P.indexEquiv I).2.val + 1 <
          (S.toJordan hstrict).componentRank (P.indexEquiv I).1
        rw [hrank, hlocal]
        exact hweakInternal
    · by_cases hleft : (x.indexEquiv I).1 = k.castSucc
      · have hcoordinates := x.strict_coordinates_of_left
          D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hleft
        have hrightRankPos : 0 <
            finrank K (D.largeAlmostJordan.component k.succ).carrier :=
          D.largeAlmostJordan.component_finrank_pos k.succ
        refine ⟨
          { componentCount := D.complementComponentCount
            strictWeak := S
            scaleOrder_strict := hstrict
            hasImproperEvenRank :=
              D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan k heq
            profile := P
            localCoordinateOffset := 0
            localCoordinate_eq := by
              simpa only [Nat.zero_add] using hcoordinates.2
            component_val_eq_of_offset_zero := by
              intro _
              calc
                (P.indexEquiv I).1.val = k.val :=
                  congrArg Fin.val hcoordinates.1
                _ = (x.indexEquiv I).1.val :=
                  (congrArg Fin.val hleft).symm
            prefixComponent_eq := by
              intro j hj
              refine ⟨j.castSucc, rfl, ?_⟩
              apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
              rw [hcoordinates.1] at hj
              exact hj
            scaleOrder_eq := ?_
            effectiveNormOrder_eq := ?_
            internal := ?_ }⟩
        · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
          rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            hcoordinates.1,
            Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
          have hskip : k.succ.succAbove k = k.castSucc := by
            rw [Fin.succAbove_of_castSucc_lt]
            exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
          rw [hskip, hleft]
        · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
            hcoordinates.1]
          exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
            k heq k (x.indexEquiv I).1 _
        · change (P.indexEquiv I).2.val + 1 <
            finrank K (S.component (P.indexEquiv I).1).carrier
          have hrankMerged :
              finrank K (S.component (P.indexEquiv I).1).carrier =
                finrank K
                    (D.largeAlmostJordan.component k.castSucc).carrier +
                  finrank K
                    (D.largeAlmostJordan.component k.succ).carrier := by
            rw [hcoordinates.1]
            exact D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq
          have hlocal := (x.indexEquiv I).2.isLt
          have hweakRankEq := congrArg
            (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier)
              hleft
          omega
      · have hright : (x.indexEquiv I).1 = k.succ := by
          apply Fin.ext
          change (x.indexEquiv I).1.val = k.val + 1
          change ¬(x.indexEquiv I).1.val < k.val at hbefore
          have hneVal : (x.indexEquiv I).1.val ≠ k.val := by
            intro hval
            apply hleft
            apply Fin.ext
            exact hval
          change (x.indexEquiv I).1.val ≤ k.val + 1 at hlePair
          omega
        have hweakInternal := hweakInternal_of_not_left (by
          rw [hright]
          exact Fin.ne_of_gt k.castSucc_lt_succ)
        have hcoordinates := x.strict_coordinates_of_right
          D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
        refine ⟨
          { componentCount := D.complementComponentCount
            strictWeak := S
            scaleOrder_strict := hstrict
            hasImproperEvenRank :=
              D.largeAlmostJordan_hasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan k heq
            profile := P
            localCoordinateOffset :=
              finrank K (D.largeAlmostJordan.component k.castSucc).carrier
            localCoordinate_eq := hcoordinates.2
            component_val_eq_of_offset_zero := by
              intro hoffset
              have hpos :=
                D.largeAlmostJordan.component_finrank_pos k.castSucc
              omega
            prefixComponent_eq := by
              intro j hj
              refine ⟨j.castSucc, rfl, ?_⟩
              apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
              rw [hcoordinates.1] at hj
              exact hj
            scaleOrder_eq := ?_
            effectiveNormOrder_eq := ?_
            internal := ?_ }⟩
        · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
          rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
            hcoordinates.1,
            Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
          have hskip : k.succ.succAbove k = k.castSucc := by
            rw [Fin.succAbove_of_castSucc_lt]
            exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
          rw [hskip, hright]
          exact heq
        · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
            hcoordinates.1]
          exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
            k heq k (x.indexEquiv I).1 _
        · change (P.indexEquiv I).2.val + 1 <
            finrank K (S.component (P.indexEquiv I).1).carrier
          have hrankMerged :
              finrank K (S.component (P.indexEquiv I).1).carrier =
                finrank K
                    (D.largeAlmostJordan.component k.castSucc).carrier +
                  finrank K
                    (D.largeAlmostJordan.component k.succ).carrier := by
            rw [hcoordinates.1]
            exact D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq
          have hweakRankEq := congrArg
            (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier)
              hright
          omega
  · have hweakInternal :
        (D.largeWeakProfileWitness a).indexEquiv I |>.2.val + 1 <
          finrank K (D.largeAlmostJordan.component
            ((D.largeWeakProfileWitness a).indexEquiv I).1).carrier := by
      rcases hinternal with hweak | ⟨c, hscale, _⟩
      · exact hweak
      · exact False.elim (hcollision ⟨c, hscale⟩)
    let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    refine ⟨
      { componentCount := D.complementComponentCount + 1
        strictWeak := D.largeAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.largeAlmostJordan_hasImproperEvenRank
        profile := P
        localCoordinateOffset := 0
        localCoordinate_eq := by
          simpa only [Nat.zero_add] using
            (congrArg (fun z ↦ z.2.val) hcoordinates).symm
        component_val_eq_of_offset_zero := by
          intro _
          exact congrArg Fin.val (congrArg Sigma.fst hcoordinates).symm
        prefixComponent_eq := by
          intro j _hj
          exact ⟨j, rfl, rfl⟩
        scaleOrder_eq := ?_
        effectiveNormOrder_eq := ?_
        internal := ?_ }⟩
    · unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
      exact congrArg (fun p ↦ ordUnit K
        (D.largeAlmostJordan.scaleGenerator p))
          (congrArg Sigma.fst hcoordinates).symm
    · rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan]
      exact D.largeAlmostJordan.effectiveNormOrderAt_anchor_irrel
        (P.indexEquiv I).1 (x.indexEquiv I).1 _
    · have hcomponent := congrArg Sigma.fst hcoordinates
      have hlocal := congrArg (fun z ↦ z.2.val) hcoordinates
      change (x.indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv I).1).carrier at hweakInternal
      change (P.indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          (P.indexEquiv I).1).carrier
      have hrankEq := congrArg
        (fun p ↦ finrank K (D.largeAlmostJordan.component p).carrier)
          hcomponent
      omega

set_option maxHeartbeats 0 in
/-- Resolve a terminal small-side coordinate strictly before the selected
component to a strict Jordan boundary. -/
theorem nonempty_smallStrictBoundaryResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {m : Nat} (b : BONG.GoodBONG q N (m + 1)) (g : Fin m)
    (hbefore : ((D.smallWeakProfileWitness b).indexEquiv g.castSucc).1 <
      D.smallSelectedPosition)
    (hlast : ((D.smallWeakProfileWitness b).indexEquiv g.castSucc).2.val + 1 =
      finrank K (D.smallAlmostJordan.component
        ((D.smallWeakProfileWitness b).indexEquiv g.castSucc).1).carrier) :
    Nonempty (BONG.StrictBoundaryResolution b D.smallAlmostJordan
      (D.smallWeakProfileWitness b) g) := by
  classical
  let x := D.smallWeakProfileWitness b
  let weakNext : Fin (D.complementComponentCount + 1) :=
    ⟨(x.indexEquiv g.castSucc).1.val + 1, by
      have hs := D.smallSelectedPosition.isLt
      change (x.indexEquiv g.castSucc).1.val <
        D.smallSelectedPosition.val at hbefore
      omega⟩
  by_cases hcollision : D.SmallScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.smallCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.smallAlmostJordan k heq
          (D.smallOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness b.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (b.toBONG.beliLemma47_profile b.good (S.toJordan hstrict))
    have hbeforePair : (x.indexEquiv g.castSucc).1 < k.castSucc := by
      rw [hk.1]
      exact hbefore
    have hresolution := x.exists_boundary_resolution_ofMerge_before
      D.smallAlmostJordan_hasImproperEvenRank k heq hstrict P g
      hbeforePair hlast
    rcases hresolution with ⟨s, hcount, hresolution⟩
    dsimp only at hresolution
    rcases hresolution with ⟨z, hz, hzval, hleft, hright⟩
    let J := (S.toJordan hstrict).castComponentCount hcount
    let P' := P.castComponentCount hcount
    refine ⟨
      { boundaryCount := s
        strictWeak := S.castComponentCount hcount
        scaleOrder_strict :=
          S.castComponentCount_scaleOrder_strict hcount hstrict
        hasImproperEvenRank :=
          Lattice.WeakJordanDecomposition.HasImproperEvenRank.castComponentCount
            S
              (Lattice.WeakJordanDecomposition.HasImproperEvenRank.mergeAdjacentAt
                D.smallAlmostJordan
                  D.smallAlmostJordan_hasImproperEvenRank k heq)
            hcount
        jordan := J
        jordan_eq := by
          exact (S.castComponentCount_toJordan hcount hstrict).symm
        profile := P'
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          have hcast : J.toOrthogonalDecomposition.prefixCarrier
                (z.val + 1) =
              S.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := by
            exact BONG.castComponentCount_prefixCarrier
              (S.toJordan hstrict) hcount (z.val + 1)
          rw [hcast,
            D.smallAlmostJordan.mergeAdjacentAt_prefixCarrier_eq_of_le
              k heq (z.val + 1) (by
                change z.val + 1 ≤ k.val
                change (x.indexEquiv g.castSucc).1.val < k.val at hbeforePair
                omega)]
          congr 1
          dsimp only [weakNext]
          omega
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnext :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by
          have hk' := k.isLt
          change (x.indexEquiv g.castSucc).1.val < k.val at hbeforePair
          omega⟩ : Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    simpa only [J, P'] using hright.trans (congrArg
      (fun p ↦ ordUnit K (D.smallAlmostJordan.scaleGenerator p)) hnext)
  · let hstrict := D.smallAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.smallNoCollisionProfileWitness hcollision b
    have hnextBound : (x.indexEquiv g.castSucc).1.val <
        D.complementComponentCount := by
      have hs := D.smallSelectedPosition.isLt
      change (x.indexEquiv g.castSucc).1.val <
        D.smallSelectedPosition.val at hbefore
      omega
    rcases x.exists_boundary_resolution_ofStrict hstrict P g hlast
        hnextBound with ⟨z, hz, hzval, hleft, hright⟩
    refine ⟨
      { boundaryCount := D.complementComponentCount
        strictWeak := D.smallAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.smallAlmostJordan_hasImproperEvenRank
        jordan := D.smallAlmostJordan.toJordan hstrict
        jordan_eq := rfl
        profile := P
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          congr 1
          dsimp only [weakNext]
          omega
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnext :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩ :
          Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    exact hright.trans (congrArg
      (fun p ↦ ordUnit K (D.smallAlmostJordan.scaleGenerator p)) hnext)

set_option maxHeartbeats 0 in
/-- Resolve a terminal large-side coordinate strictly before the selected
component, provided it is not the left member of the unique large-side
collision.  That excluded member is internal after amalgamation and is
handled by `nonempty_largeInternalStrictCoordinateResolution`. -/
theorem nonempty_largeStrictBoundaryResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {m : Nat} (a : BONG.GoodBONG q M (m + 1)) (g : Fin m)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 <
      D.largeSelectedPosition)
    (hlast : ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1).carrier)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1 =
          D.largeCommonPosition c) :
    Nonempty (BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a) g) := by
  classical
  let x := D.largeWeakProfileWitness a
  let weakNext : Fin (D.complementComponentCount + 1) :=
    ⟨(x.indexEquiv g.castSucc).1.val + 1, by
      have hs := D.largeSelectedPosition.isLt
      change (x.indexEquiv g.castSucc).1.val <
        D.largeSelectedPosition.val at hbefore
      omega⟩
  by_cases hcollision : D.LargeScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hbeforePair : (x.indexEquiv g.castSucc).1 < k.castSucc := by
      change (x.indexEquiv g.castSucc).1 <
        D.largeSelectedPosition at hbefore
      rw [← hk.2] at hbefore
      change (x.indexEquiv g.castSucc).1.val < k.val + 1 at hbefore
      have hle : (x.indexEquiv g.castSucc).1 ≤ k.castSucc := by
        change (x.indexEquiv g.castSucc).1.val ≤ k.val
        omega
      exact lt_of_le_of_ne hle (by
        intro heqPosition
        apply hnotCollisionLeft
        exact ⟨c, hscale, heqPosition.trans hk.1⟩)
    have hresolution := x.exists_boundary_resolution_ofMerge_before
      D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P g
      hbeforePair hlast
    rcases hresolution with ⟨s, hcount, hresolution⟩
    dsimp only at hresolution
    rcases hresolution with ⟨z, hz, hzval, hleft, hright⟩
    let J := (S.toJordan hstrict).castComponentCount hcount
    let P' := P.castComponentCount hcount
    refine ⟨
      { boundaryCount := s
        strictWeak := S.castComponentCount hcount
        scaleOrder_strict :=
          S.castComponentCount_scaleOrder_strict hcount hstrict
        hasImproperEvenRank :=
          Lattice.WeakJordanDecomposition.HasImproperEvenRank.castComponentCount
            S
              (Lattice.WeakJordanDecomposition.HasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan
                  D.largeAlmostJordan_hasImproperEvenRank k heq)
            hcount
        jordan := J
        jordan_eq := by
          exact (S.castComponentCount_toJordan hcount hstrict).symm
        profile := P'
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          have hcast : J.toOrthogonalDecomposition.prefixCarrier
                (z.val + 1) =
              S.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := by
            exact BONG.castComponentCount_prefixCarrier
              (S.toJordan hstrict) hcount (z.val + 1)
          rw [hcast,
            D.largeAlmostJordan.mergeAdjacentAt_prefixCarrier_eq_of_le
              k heq (z.val + 1) (by
                change z.val + 1 ≤ k.val
                change (x.indexEquiv g.castSucc).1.val < k.val at hbeforePair
                omega)]
          congr 1
          dsimp only [weakNext]
          omega
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnext :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by
          have hk' := k.isLt
          change (x.indexEquiv g.castSucc).1.val < k.val at hbeforePair
          omega⟩ : Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    simpa only [J, P'] using hright.trans (congrArg
      (fun p ↦ ordUnit K (D.largeAlmostJordan.scaleGenerator p)) hnext)
  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hnextBound : (x.indexEquiv g.castSucc).1.val <
        D.complementComponentCount := by
      have hs := D.largeSelectedPosition.isLt
      change (x.indexEquiv g.castSucc).1.val <
        D.largeSelectedPosition.val at hbefore
      omega
    rcases x.exists_boundary_resolution_ofStrict hstrict P g hlast
        hnextBound with ⟨z, hz, hzval, hleft, hright⟩
    refine ⟨
      { boundaryCount := D.complementComponentCount
        strictWeak := D.largeAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.largeAlmostJordan_hasImproperEvenRank
        jordan := D.largeAlmostJordan.toJordan hstrict
        jordan_eq := rfl
        profile := P
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          congr 1
          dsimp only [weakNext]
          omega
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnext :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩ :
          Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    exact hright.trans (congrArg
      (fun p ↦ ordUnit K (D.largeAlmostJordan.scaleGenerator p)) hnext)

set_option maxHeartbeats 0 in
/-- Resolve a terminal large-side coordinate at or after the selected
component.  Since the only possible large-side collision consists of a
common component immediately followed by the selected component, the
whole collision pair lies in the prefix through this coordinate. -/
theorem nonempty_largeStrictBoundaryResolution_afterSelected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {m : Nat} (a : BONG.GoodBONG q M (m + 1)) (g : Fin m)
    (hselectedLe : D.largeSelectedPosition ≤
      ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1)
    (hlast : ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1).carrier)
    (hnext : ((D.largeWeakProfileWitness a).indexEquiv g.castSucc).1.val <
      D.complementComponentCount) :
    Nonempty (BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a) g) := by
  classical
  let x := D.largeWeakProfileWitness a
  have hnextX : (x.indexEquiv g.castSucc).1.val <
      D.complementComponentCount := by
    simpa only [x] using hnext
  let weakNext : Fin (D.complementComponentCount + 1) :=
    ⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩
  by_cases hcollision : D.LargeScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent c hscale
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
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hpairLe : k.succ ≤ (x.indexEquiv g.castSucc).1 := by
      rw [hk.2]
      exact hselectedLe
    have hresolution := x.exists_boundary_resolution_ofMerge_after_pair
      D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P g
      hpairLe hlast hnext
    rcases hresolution with ⟨s, hcount, hresolution⟩
    dsimp only at hresolution
    rcases hresolution with ⟨z, hz, hzval, hleft, hright⟩
    let J := (S.toJordan hstrict).castComponentCount hcount
    let P' := P.castComponentCount hcount
    refine ⟨
      { boundaryCount := s
        strictWeak := S.castComponentCount hcount
        scaleOrder_strict :=
          S.castComponentCount_scaleOrder_strict hcount hstrict
        hasImproperEvenRank :=
          Lattice.WeakJordanDecomposition.HasImproperEvenRank.castComponentCount
            S
              (Lattice.WeakJordanDecomposition.HasImproperEvenRank.mergeAdjacentAt
                D.largeAlmostJordan
                  D.largeAlmostJordan_hasImproperEvenRank k heq)
            hcount
        jordan := J
        jordan_eq := by
          exact (S.castComponentCount_toJordan hcount hstrict).symm
        profile := P'
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          have hcast : J.toOrthogonalDecomposition.prefixCarrier
                (z.val + 1) =
              S.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := by
            exact BONG.castComponentCount_prefixCarrier
              (S.toJordan hstrict) hcount (z.val + 1)
          calc
            J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) =
                S.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := hcast
            _ = S.toOrthogonalDecomposition.prefixCarrier
                (weakNext.val - 1) := by
              congr 1
            _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
                weakNext.val :=
              D.largeAlmostJordan.mergeAdjacentAt_prefixCarrier_eq_of_pair_le
                k heq weakNext.val (by
                  dsimp only [weakNext]
                  change k.val + 1 ≤ (x.indexEquiv g.castSucc).1.val at hpairLe
                  omega) (by exact weakNext.isLt.le)
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnextEq :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩ :
          Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    exact hright.trans (congrArg
      (fun p ↦ ordUnit K (D.largeAlmostJordan.scaleGenerator p)) hnextEq)
  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    rcases x.exists_boundary_resolution_ofStrict hstrict P g hlast hnext with
      ⟨z, hz, hzval, hleft, hright⟩
    refine ⟨
      { boundaryCount := D.complementComponentCount
        strictWeak := D.largeAlmostJordan
        scaleOrder_strict := hstrict
        hasImproperEvenRank := D.largeAlmostJordan_hasImproperEvenRank
        jordan := D.largeAlmostJordan.toJordan hstrict
        jordan_eq := rfl
        profile := P
        boundary := z
        weakNext := weakNext
        weakNext_val := rfl
        boundaryIndex_eq := hz
        prefixCarrier_eq := by
          congr 1
          dsimp only [weakNext]
          omega
        leftScaleOrder_eq := hleft
        rightScaleOrder_eq := ?_ }⟩
    have hnextEq :
        (⟨(x.indexEquiv g.castSucc).1.val + 1, by omega⟩ :
          Fin (D.complementComponentCount + 1)) = weakNext := by
      apply Fin.ext
      rfl
    exact hright.trans (congrArg
      (fun p ↦ ordUnit K (D.largeAlmostJordan.scaleGenerator p)) hnextEq)

/-- Scale interval in the aligned weak profiles, without excluding either
equal-scale collision. -/
theorem weakAligned_fundamentalScale_interval
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (b : BONG.GoodBONG q N n) (I : Fin n)
    (hrange :
      ((D.largeWeakProfileWitness a).indexEquiv I).1 <
          D.largeSelectedPosition ∨
        (((D.largeWeakProfileWitness a).indexEquiv I).1 =
            D.largeSelectedPosition ∧
          ((D.largeWeakProfileWitness a).indexEquiv I).2.val = 0)) :
    let pLarge := ((D.largeWeakProfileWitness a).indexEquiv I).1
    let pSmall := ((D.smallWeakProfileWitness b).indexEquiv I).1
    ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
        ordUnit K (D.smallAlmostJordan.scaleGenerator pSmall) ∧
      ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
  let pLarge := ((D.largeWeakProfileWitness a).indexEquiv I).1
  let pSmall := ((D.smallWeakProfileWitness b).indexEquiv I).1
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  change pLarge = pSmall ∧ _ at hcoordinates
  change ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator pSmall) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
      ordUnit K D.input.block.enlargedScaleGenerator
  change pLarge < D.largeSelectedPosition ∨
    (pLarge = D.largeSelectedPosition ∧ _) at hrange
  rcases hrange with hbefore | ⟨hposition, _hlocal⟩
  · have hscaleEq := D.weakAligned_scaleOrder_eq_before_selected
      hselected pLarge hbefore
    have hboundRaw := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    have hbound :
        ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
          ordUnit K D.input.block.enlargedScaleGenerator := by
      simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hboundRaw
    constructor
    · rw [← hcoordinates.1]
      exact hscaleEq.le
    · exact hbound
  · have hsmallPosition : pSmall = D.smallSelectedPosition := by
      calc
        pSmall = pLarge := hcoordinates.1.symm
        _ = D.largeSelectedPosition := hposition
        _ = D.smallSelectedPosition := hselected.symm
    constructor
    · rw [hposition, hsmallPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected]
      exact D.enlargedScaleOrder_lt_smallScaleOrder.le
    · rw [hposition, D.largeAlmostJordan_scaleGenerator_selected]

/-- Lemma 5.17(i) whenever the large weak coordinate is internal after
resolving the possible collision.  The small side only needs the universal
fundamental-weight upper bound. -/
theorem weakAligned_prefixAlphaCap_le_of_internalResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
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
  have hrange := D.lemma517Range_large_coordinate a i hi
  change (x.indexEquiv I).1 < D.largeSelectedPosition ∨
      ((x.indexEquiv I).1 = D.largeSelectedPosition ∧
        (x.indexEquiv I).2.val = 0) at hrange
  have hlargeLe : (x.indexEquiv I).1 ≤ D.largeSelectedPosition := by
    rcases hrange with hbefore | ⟨hposition, _⟩
    · exact hbefore.le
    · exact hposition.le
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallLe : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ ≤ D.largeSelectedPosition := hlargeLe
      _ = D.smallSelectedPosition := hselected.symm
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe hinternal
  have hscales := D.weakAligned_fundamentalScale_interval
    hselected a b I hrange
  change ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1) ≤
      ordUnit K D.input.block.enlargedScaleGenerator at hscales
  have hscale : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      Rsmall.jordan.fundamentalScaleOrder
        (Rsmall.profile.indexEquiv I).1 := by
    rw [Rlarge.scaleOrder_eq, Rsmall.scaleOrder_eq]
    exact hscales.1
  have hbound : Rlarge.jordan.fundamentalScaleOrder
        (Rlarge.profile.indexEquiv I).1 ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    rw [Rlarge.scaleOrder_eq]
    exact hscales.2
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

/-- Lemma 5.17(i) at an ordinary weak boundary before the selected block,
allowing a later equal-scale amalgamation on either side. -/
theorem weakAligned_prefixAlphaCap_le_of_boundaryResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
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
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
    (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
      _ < D.largeSelectedPosition := hbefore
      _ = D.smallSelectedPosition := hselected.symm
  have hsmallLast : (y.indexEquiv I).2.val + 1 =
      finrank K (D.smallAlmostJordan.component (y.indexEquiv I).1).carrier := by
    have hrank := congrFun (D.almostJordan_componentRank_eq hselected)
      (x.indexEquiv I).1
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
    have h := D.weakAligned_scaleOrder_eq_before_selected
      hselected (x.indexEquiv I).1 hbefore
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
    · have h := D.weakAligned_scaleOrder_eq_before_selected
        hselected Rlarge.weakNext hnextBefore
      rw [← hnextEq]
      exact h.le
    · have hnextPosition : Rlarge.weakNext = D.largeSelectedPosition :=
        le_antisymm hnextLe (le_of_not_gt hnextBefore)
      have hsmallNextPosition : Rsmall.weakNext = D.smallSelectedPosition := by
        calc
          Rsmall.weakNext = Rlarge.weakNext := hnextEq.symm
          _ = D.largeSelectedPosition := hnextPosition
          _ = D.smallSelectedPosition := hselected.symm
      rw [hnextPosition, hsmallNextPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected]
      exact D.enlargedScaleOrder_lt_smallScaleOrder.le
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

/-- Complete Lemma 5.17(i) for aligned weak profiles, including every
combination of the two possible endpoint collisions. -/
theorem weakAligned_prefixAlphaCap_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
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
  let y := D.smallWeakProfileWitness b
  have hrange := D.lemma517Range_large_coordinate a i hi
  change (x.indexEquiv I).1 < D.largeSelectedPosition ∨
      ((x.indexEquiv I).1 = D.largeSelectedPosition ∧
        (x.indexEquiv I).2.val = 0) at hrange
  by_cases hinternal : (x.indexEquiv I).2.val + 1 <
      finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier
  · exact D.weakAligned_prefixAlphaCap_le_of_internalResolution
      hselected a b i hi hcurrent (Or.inl hinternal)
  · have hlast : (x.indexEquiv I).2.val + 1 =
        finrank K (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier := by
      have hlocal := (x.indexEquiv I).2.isLt
      omega
    rcases hrange with hbefore | ⟨hposition, hlocalZero⟩
    · by_cases hcollisionLeft : ∃ c : Fin D.complementComponentCount,
          ordUnit K (D.complementStrictWeak.scaleGenerator c) =
              ordUnit K D.input.block.enlargedScaleGenerator ∧
            (x.indexEquiv I).1 = D.largeCommonPosition c
      · exact D.weakAligned_prefixAlphaCap_le_of_internalResolution
          hselected a b i hi hcurrent (Or.inr hcollisionLeft)
      · exact D.weakAligned_prefixAlphaCap_le_of_boundaryResolution
          hselected a b i hbefore hlast hcollisionLeft
    · have hRankOne : finrank K (D.largeAlmostJordan.component
          (x.indexEquiv I).1).carrier = 1 := by
        omega
      have hBlockRankOne :
          finrank K D.input.block.component.carrier = 1 := by
        rw [hposition, D.largeAlmostJordan_finrank_selected] at hRankOne
        exact hRankOne
      have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
      change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
        (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
      have hsmallPosition : (y.indexEquiv I).1 = D.smallSelectedPosition := by
        calc
          (y.indexEquiv I).1 = (x.indexEquiv I).1 := hcoordinates.1.symm
          _ = D.largeSelectedPosition := hposition
          _ = D.smallSelectedPosition := hselected.symm
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
      have hlargeEffective :=
        D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hBlockRankOne
      have hsmallEffective :=
        D.smallSelected_effectiveNormOrder_eq_scale_of_rank_one hBlockRankOne
      change ((D.largeWeakProfileWitness a).indexEquiv I).1 =
        D.largeSelectedPosition at hposition
      change ((D.smallWeakProfileWitness b).indexEquiv I).1 =
        D.smallSelectedPosition at hsmallPosition
      rw [D.largeWeak_order_eq_localOrder a I,
        D.smallWeak_order_eq_localOrder b I] at hcurrent'
      simp only [hposition, hsmallPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected] at hcurrent'
      rw [hlargeEffective, hsmallEffective] at hcurrent'
      simp only [JordanProfileOrder.localOrder_of_proper] at hcurrent'
      exact False.elim
        ((ne_of_lt D.enlargedScaleOrder_lt_smallScaleOrder) hcurrent')

end Lattice.Beli2019Lemma51Data

end Bong
