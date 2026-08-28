/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralCollision

/-!
# Collision-left central representation cases in Beli (2019), Section 5

This file resolves the remaining aligned direct cases in which the target
coordinate lies in the common component immediately to the left of a selected
block with the same scale.  The two weak components are amalgamated explicitly,
and all endpoint/rank branches are discharged from Lemma 3.7.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Explicit strict resolution of a coordinate in the common (left) member
of the unique large-side collision pair. -/
noncomputable def largeCollisionLeftCoordinateResolution
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeCommonPosition c) :
    BONG.StrictCoordinateResolution a.toBONG D.largeAlmostJordan
      (D.largeWeakProfileWitness a) I := by
  classical
  let x := D.largeWeakProfileWitness a
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
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
    Classical.choice (a.toBONG.beliLemma47_profile a.good
      (S.toJordan hstrict))
  have hleft : (x.indexEquiv I).1 = k.castSucc :=
    hposition.trans hk.1.symm
  have hcoordinates := x.strict_coordinates_of_left
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
          (P.indexEquiv I).1.val = k.val := congrArg Fin.val hcoordinates.1
          _ = (x.indexEquiv I).1.val := by
            simpa only [Fin.val_castSucc] using
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

theorem largeCollisionLeftCoordinateResolution_component_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeCommonPosition c) :
    (D.largeCollisionLeftCoordinateResolution c hscale a I
      hposition).component =
        Classical.choose (D.largeCollision_adjacent c hscale) := by
  classical
  let x := D.largeWeakProfileWitness a
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
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
    Classical.choice (a.toBONG.beliLemma47_profile a.good
      (S.toJordan hstrict))
  have hleft : (x.indexEquiv I).1 = k.castSucc :=
    hposition.trans hk.1.symm
  have hcoordinates := x.strict_coordinates_of_left
    D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hleft
  change (P.indexEquiv I).1 = k
  exact hcoordinates.1

theorem largeCollisionLeftCoordinateResolution_rank
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hposition : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
      D.largeCommonPosition c) :
    let R := D.largeCollisionLeftCoordinateResolution
      c hscale a I hposition
    R.jordan.componentRank R.component =
      finrank K (D.complementStrictWeak.component c).carrier +
        finrank K D.input.block.component.carrier := by
  classical
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let R := D.largeCollisionLeftCoordinateResolution
    c hscale a I hposition
  have hcomponent : R.component = k :=
    D.largeCollisionLeftCoordinateResolution_component_eq
      c hscale a I hposition
  change finrank K (R.strictWeak.component R.component).carrier = _
  rw [hcomponent]
  change finrank K
      ((D.largeAlmostJordan.mergeAdjacentAt k heq).component k).carrier = _
  rw [Lattice.WeakJordanDecomposition.mergeAdjacentAt_componentRank_self,
    hk.1, hk.2, D.largeAlmostJordan_finrank_common,
    D.largeAlmostJordan_finrank_selected]

set_option maxHeartbeats 0 in
theorem centralCertificate_of_collisionLeft_targetFirst_highRank_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hcoordinates :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (hsourceBefore :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      ((D.smallWeakProfileWitness b).indexEquiv ISource).1 <
        D.smallSelectedPosition)
    (hprefixCarrier :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      2 < R.jordan.componentRank R.component) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let ISource : Fin (n + 2) := gSource.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by
      simpa only [ITarget, gTarget, Fin.castSucc_mk] using hposition)
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change 2 < Rtarget.jordan.componentRank Rtarget.component at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 := rfl
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hcoordinates' :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget, gTarget, Fin.castSucc_mk] using hcoordinates
  have hsourceNextZero : (y.indexEquiv ITarget).2.val = 0 := by
    omega
  have hadjacent :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsourceNextZero
  have hsourceBefore' : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore')
      (by simpa only [y, ISource] using hadjacent.2)
  have hweakNext : Rsource.weakNext.val =
      (x.indexEquiv ITarget).1.val := by
    rw [Rsource.weakNext_val]
    have hcomponentEq := congrArg Fin.val hcoordinates'.1
    have hadjacentVal :
        ((D.smallWeakProfileWitness b).indexEquiv gSource.castSucc).1.val + 1 =
          (y.indexEquiv ITarget).1.val := by
      simpa only [y, ISource] using hadjacent.1
    omega
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero hoffset
  have hsourceCarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.weakNext.val := by
    rw [← Rsource.jordan_eq]
    exact Rsource.prefixCarrier_eq
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hprefixCarrier
  have hcarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
    calc
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val := hsourceCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := by rw [hweakNext]
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := haligned.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := htargetCarrier.symm
  let C := (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixQuadraticSublattice
      (Rsource.boundary.val + 1)
  let E := Rtarget.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    Rtarget.component.val
  have hprefix : QuadraticSpace.Isometry C.space E.space :=
    C.spaceIsometryOfCarrierEq E hcarrier
  have htargetPositive : 0 < ITarget.val := by
    change 0 < i.val - 1
    have hi := i.one_lt
    omega
  rcases Rtarget.exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first
      gTarget rfl htargetPositive hfirst hrank
        Rsource.strictProfile Rsource.boundary (by
          simpa only [C, E] using hprefix)
    with ⟨target, hrep⟩
  let sourceBase :=
    BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
      b Rsource.strictWeak Rsource.hasImproperEvenRank
        Rsource.scaleOrder_strict Rsource.strictProfile Rsource.boundary
  let sourceSpace : BONG.GoodBONG.SpaceApproximationModel b gSource :=
    sourceBase.castIndex Rsource.strictProfile_boundaryIndex_eq
  let source := sourceSpace.toDiagonal
  have hmodels : DiagonalRepresents
      (diagonalUnitCoefficients source.units)
      (diagonalUnitCoefficients target.units) :=
    sourceBase.castIndex_diagonalRepresents
      Rsource.strictProfile_boundaryIndex_eq hrep
  exact .represented
    (target.centralRepresentation a b hdefect i htrigger source hmodels)

set_option maxHeartbeats 0 in
/-- The aligned specialization of the collision-left high-rank argument. -/
theorem weakAligned_centralCertificate_of_collisionLeft_targetFirst_highRank
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      2 < R.jordan.componentRank R.component) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val = (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hcoordinatesRaw
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by simpa only [x, ITarget] using hposition)
  have hfirst' : ITarget.val = Rtarget.coordinates.start := by
    simpa only [ITarget, Rtarget] using hfirst
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hsmallTargetZero : (y.indexEquiv ITarget).2.val = 0 := by omega
  have hadjacent := y.terminal_and_component_succ_eq_of_global_succ_local_zero
    ISource ITarget (by
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega) hsmallTargetZero
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have htargetBefore' : (x.indexEquiv ITarget).1 <
        D.largeSelectedPosition := by
      simpa only [x, ITarget] using htargetBefore
    have hselectedVal := congrArg Fin.val hselected
    have hcomponentEq := congrArg Fin.val hcoordinates.1
    have hadjacentVal := hadjacent.1
    change (y.indexEquiv ISource).1.val < D.smallSelectedPosition.val
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBefore'
    omega
  have hprefix := D.aligned_prefixCarrier_eq hselected
    (x.indexEquiv ITarget).1.val
  exact D.centralCertificate_of_collisionLeft_targetFirst_highRank_of_prefixAlignment
    c hscale a b hdefect i htrigger htargetBefore
      (by simpa only [x, y, ITarget] using hcoordinates)
      (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [x, ITarget] using hprefix)
      hposition hfirst hrank

set_option maxHeartbeats 0 in
theorem collisionLeft_targetFirst_rank_two_leftOuter_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      R.jordan.componentRank R.component = 2) :
    a.order (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2)) <
      a.order ⟨i.val, i.lt_large⟩ := by
  classical
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by simpa only [x, ITarget] using hposition)
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change Rtarget.jordan.componentRank Rtarget.component = 2 at hrank
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeCommonPosition c := by
    simpa only [x, ITarget] using hposition
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hcommonRank : finrank K
      (D.complementStrictWeak.component c).carrier = 1 := by
    have hrankRaw := D.largeCollisionLeftCoordinateResolution_rank
      c hscale a ITarget htargetPosition
    change Rtarget.jordan.componentRank Rtarget.component = _ at hrankRaw
    omega
  have htargetRank : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier = 1 := by
    rw [htargetPosition, D.largeAlmostJordan_finrank_common, hcommonRank]
  have htargetTerminal : (x.indexEquiv ITarget).2.val + 1 =
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier := by
    omega
  have hnextCoordinates := x.indexEquiv_global_succ_of_terminal
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) htargetTerminal
  have hpreviousCoordinates :=
    x.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetZero
  let pPrev := (x.indexEquiv ISource).1
  let pCurrent := (x.indexEquiv ITarget).1
  let pNext := (x.indexEquiv INext).1
  have hpPrevCurrent : pPrev < pCurrent := by
    change pPrev.val < pCurrent.val
    have h := hpreviousCoordinates.1
    change pPrev.val + 1 = pCurrent.val at h
    omega
  have hpCurrentSelected : pCurrent = D.largeCommonPosition c := by
    simpa only [pCurrent] using htargetPosition
  have hpNextSelected : pNext = D.largeSelectedPosition := by
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
    apply Fin.ext
    have hnextVal := hnextCoordinates.1
    have hcurrentVal := congrArg Fin.val (hpCurrentSelected.trans hk.1.symm)
    have hselectedVal := congrArg Fin.val hk.2
    change pNext.val = D.largeSelectedPosition.val
    change pNext.val = pCurrent.val + 1 at hnextVal
    change pCurrent.val = k.val at hcurrentVal
    change k.val + 1 = D.largeSelectedPosition.val at hselectedVal
    omega
  have hpCurrentLtSelected : pCurrent < D.largeSelectedPosition := by
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
    change pCurrent.val < D.largeSelectedPosition.val
    have hcurrentVal := congrArg Fin.val (hpCurrentSelected.trans hk.1.symm)
    have hselectedVal := congrArg Fin.val hk.2
    change pCurrent.val = k.val at hcurrentVal
    change k.val + 1 = D.largeSelectedPosition.val at hselectedVal
    omega
  have hpPrevSelected : pPrev < D.largeSelectedPosition :=
    hpPrevCurrent.trans hpCurrentLtSelected
  let prevScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
  let currentScale := ordUnit K D.input.block.enlargedScaleGenerator
  have hcurrentScale : ordUnit K
      (D.largeAlmostJordan.scaleGenerator pCurrent) = currentScale := by
    rw [hpCurrentSelected, D.largeAlmostJordan_scaleGenerator_common]
    simpa only [currentScale] using hscale
  have hprevScaleLe : prevScale ≤ currentScale := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hpPrevCurrent.le
    calc
      prevScale = ordUnit K
          (D.largeAlmostJordan.scaleGenerator pPrev) := rfl
      _ ≤ ordUnit K (D.largeAlmostJordan.scaleGenerator pCurrent) := hmono
      _ = currentScale := hcurrentScale
  have hprevScaleLt : prevScale < currentScale := by
    refine lt_of_le_of_ne hprevScaleLe ?_
    intro heq
    have heqRaw : ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator pCurrent) := by
      simpa only [prevScale, hcurrentScale] using heq
    rcases D.largeEqualScale_involves_selected
        (ne_of_lt hpPrevCurrent) heqRaw with hprev | hcurrent
    · exact (ne_of_lt hpPrevSelected) hprev
    · exact (ne_of_lt hpCurrentLtSelected) hcurrent
  have hsourceOrderLe : a.order ISource ≤ prevScale := by
    rw [D.largeWeak_order_eq_localOrder a ISource]
    change JordanProfileOrder.localOrder prevScale
        (D.largeAlmostJordan.effectiveNormOrderAt pPrev prevScale)
        (x.indexEquiv ISource).2.val ≤ prevScale
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pPrev
    have hlocalLast : (x.indexEquiv ISource).2.val =
        finrank K (D.largeAlmostJordan.component pPrev).carrier - 1 := by
      have hterminal := hpreviousCoordinates.2
      change (x.indexEquiv ISource).2.val + 1 =
        finrank K (D.largeAlmostJordan.component pPrev).carrier at hterminal
      omega
    have heffectiveLower :=
      D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt pPrev prevScale
    rw [hlocalLast]
    have hlast' : JordanProfileOrder.localOrder prevScale
          (D.largeAlmostJordan.effectiveNormOrderAt pPrev prevScale)
          (finrank K (D.largeAlmostJordan.component pPrev).carrier - 1) =
        2 * prevScale -
          D.largeAlmostJordan.effectiveNormOrderAt pPrev prevScale := by
      simpa only [prevScale] using hlast
    rw [hlast']
    omega
  have hnextZero : (x.indexEquiv INext).2.val = 0 := by
    simpa only [Fin.val_mk] using hnextCoordinates.2
  have hnextOrder : a.order INext = currentScale := by
    rw [D.largeWeak_order_eq_localOrder a INext]
    change JordanProfileOrder.localOrder
        (ordUnit K (D.largeAlmostJordan.scaleGenerator pNext))
        (D.largeAlmostJordan.effectiveNormOrderAt pNext
          (ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)))
        (x.indexEquiv INext).2.val = currentScale
    rw [hpNextSelected, hnextZero,
      D.largeAlmostJordan_scaleGenerator_selected]
    have heffective :=
      D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hfin
    rw [heffective]
    simpa only [JordanProfileOrder.localOrder_of_proper, currentScale]
  have houterLe : a.order ISource ≤ a.order INext := by
    have hbound : ISource.val + 2 < n + 2 := by
      dsimp only [ISource, Fin.val_mk]
      have := i.one_lt
      have := i.lt_large
      omega
    calc
      a.order ISource ≤ a.order ⟨ISource.val + 2, hbound⟩ :=
        a.good ISource hbound
      _ = a.order INext := by
        apply congrArg a.order
        apply Fin.ext
        dsimp only [ISource, INext, Fin.val_mk]
        have := i.one_lt
        omega
  refine lt_of_le_of_ne houterLe ?_
  intro houterEq
  rw [hnextOrder] at houterEq
  have hreverse : currentScale ≤ prevScale := by
    rw [← houterEq]
    exact hsourceOrderLe
  exact (not_le_of_gt hprevScaleLt hreverse)

end Lattice.Beli2019Lemma51Data

namespace BONG.StrictCoordinateResolution

set_option maxHeartbeats 0 in
/-- Terminal case of Lemma 3.7(iv), packaged with the carrier lower bound
needed by the central representation argument. -/
theorem exists_leftSpaceModel_iv_of_binary_first_terminal
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : R.jordan.componentRank R.component = 2)
    (hcomponentLast : R.component.val + 1 = R.componentCount)
    (hnextBound : I.val + 1 < n + 2)
    (hleftOuter : a.order ⟨I.val - 1, by omega⟩ <
      a.order ⟨I.val + 1, hnextBound⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      R.jordan.toOrthogonalDecomposition.prefixCarrier R.component.val ≤
        model.carrier := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let resolved : StrictCoordinateResolution a.toBONG W x I :=
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hrankP : (strictWeak.toJordan hstrict).componentRank p = 2 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hpPositive : 0 < p.val := by
      have hraw := resolved.component_pos_of_first_of_positive hpositive (by
        simpa only [resolved] using hfirst)
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hraw
    have hpLast : p.val + 1 = t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.componentCount] using hcomponentLast
    let pPrev : Fin (t + 1) := ⟨p.val - 1, by omega⟩
    have hpPrevSucc : pPrev.val + 1 = p.val := by
      dsimp only [pPrev]
      omega
    have hIio : Finset.Iio p = insert pPrev (Finset.Iio pPrev) := by
      ext z
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change z.val < p.val ↔ z = pPrev ∨ z.val < pPrev.val
      constructor
      · intro hz
        by_cases heq : z.val = pPrev.val
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (rfl | hz) <;> omega
    have hstartSum :
        (∑ z ∈ Finset.Iio p,
          (strictWeak.toJordan hstrict).componentRank z) = I.val := by
      change resolved.coordinates.start = I.val
      exact (by simpa only [resolved] using hfirst.symm)
    have hprevRankPositive : 0 <
        (strictWeak.toJordan hstrict).componentRank pPrev :=
      strictWeak.component_finrank_pos pPrev
    have hprevLast : profile.profileComponentLastIndex pPrev =
        ⟨I.val - 1, by omega⟩ := by
      apply Fin.ext
      change (profile.profileComponentLastIndex pPrev).val = I.val - 1
      rw [hIio, Finset.sum_insert (by simp)] at hstartSum
      have hrankSub :
          (strictWeak.toJordan hstrict).componentRank pPrev - 1 + 1 =
            (strictWeak.toJordan hstrict).componentRank pPrev :=
        Nat.sub_add_cancel (by omega)
      have hlastVal :=
        BONG.JordanOrderProfileWitness.profileComponentLastIndex_val
          profile pPrev
      have htargetSub : I.val - 1 + 1 = I.val :=
        Nat.sub_add_cancel (by omega)
      omega
    have hsecond : profile.profileComponentSecondIndex p (by
        rw [hrankP]
        omega) = ⟨I.val + 1, by omega⟩ := by
      apply Fin.ext
      rw [BONG.JordanOrderProfileWitness.profileComponentSecondIndex_val]
      rw [hstartSum]
    have hleftProfile : ∀ _hp : 0 < p.val,
        a.order (profile.profileComponentLastIndex
          ⟨p.val - 1, by omega⟩) <
        a.order (profile.profileComponentSecondIndex p (by
          rw [hrankP]
          omega)) := by
      intro _hp
      have hprevEq : (⟨p.val - 1, by omega⟩ : Fin (t + 1)) = pPrev := by
        apply Fin.ext
        rfl
      rw [hprevEq, hprevLast, hsecond]
      exact hleftOuter
    have hrightProfile : ∀ hp : p.val + 1 < t + 1,
        a.order (profile.profileComponentFirstIndex p) <
        a.order (profile.profileComponentFirstIndex
          ⟨p.val + 1, hp⟩) := by
      intro hp
      omega
    have heffectiveP := profile.beli2019Lemma36 strictWeak hparity hstrict
      p hrankP hleftProfile hrightProfile
    change strictWeak.effectiveNormOrderAt p
        (ordUnit K (strictWeak.scaleGenerator p)) =
      ordUnit K (strictWeak.normGeneratorUnit p) at heffectiveP
    have hmin : JordanProfileOrder.adjustedAt
        strictWeak.scaleOrderFamily strictWeak.normOrderFamily
          (ordUnit K (strictWeak.scaleGenerator p)) p =
        strictWeak.effectiveNormOrderAt p
          (ordUnit K (strictWeak.scaleGenerator p)) := by
      calc
        JordanProfileOrder.adjustedAt strictWeak.scaleOrderFamily
            strictWeak.normOrderFamily
              (ordUnit K (strictWeak.scaleGenerator p)) p =
            ordUnit K (strictWeak.normGeneratorUnit p) := by
              simp [JordanProfileOrder.adjustedAt,
                Lattice.WeakJordanDecomposition.scaleOrderFamily,
                Lattice.WeakJordanDecomposition.normOrderFamily]
        _ = _ := heffectiveP.symm
    let G := BONG.RepresentedFundamentalNormGenerator.ofComponentMinimum
      strictWeak hstrict p hmin
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    rcases BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_iv_last_nonsingleton
        a strictWeak hparity hstrict profile p hpPositive hpLast
          G.value G.fundamental G.componentValue hrankP hleftProfile
      with ⟨_A', hleftRankRaw, _hA', _hterminal, happroximationRaw, _hright⟩
    have hzCut : zLeft.val + 1 = p.val := by
      dsimp only [zLeft]
      omega
    have hcomponentZ :
        Lattice.JordanDecomposition.boundaryRightIndex zLeft = p := by
      apply Fin.ext
      change zLeft.val + 1 = p.val
      exact hzCut
    have hleftRank : 1 <
        (strictWeak.toJordan hstrict).componentRank
          (Lattice.JordanDecomposition.boundaryRightIndex zLeft) := by
      rw [hcomponentZ, hrankP]
      omega
    have happroximation : a.IsSpaceApproximation
        (profile.boundaryOneAfterIndex zLeft hleftRank)
        (profile.boundaryOneAfterDiagonalUnits zLeft G.value) := by
      simpa only [zLeft,
        BONG.JordanOrderProfileWitness.boundaryOneAfterIndex,
        BONG.JordanOrderProfileWitness.boundaryOneAfterDiagonalUnits]
        using happroximationRaw
    have htargetIndex : profile.boundaryOneAfterIndex zLeft hleftRank = g := by
      apply Fin.ext
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix zLeft
      have hsumBoundary :
          (∑ k ∈ Finset.Iio
              (Lattice.JordanDecomposition.boundaryRightIndex zLeft),
            (strictWeak.toJordan hstrict).componentRank k) = I.val := by
        rw [hcomponentZ]
        exact hstartSum
      have hb' := hb.trans hsumBoundary
      simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex,
        Fin.val_mk]
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have horth : ∀ y :
        ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (zLeft.val + 1)).carrier,
        q.bilin (y : V) (G.vector : V) = 0 := by
      intro y
      let y' :
          ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
            |>.prefixQuadraticSublattice p.val).carrier :=
        ⟨(y : V), by simpa only [hzCut] using y.property⟩
      simpa only [y'] using G.prefix_orthogonal_vector y'
    let targetBase : BONG.GoodBONG.SpaceApproximationModel a
        (profile.boundaryOneAfterIndex zLeft hleftRank) :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneAfter_ofOrthogonalVector
        a (strictWeak.toJordan hstrict) profile zLeft G.value hleftRank
          (G.vector : V) G.quadratic_ambientVector horth happroximation
    let target := targetBase.castIndex htargetIndex
    have htargetLower :
        (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
            (zLeft.val + 1) ≤ targetBase.carrier := by
      exact BONG.JordanOrderProfileWitness.PrescribedJordanComparison.prefixCarrier_le_spaceApproximationModel_oneAfter_ofOrthogonalVector
        a (strictWeak.toJordan hstrict) profile zLeft G.value hleftRank
          (G.vector : V) G.quadratic_ambientVector horth happroximation
    refine ⟨target, ?_⟩
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    change (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
        p.val ≤ targetBase.carrier
    simpa only [hzCut] using htargetLower

end BONG.StrictCoordinateResolution

namespace Lattice.Beli2019Lemma51Data

set_option maxHeartbeats 0 in
theorem centralCertificate_of_collisionLeft_targetFirst_rank_two_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hcoordinates :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (hsourceBefore :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      ((D.smallWeakProfileWitness b).indexEquiv ISource).1 <
        D.smallSelectedPosition)
    (hprefixCarrier :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      R.jordan.componentRank R.component = 2) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let ISource : Fin (n + 2) := gSource.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by
      simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition)
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change Rtarget.jordan.componentRank Rtarget.component = 2 at hrank
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeCommonPosition c := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hposition
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have htargetCoordinates' :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget, gTarget, Fin.castSucc_mk] using hcoordinates
  have hsmallTargetZero : (y.indexEquiv ITarget).2.val = 0 := by
    omega
  have hsourceBoundary :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsmallTargetZero
  have hsourceBefore' : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore')
      (by simpa only [y, ISource] using hsourceBoundary.2)
  have hweakNext : Rsource.weakNext.val =
      (x.indexEquiv ITarget).1.val := by
    rw [Rsource.weakNext_val]
    have hsourceSucc : (y.indexEquiv ISource).1.val + 1 =
        (x.indexEquiv ITarget).1.val := by
      calc
        (y.indexEquiv ISource).1.val + 1 =
            (y.indexEquiv ITarget).1.val := hsourceBoundary.1
        _ = (x.indexEquiv ITarget).1.val :=
          congrArg Fin.val htargetCoordinates'.1 |>.symm
    simpa only [y, ISource, gSource] using hsourceSucc
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero (by rfl)
  have hsourceCarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.weakNext.val := by
    rw [← Rsource.jordan_eq]
    exact Rsource.prefixCarrier_eq
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hprefixCarrier
  have hcarrier :
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
    calc
      (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rsource.boundary.val + 1) =
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rsource.weakNext.val := hsourceCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := by rw [hweakNext]
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := haligned.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := htargetCarrier.symm
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    omega
  have hpenultimate : ITarget.val + 2 = Rtarget.coordinates.stop := by
    have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
        Rtarget.jordan.componentRank Rtarget.component := rfl
    omega
  have hcomponentPositive : 0 < Rtarget.component.val :=
    Rtarget.component_pos_of_first_of_positive htargetPositive hfirst
  have hleftOuterRaw :=
    D.collisionLeft_targetFirst_rank_two_leftOuter_lt
      c hscale a i hfin hposition hfirst hrank
  have hleftBound : ITarget.val - 1 < n + 2 := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) ITarget.isLt
  have hnextBound : ITarget.val + 1 < n + 2 := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have := i.one_lt
    have := i.lt_large
    omega
  have hleftOuter : a.order ⟨ITarget.val - 1, hleftBound⟩ <
      a.order ⟨ITarget.val + 1, hnextBound⟩ := by
    convert hleftOuterRaw using 1 <;> apply congrArg a.order <;>
      apply Fin.ext <;>
        dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk] <;>
          have := i.one_lt <;> omega
  by_cases hcomponentNext : Rtarget.component.val + 1 <
      Rtarget.componentCount
  · have hrightBound : ITarget.val + 2 < n + 2 := by
      rw [hpenultimate]
      exact Rtarget.coordinates_stop_lt_of_component_succ hcomponentNext
    have hrightLe : a.order ITarget ≤
        a.order ⟨ITarget.val + 2, hrightBound⟩ :=
      a.good ITarget hrightBound
    rcases lt_or_eq_of_le hrightLe with hrightOuter | hrightOuter
    · rcases Rtarget.exists_leftSpaceModel_iv_of_binary_penultimate
          gTarget rfl htargetPositive hpenultimate hrank hcomponentPositive
            hcomponentNext hrightBound hleftOuter hrightOuter
        with ⟨target, htargetLower, _htargetUpper⟩
      have hsourceToTarget : Rsource.lemma37Model_i.carrier ≤
          target.carrier := by
        rw [Rsource.lemma37Model_i_carrier_eq]
        calc
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
                Rsource.weakNext.val =
              (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
                (Rsource.boundary.val + 1) := hsourceCarrier.symm
          _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
                Rtarget.component.val := hcarrier
          _ ≤ target.carrier := htargetLower
      exact .represented
        (BONG.GoodBONG.centralRepresentation_of_approximationModels
          a b hdefect i htrigger target Rsource.lemma37Model_i
            hsourceToTarget)
    · let C :=
          (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixQuadraticSublattice
            (Rsource.boundary.val + 1)
      let E := Rtarget.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        Rtarget.component.val
      have hprefix : QuadraticSpace.Isometry C.space E.space :=
        C.spaceIsometryOfCarrierEq E hcarrier
      have hinternal : gTarget.val + 1 < n + 1 := by
        dsimp only [gTarget, Fin.val_mk]
        dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
          at hrightBound
        omega
      have houter : a.order gTarget.castSucc =
          a.order (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
        have hrightIndex :
            (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ =
              ⟨ITarget.val + 2, hrightBound⟩ := by
          apply Fin.ext
          rfl
        rw [show gTarget.castSucc = ITarget by rfl, hrightIndex]
        exact hrightOuter
      rcases Rtarget.exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first_with_outer
          gTarget rfl htargetPositive hfirst (by omega) hinternal houter
            Rsource.strictProfile Rsource.boundary (by
              simpa only [C, E] using hprefix)
        with ⟨target, hrep⟩
      let sourceBase :=
        BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
          b Rsource.strictWeak Rsource.hasImproperEvenRank
            Rsource.scaleOrder_strict Rsource.strictProfile Rsource.boundary
      let sourceSpace : BONG.GoodBONG.SpaceApproximationModel b gSource :=
        sourceBase.castIndex Rsource.strictProfile_boundaryIndex_eq
      let source := sourceSpace.toDiagonal
      have hmodels : DiagonalRepresents
          (diagonalUnitCoefficients source.units)
          (diagonalUnitCoefficients target.units) :=
        sourceBase.castIndex_diagonalRepresents
          Rsource.strictProfile_boundaryIndex_eq hrep
      exact .represented
        (target.centralRepresentation a b hdefect i htrigger source hmodels)
  · have hcomponentLast : Rtarget.component.val + 1 =
        Rtarget.componentCount := by
      have := Rtarget.component.isLt
      omega
    obtain ⟨target, htargetLower⟩ :=
      Rtarget.exists_leftSpaceModel_iv_of_binary_first_terminal
        gTarget rfl htargetPositive hfirst hrank hcomponentLast (by
          exact hnextBound) hleftOuter
    have hsourceToTarget : Rsource.lemma37Model_i.carrier ≤
        target.carrier := by
      rw [Rsource.lemma37Model_i_carrier_eq]
      calc
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              Rsource.weakNext.val =
            (Rsource.strictWeak.toJordan Rsource.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
              (Rsource.boundary.val + 1) := hsourceCarrier.symm
        _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
              Rtarget.component.val := hcarrier
        _ ≤ target.carrier := htargetLower
    exact .represented
      (BONG.GoodBONG.centralRepresentation_of_approximationModels
        a b hdefect i htrigger target Rsource.lemma37Model_i hsourceToTarget)

set_option maxHeartbeats 0 in
/-- The aligned specialization of the collision-left binary argument. -/
theorem weakAligned_centralCertificate_of_collisionLeft_targetFirst_rank_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      R.jordan.componentRank R.component = 2) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val = (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hcoordinatesRaw
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by simpa only [x, ITarget] using hposition)
  have hfirst' : ITarget.val = Rtarget.coordinates.start := by
    simpa only [ITarget, Rtarget] using hfirst
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hsmallTargetZero : (y.indexEquiv ITarget).2.val = 0 := by omega
  have hadjacent := y.terminal_and_component_succ_eq_of_global_succ_local_zero
    ISource ITarget (by
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega) hsmallTargetZero
  have hcommonBefore : D.largeCommonPosition c <
      D.largeSelectedPosition := by
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
    change (D.largeCommonPosition c).val < D.largeSelectedPosition.val
    have hcommon := congrArg Fin.val hk.1
    have hsel := congrArg Fin.val hk.2
    change k.val = (D.largeCommonPosition c).val at hcommon
    change k.val + 1 = D.largeSelectedPosition.val at hsel
    omega
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have hcomponentEq := congrArg Fin.val hcoordinates.1
    have hposition' : (x.indexEquiv ITarget).1 =
        D.largeCommonPosition c := by
      simpa only [x, ITarget] using hposition
    have hpositionVal := congrArg Fin.val hposition'
    have hselectedVal := congrArg Fin.val hselected
    have hadjacentVal := hadjacent.1
    change (y.indexEquiv ISource).1.val + 1 =
      (y.indexEquiv ITarget).1.val at hadjacentVal
    change (x.indexEquiv ITarget).1.val =
      (y.indexEquiv ITarget).1.val at hcomponentEq
    change (x.indexEquiv ITarget).1.val =
      (D.largeCommonPosition c).val at hpositionVal
    change D.smallSelectedPosition.val =
      D.largeSelectedPosition.val at hselectedVal
    change (y.indexEquiv ISource).1.val < D.smallSelectedPosition.val
    change (D.largeCommonPosition c).val < D.largeSelectedPosition.val
      at hcommonBefore
    omega
  have hprefix := D.aligned_prefixCarrier_eq hselected
    (x.indexEquiv ITarget).1.val
  exact D.centralCertificate_of_collisionLeft_targetFirst_rank_two_of_prefixAlignment
    c hscale a b hdefect i htrigger hfin
      (by simpa only [x, y, ITarget] using hcoordinates)
      (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [x, ITarget] using hprefix)
      hposition hfirst hrank

set_option maxHeartbeats 0 in
theorem collisionLeft_not_centralTrigger_of_targetPenultimate_notFirst_of_prefixAlignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hcoordinatesInput :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (hcommonPosition : D.largeCommonPosition c =
      D.smallCommonPosition c)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val + 2 = R.coordinates.stop)
    (hnotFirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val ≠ R.coordinates.start) : False := by
  classical
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget (by simpa only [x, ITarget] using hposition)
  change ITarget.val + 2 = Rtarget.coordinates.stop at hpenultimate
  change ITarget.val ≠ Rtarget.coordinates.start at hnotFirst
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeCommonPosition c := by
    simpa only [x, ITarget] using hposition
  let commonRank := finrank K (D.complementStrictWeak.component c).carrier
  have hrank : Rtarget.jordan.componentRank Rtarget.component =
      commonRank + 1 := by
    simpa only [commonRank, hfin, Nat.add_comm] using
      D.largeCollisionLeftCoordinateResolution_rank
        c hscale a ITarget htargetPosition
  have hindex := Rtarget.index_val_eq_coordinates_start_add_local
  have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
      Rtarget.jordan.componentRank Rtarget.component := rfl
  have hresolvedLocal : (Rtarget.profile.indexEquiv ITarget).2.val =
      (x.indexEquiv ITarget).2.val := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal
  have htargetLast : (x.indexEquiv ITarget).2.val + 1 = commonRank := by
    omega
  have htargetLocalPos : 0 < (x.indexEquiv ITarget).2.val := by
    by_contra hnot
    have hzero : (x.indexEquiv ITarget).2.val = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hindexX : ITarget.val = Rtarget.coordinates.start +
        (x.indexEquiv ITarget).2.val := by
      calc
        ITarget.val = Rtarget.coordinates.start +
            (Rtarget.profile.indexEquiv ITarget).2.val := hindex
        _ = Rtarget.coordinates.start +
            (x.indexEquiv ITarget).2.val := by rw [hresolvedLocal]
    have hindexStart : ITarget.val = Rtarget.coordinates.start := by
      omega
    exact hnotFirst hindexStart
  have hcommonRankOneLt : 1 < commonRank := by omega
  have htargetWeakRank : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier =
        commonRank := by
    rw [htargetPosition, D.largeAlmostJordan_finrank_common]
  have htargetTerminal : (x.indexEquiv ITarget).2.val + 1 =
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier := by
    exact htargetLast.trans htargetWeakRank.symm
  have hnextCoordinates := x.indexEquiv_global_succ_of_terminal
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) htargetTerminal
  let pNext := (x.indexEquiv INext).1
  have hpNextSelected : pNext = D.largeSelectedPosition := by
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
    apply Fin.ext
    have hnextVal := hnextCoordinates.1
    have htargetVal := congrArg Fin.val (htargetPosition.trans hk.1.symm)
    have hselectedVal := congrArg Fin.val hk.2
    change pNext.val = D.largeSelectedPosition.val
    change pNext.val = (x.indexEquiv ITarget).1.val + 1 at hnextVal
    change (x.indexEquiv ITarget).1.val = k.val at htargetVal
    change k.val + 1 = D.largeSelectedPosition.val at hselectedVal
    omega
  have hnextZero : (x.indexEquiv INext).2.val = 0 := by
    simpa only [Fin.val_mk] using hnextCoordinates.2
  let scale := ordUnit K D.input.block.enlargedScaleGenerator
  have hnextOrder : a.order INext = scale := by
    rw [D.largeWeak_order_eq_localOrder a INext]
    change JordanProfileOrder.localOrder
        (ordUnit K (D.largeAlmostJordan.scaleGenerator pNext))
        (D.largeAlmostJordan.effectiveNormOrderAt pNext
          (ordUnit K (D.largeAlmostJordan.scaleGenerator pNext)))
        (x.indexEquiv INext).2.val = scale
    rw [hpNextSelected, hnextZero,
      D.largeAlmostJordan_scaleGenerator_selected]
    have heffective :=
      D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hfin
    rw [heffective]
    simpa only [JordanProfileOrder.localOrder_of_proper, scale]
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget] using hcoordinatesInput
  have hsmallPosition : (y.indexEquiv ITarget).1 =
      D.smallCommonPosition c := by
    calc
      (y.indexEquiv ITarget).1 = (x.indexEquiv ITarget).1 :=
        hcoordinates.1.symm
      _ = D.largeCommonPosition c := htargetPosition
      _ = D.smallCommonPosition c := hcommonPosition
  have hsmallLocalPos : 0 < (y.indexEquiv ITarget).2.val := by
    rw [← hcoordinates.2]
    exact htargetLocalPos
  have hsmallScale : ordUnit K
      (D.smallAlmostJordan.scaleGenerator (y.indexEquiv ITarget).1) =
        scale := by
    rw [hsmallPosition, D.smallAlmostJordan_scaleGenerator_common]
    simpa only [scale] using hscale
  let smallEffective := D.smallAlmostJordan.effectiveNormOrderAt
    (y.indexEquiv ITarget).1 scale
  have hscaleEffective : scale ≤ smallEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      (y.indexEquiv ITarget).1 scale
  have hsourceOrder : b.order ISource =
      JordanProfileOrder.localOrder scale smallEffective
        ((y.indexEquiv ITarget).2.val - 1) := by
    have hraw := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred
      ITarget hsmallLocalPos
    simp only [BONG.weakJordanExpectedOrder] at hraw
    change b.order ⟨ITarget.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          (y.indexEquiv ITarget).1))
        (D.smallAlmostJordan.effectiveNormOrderAt
          (y.indexEquiv ITarget).1
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv ITarget).1)))
        ((y.indexEquiv ITarget).2.val - 1) at hraw
    rw [hsmallScale] at hraw
    change b.order ISource = _
    convert hraw using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        dsimp only [ISource, ITarget, Fin.val_mk] <;>
          have := i.one_lt <;> omega
  have hsmallLocalLast : (y.indexEquiv ITarget).2.val + 1 =
      commonRank := by
    rw [← hcoordinates.2]
    exact htargetLast
  have hsourceOrderGe : scale ≤ b.order ISource := by
    rw [hsourceOrder]
    by_cases heq : scale = smallEffective
    · rw [heq, JordanProfileOrder.localOrder_of_proper]
    · have hstrict : scale < smallEffective :=
        lt_of_le_of_ne hscaleEffective heq
      have hrankEvenRaw :=
        D.smallCommon_componentRank_even_of_scale_lt_effective c (by
          simpa only [hsmallPosition, smallEffective, scale, hscale] using hstrict)
      have hrankEven : Even commonRank := by
        simpa only [D.smallAlmostJordan_finrank_common, commonRank] using
          hrankEvenRaw
      have hlocalEven : Even ((y.indexEquiv ITarget).2.val - 1) := by
        rcases hrankEven with ⟨r, hr⟩
        refine ⟨r - 1, ?_⟩
        omega
      rw [JordanProfileOrder.localOrder_even_of_scale_le
        hscaleEffective hlocalEven]
      exact hscaleEffective
  have hstrictTrigger : b.order ISource < a.order INext := by
    simpa only [ISource, INext] using htrigger.1
  rw [hnextOrder] at hstrictTrigger
  exact (not_lt_of_ge hsourceOrderGe hstrictTrigger)

set_option maxHeartbeats 0 in
/-- The aligned specialization of the collision-left penultimate
contradiction. -/
theorem collisionLeft_not_centralTrigger_of_targetPenultimate_notFirst
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val + 2 = R.coordinates.stop)
    (hnotFirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeCollisionLeftCoordinateResolution
        c hscale a I hposition
      I.val ≠ R.coordinates.start) : False := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hcoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  exact D.collisionLeft_not_centralTrigger_of_targetPenultimate_notFirst_of_prefixAlignment
    c hscale a b i htrigger hfin
      (by simpa only [ITarget] using hcoordinates)
      (D.commonPositions_eq_of_selectedPositions_eq hselected c).symm
      hposition hpenultimate hnotFirst

set_option maxHeartbeats 0 in
theorem weakAligned_centralCertificate_of_collisionLeft
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
          D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  have htargetPosition : (x.indexEquiv ITarget).1 =
      D.largeCommonPosition c := by
    simpa only [x, ITarget] using hposition
  let Rtarget := D.largeCollisionLeftCoordinateResolution
    c hscale a ITarget htargetPosition
  have hendpoints := a.centralTrigger_targetResolvedEndpointTrichotomy
    hdefect i htrigger ITarget (by rfl) Rtarget
  let commonRank := finrank K (D.complementStrictWeak.component c).carrier
  have hcommonRankPos : 0 < commonRank := by
    exact D.complementStrictWeak.component_finrank_pos c
  have hlocalLt : (x.indexEquiv ITarget).2.val < commonRank := by
    have hraw := (x.indexEquiv ITarget).2.isLt
    have htargetWeakRank : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier =
          commonRank := by
      rw [htargetPosition, D.largeAlmostJordan_finrank_common]
    omega
  have hindex := Rtarget.index_val_eq_coordinates_start_add_local
  have hstop : Rtarget.coordinates.stop = Rtarget.coordinates.start +
      Rtarget.jordan.componentRank Rtarget.component := rfl
  have hresolvedLocal : (Rtarget.profile.indexEquiv ITarget).2.val =
      (x.indexEquiv ITarget).2.val := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [show Rtarget.localCoordinateOffset = 0 by rfl, Nat.zero_add] at hlocal
    exact hlocal
  have hindexX : ITarget.val = Rtarget.coordinates.start +
      (x.indexEquiv ITarget).2.val := by
    calc
      ITarget.val = Rtarget.coordinates.start +
          (Rtarget.profile.indexEquiv ITarget).2.val := hindex
      _ = Rtarget.coordinates.start +
          (x.indexEquiv ITarget).2.val := by rw [hresolvedLocal]
  rcases D.rank_one_or_two with hOne | hTwo
  · have hrank : Rtarget.jordan.componentRank Rtarget.component =
        commonRank + 1 := by
      simpa only [commonRank, hOne, Nat.add_comm] using
        D.largeCollisionLeftCoordinateResolution_rank
          c hscale a ITarget htargetPosition
    rcases hendpoints with hfirst | hlast | hpenultimate
    · by_cases hrankTwo :
          Rtarget.jordan.componentRank Rtarget.component = 2
      · exact D.weakAligned_centralCertificate_of_collisionLeft_targetFirst_rank_two
          hselected c hscale a b hdefect i htrigger hOne hposition
            hfirst hrankTwo
      · have hrankHigh : 2 <
            Rtarget.jordan.componentRank Rtarget.component := by
          omega
        exact D.weakAligned_centralCertificate_of_collisionLeft_targetFirst_highRank
          hselected c hscale a b hdefect i htrigger htargetBefore
            hposition hfirst hrankHigh
    · exfalso
      omega
    · by_cases hfirst : ITarget.val = Rtarget.coordinates.start
      · have hrankTwo :
            Rtarget.jordan.componentRank Rtarget.component = 2 := by
          omega
        exact D.weakAligned_centralCertificate_of_collisionLeft_targetFirst_rank_two
          hselected c hscale a b hdefect i htrigger hOne hposition
            hfirst hrankTwo
      · exact False.elim
          (D.collisionLeft_not_centralTrigger_of_targetPenultimate_notFirst
            hselected c hscale a b i htrigger hOne hposition
              hpenultimate hfirst)
  · have hrank : Rtarget.jordan.componentRank Rtarget.component =
        commonRank + 2 := by
      simpa only [commonRank, hTwo, Nat.add_comm] using
        D.largeCollisionLeftCoordinateResolution_rank
          c hscale a ITarget htargetPosition
    rcases hendpoints with hfirst | hlast | hpenultimate
    · have hrankHigh : 2 <
          Rtarget.jordan.componentRank Rtarget.component := by
        omega
      exact D.weakAligned_centralCertificate_of_collisionLeft_targetFirst_highRank
        hselected c hscale a b hdefect i htrigger htargetBefore
          hposition hfirst hrankHigh
    · exfalso
      omega
    · exfalso
      omega

end Lattice.Beli2019Lemma51Data

end Bong
