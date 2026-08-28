/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralDirect
import Bong.Bong.Beli2019SectionFiveCentralCarriers
import Bong.Bong.Beli2019TernaryGeneratorChoice
import Bong.Lattice.Omeara9315TernaryGenerators

/-!
# High-rank central representation cases in Beli (2019), Section 5

This file realizes the ordinary adjacency in which the source coordinate is
penultimate in a resolved component and the target coordinate is the full
boundary after that component.  A prefix of rank at least four represents
the fundamental line unconditionally.
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

set_option maxHeartbeats 0 in
/-- A source approximation model contained in a resolved target boundary
model gives the required central prefix representation. -/
theorem centralCertificate_of_sourceModel_to_boundary
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    {t : Nat} {W : Lattice.WeakJordanDecomposition q M t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    (Rtarget : BONG.StrictBoundaryResolution a W x
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (source : BONG.GoodBONG.SpaceApproximationModel b
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hcarrier : source.carrier ≤ Rtarget.lemma37Model_i.carrier) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger Rtarget.lemma37Model_i source hcarrier)

set_option maxHeartbeats 0 in
/-- Two consecutive ordinary weak boundaries give nested Lemma 3.7(i)
models.  This is the rank-one specialization of the source-last/target-first
adjacency, and is also useful whenever the target coordinate is terminal
for an independent reason. -/
theorem centralCertificate_of_weakBoundaries_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (htargetCoordinates :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (hprefixCarriers : ∀ k, k ≤ D.largeSelectedPosition.val →
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier k =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier k)
    (hsourceLast :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val + 1 =
      finrank K (D.smallAlmostJordan.component
        ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1).carrier)
    (htargetLast :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1).carrier)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  change (y.indexEquiv gSource.castSucc).1 <
    D.smallSelectedPosition at hsourceBefore
  change (x.indexEquiv gTarget.castSucc).1 <
    D.largeSelectedPosition at htargetBefore
  change (y.indexEquiv gSource.castSucc).2.val + 1 =
    finrank K (D.smallAlmostJordan.component
      (y.indexEquiv gSource.castSucc).1).carrier at hsourceLast
  change (x.indexEquiv gTarget.castSucc).2.val + 1 =
    finrank K (D.largeAlmostJordan.component
      (x.indexEquiv gTarget.castSucc).1).carrier at htargetLast
  change ¬ ∃ c : Fin D.complementComponentCount,
    ordUnit K (D.complementStrictWeak.scaleGenerator c) =
        ordUnit K D.input.block.enlargedScaleGenerator ∧
      (x.indexEquiv gTarget.castSucc).1 =
        D.largeCommonPosition c at hnotCollisionLeft
  have htargetCoordinates' :
      (x.indexEquiv gTarget.castSucc).1 =
          (y.indexEquiv gTarget.castSucc).1 ∧
        (x.indexEquiv gTarget.castSucc).2.val =
          (y.indexEquiv gTarget.castSucc).2.val := by
    simpa only [x, y, gTarget, Fin.castSucc_mk] using htargetCoordinates
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y] using hsourceBefore)
      (by simpa only [y] using hsourceLast)
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution
    a gTarget (by simpa only [x] using htargetBefore)
      (by simpa only [x] using htargetLast)
      (by simpa only [x] using hnotCollisionLeft)
  have hcut : Rsource.weakNext.val ≤ Rtarget.weakNext.val := by
    rw [Rsource.weakNext_val, Rtarget.weakNext_val]
    have hsourceTarget :=
      (D.smallWeakProfileWitness b).indexEquiv_global_succ_of_terminal
        gSource.castSucc gTarget.castSucc (by
          dsimp only [gSource, gTarget, Fin.castSucc_mk, Fin.val_mk]
          have hiOne := i.one_lt
          omega) hsourceLast
    have hcomponentEq := congrArg Fin.val htargetCoordinates'.1
    have hsourceTargetVal := hsourceTarget.1
    change (y.indexEquiv gTarget.castSucc).1.val =
      (y.indexEquiv gSource.castSucc).1.val + 1 at hsourceTargetVal
    change (x.indexEquiv gTarget.castSucc).1.val =
      (y.indexEquiv gTarget.castSucc).1.val at hcomponentEq
    change (y.indexEquiv gSource.castSucc).1.val + 1 ≤
      (x.indexEquiv gTarget.castSucc).1.val + 1
    omega
  have hcarrier : Rsource.lemma37Model_i.carrier ≤
      Rtarget.lemma37Model_i.carrier := by
    have htargetCutLe : Rtarget.weakNext.val ≤
        D.largeSelectedPosition.val := by
      rw [Rtarget.weakNext_val]
      change (x.indexEquiv gTarget.castSucc).1.val + 1 ≤
        D.largeSelectedPosition.val
      change (x.indexEquiv gTarget.castSucc).1.val <
        D.largeSelectedPosition.val at htargetBefore
      omega
    have hsourceCutLe : Rsource.weakNext.val ≤
        D.largeSelectedPosition.val := hcut.trans htargetCutLe
    have haligned := hprefixCarriers Rsource.weakNext.val hsourceCutLe
    rw [Rsource.lemma37Model_i_carrier_eq,
      Rtarget.lemma37Model_i_carrier_eq,
      ← haligned]
    exact D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono hcut
  exact centralCertificate_of_sourceModel_to_boundary
    a b hdefect i htrigger Rtarget Rsource.lemma37Model_i hcarrier

set_option maxHeartbeats 0 in
/-- The source-last/target-first adjacency with a unary target component
reduces to two weak boundaries, hence to nested case-(i) models. -/
theorem centralCertificate_of_sourceLast_targetFirst_rank_one_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (htargetCoordinates :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (hprefixCarriers : ∀ k, k ≤ D.largeSelectedPosition.val →
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier k =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier k)
    (hsourceLast :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 1 = R.coordinates.stop)
    (htargetFirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrankOne :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 1)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ISource.val + 1 = Rsource.coordinates.stop at hsourceLast
  change ITarget.val = Rtarget.coordinates.start at htargetFirst
  change Rtarget.jordan.componentRank Rtarget.component = 1 at hrankOne
  have hsourceOffset : Rsource.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b ISource hsourceBefore.le
  have hsourceComponent : Rsource.strictWeak.component Rsource.component =
      D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
    simpa only [Rsource, y] using
      D.smallStrictCoordinateResolution_component_eq_of_lt
        b ISource hsourceBefore.le (by
          simpa only [y, ISource] using hsourceBefore)
  have hsourceCoordinates :=
    Rsource.coordinates_eq_weak_of_offset_zero_of_component_eq
      hsourceOffset hsourceComponent
  have hsourceGlobal := y.index_val_eq_componentStart_add_local ISource
  change ISource.val = y.componentStart (y.indexEquiv ISource).1 +
    (y.indexEquiv ISource).2.val at hsourceGlobal
  have hsourceWeakLast : (y.indexEquiv ISource).2.val + 1 =
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv ISource).1).carrier := by
    have hstopFormula : y.componentStop (y.indexEquiv ISource).1 =
        y.componentStart (y.indexEquiv ISource).1 +
          finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ISource).1).carrier := by rfl
    have hstop : Rsource.coordinates.stop =
        y.componentStop (y.indexEquiv ISource).1 := by
      simpa only [y] using hsourceCoordinates.2
    rw [hstop, hstopFormula] at hsourceLast
    omega
  have htargetOffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le (by
        simpa only [x, ITarget] using htargetBefore)
  have htargetComponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le (by
          simpa only [x, ITarget] using htargetBefore) (by
            simpa only [x, ITarget] using hnotCollisionLeft)
  have hresolvedTargetCoordinates :=
    Rtarget.coordinates_eq_weak_of_offset_zero_of_component_eq
      htargetOffset htargetComponent
  have htargetGlobal := x.index_val_eq_componentStart_add_local ITarget
  change ITarget.val = x.componentStart (x.indexEquiv ITarget).1 +
    (x.indexEquiv ITarget).2.val at htargetGlobal
  have htargetWeakFirst : (x.indexEquiv ITarget).2.val = 0 := by
    have hstart : Rtarget.coordinates.start =
        x.componentStart (x.indexEquiv ITarget).1 := by
      simpa only [x] using hresolvedTargetCoordinates.1
    rw [hstart] at htargetFirst
    omega
  have htargetWeakRank : finrank K (D.largeAlmostJordan.component
      (x.indexEquiv ITarget).1).carrier = 1 := by
    change finrank K (Rtarget.strictWeak.component Rtarget.component).carrier = 1
      at hrankOne
    rw [htargetComponent] at hrankOne
    exact hrankOne
  have htargetWeakLast : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by omega
  exact D.centralCertificate_of_weakBoundaries_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore htargetCoordinates
      hprefixCarriers
      (by simpa only [y, ISource] using hsourceWeakLast)
      (by simpa only [x, ITarget] using htargetWeakLast) hnotCollisionLeft

set_option maxHeartbeats 0 in
/-- The aligned specialization of the unary-target weak-boundary branch. -/
theorem weakAligned_centralCertificate_of_sourceLast_targetFirst_rank_one
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hsourceLast :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 1 = R.coordinates.stop)
    (htargetFirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrankOne :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 1)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hcoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  exact D.centralCertificate_of_sourceLast_targetFirst_rank_one_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore
      (by simpa only [ITarget] using hcoordinates)
      (fun k _hk => D.aligned_prefixCarrier_eq hselected k)
      hsourceLast htargetFirst hrankOne hnotCollisionLeft

set_option maxHeartbeats 0 in
/-- In the aligned direct range, a source penultimate coordinate has a
strict two-step rise to its next component.  Indeed that next coordinate is
local zero, so Section 5.4 gives the direct order inequality there; the
first central-trigger inequality then makes the source rise strict.  This
is the collision-safe form of the paper's exclusion of Lemma 3.7(ii). -/
theorem weakAligned_source_rightTwoStep_lt_of_penultimate
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop) :
    b.order ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩ := by
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let IBoundary : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  have hterminal := D.smallWeak_globalSucc_terminal_of_strictPenultimate
    b ISource IBoundary hsourceBefore.le hsourceBefore (by
      dsimp only [ISource, IBoundary, gSource, Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega) hpenultimate
  have hnext := y.indexEquiv_global_succ_of_terminal
    IBoundary INext (by
      dsimp only [IBoundary, INext, Fin.val_mk]
      have := i.one_lt
      omega) (by simpa only [y] using hterminal.2)
  have hsmallNextLe : (y.indexEquiv INext).1 ≤
      D.smallSelectedPosition := by
    have hsourceBefore' := hsourceBefore
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val at hsourceBefore'
    have hterminal' : (y.indexEquiv IBoundary).1 =
        (y.indexEquiv ISource).1 := by
      simpa only [y] using hterminal.1
    have hterminalComponent := congrArg Fin.val hterminal'
    have hnextComponent := hnext.1
    change (y.indexEquiv INext).1.val ≤ D.smallSelectedPosition.val
    omega
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b INext
  have hcoordinates :
      (x.indexEquiv INext).1 = (y.indexEquiv INext).1 ∧
        (x.indexEquiv INext).2.val = (y.indexEquiv INext).2.val := by
    simpa only [x, y] using hcoordinatesRaw
  have hlargeNextLe : (x.indexEquiv INext).1 ≤
      D.largeSelectedPosition := by
    have hcomponentVal := congrArg Fin.val hcoordinates.1
    have hselectedVal := congrArg Fin.val hselected
    change (x.indexEquiv INext).1.val ≤ D.largeSelectedPosition.val
    change (y.indexEquiv INext).1.val ≤
      D.smallSelectedPosition.val at hsmallNextLe
    omega
  have hlargeNextEven : Even (x.indexEquiv INext).2.val := by
    rw [hcoordinates.2, hnext.2]
    exact Even.zero
  have hdirect : a.order INext ≤ b.order INext :=
    D.weakAligned_order_le_of_component_le_selected_of_local_even
      hselected a b INext hlargeNextLe hlargeNextEven
  unfold BONG.GoodBONG.centralAlphaTrigger at htrigger
  simpa only [INext] using htrigger.1.trans_le hdirect

set_option maxHeartbeats 0 in
/-- Away from the unique large-side collision, two consecutive resolved
central coordinates have exactly the three adjacency patterns used in
Section 5.14: source penultimate/target last, source last/target first, or
source first/target penultimate. -/
theorem weakAligned_central_endpoint_pair_trichotomy
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i)
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
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
    let hbounds := D.weakAligned_central_component_bounds
      hselected a b i hrange
    let Rtarget := D.largeStrictCoordinateResolution a ITarget hbounds.1
    let Rsource := D.smallStrictCoordinateResolution b ISource hbounds.2
    ((ISource.val + 2 = Rsource.coordinates.stop ∧
        ITarget.val + 1 = Rtarget.coordinates.stop) ∨
      (ISource.val + 1 = Rsource.coordinates.stop ∧
        ITarget.val = Rtarget.coordinates.start) ∨
      (ISource.val = Rsource.coordinates.start ∧
        ITarget.val + 2 = Rtarget.coordinates.stop ∧
        (y.indexEquiv ISource).1 = (y.indexEquiv ITarget).1 ∧
        Rsource.jordan.componentRank Rsource.component = 3 ∧
        Rtarget.jordan.componentRank Rtarget.component = 3)) := by
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
  let hbounds := D.weakAligned_central_component_bounds
    hselected a b i hrange
  let Rtarget := D.largeStrictCoordinateResolution a ITarget hbounds.1
  let Rsource := D.smallStrictCoordinateResolution b ISource hbounds.2
  have hpositions := D.weakAligned_central_strict_source_and_target_position
    hselected a b i hrange
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    simpa only [y, ISource, gSource] using hpositions.1
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using htargetBefore
  have hsourceOffset : Rsource.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b ISource hbounds.2
  have hsourceComponent : Rsource.strictWeak.component Rsource.component =
      D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
    simpa only [Rsource, y] using
      D.smallStrictCoordinateResolution_component_eq_of_lt
        b ISource hbounds.2 hsourceBefore
  have hsourceCoordinates :=
    Rsource.coordinates_eq_weak_of_offset_zero_of_component_eq
      hsourceOffset hsourceComponent
  have hsourceStart : Rsource.coordinates.start =
      y.componentStart (y.indexEquiv ISource).1 := by
    simpa only [y] using hsourceCoordinates.1
  have hsourceStop : Rsource.coordinates.stop =
      y.componentStop (y.indexEquiv ISource).1 := by
    simpa only [y] using hsourceCoordinates.2
  have htargetOffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget hbounds.1 htargetBefore'
  have htargetComponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget hbounds.1 htargetBefore' (by
          simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using
            hnotCollisionLeft)
  have htargetCoordinatesX :=
    Rtarget.coordinates_eq_weak_of_offset_zero_of_component_eq
      htargetOffset htargetComponent
  have hxyTargetRaw := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hxyTarget :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hxyTargetRaw
  have htargetStartXY :
      x.componentStart (x.indexEquiv ITarget).1 =
        y.componentStart (y.indexEquiv ITarget).1 := by
    rw [hxyTarget.1]
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k _hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  have htargetRankXY :
      finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ITarget).1).carrier := by
    have hrank := congrFun (D.almostJordan_componentRank_eq hselected)
      (x.indexEquiv ITarget).1
    calc
      finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
          finrank K (D.smallAlmostJordan.component
            (x.indexEquiv ITarget).1).carrier := hrank
      _ = finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ITarget).1).carrier := by rw [hxyTarget.1]
  have htargetStopXY :
      x.componentStop (x.indexEquiv ITarget).1 =
        y.componentStop (y.indexEquiv ITarget).1 := by
    change x.componentStart (x.indexEquiv ITarget).1 +
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
      y.componentStart (y.indexEquiv ITarget).1 +
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ITarget).1).carrier
    rw [htargetStartXY, htargetRankXY]
  have htargetCoordinates :
      Rtarget.coordinates.start =
          y.componentStart (y.indexEquiv ITarget).1 ∧
        Rtarget.coordinates.stop =
          y.componentStop (y.indexEquiv ITarget).1 :=
    ⟨htargetCoordinatesX.1.trans htargetStartXY,
      htargetCoordinatesX.2.trans htargetStopXY⟩
  have hsourceGlobal := y.index_val_eq_componentStart_add_local ISource
  change ISource.val = y.componentStart (y.indexEquiv ISource).1 +
    (y.indexEquiv ISource).2.val at hsourceGlobal
  have hsourceStopFormula : y.componentStop (y.indexEquiv ISource).1 =
      y.componentStart (y.indexEquiv ISource).1 +
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ISource).1).carrier := by
    rfl
  have htargetGlobal := y.index_val_eq_componentStart_add_local ITarget
  change ITarget.val = y.componentStart (y.indexEquiv ITarget).1 +
    (y.indexEquiv ITarget).2.val at htargetGlobal
  have hsucc : ITarget.val = ISource.val + 1 := by
    dsimp only [ITarget, ISource, gTarget, gSource,
      Fin.castSucc_mk, Fin.val_mk]
    have hiOne := i.one_lt
    omega
  have htargetEndpoints := a.centralTrigger_targetResolvedEndpointTrichotomy
    hdefect i htrigger ITarget (by rfl) Rtarget
  have hsourceEndpoints := a.centralTrigger_sourceResolvedEndpointTrichotomy
    hdefect i htrigger ISource (by rfl) Rsource
  by_cases hinternal : (y.indexEquiv ISource).2.val + 1 <
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv ISource).1).carrier
  · have hnext := y.indexEquiv_global_succ_eq_local_succ
      ISource ITarget hsucc hinternal
    have hcomponentST : (y.indexEquiv ITarget).1 =
        (y.indexEquiv ISource).1 := by
      simpa only using congrArg Sigma.fst hnext
    have hlocalST : (y.indexEquiv ITarget).2.val =
        (y.indexEquiv ISource).2.val + 1 := by
      simpa only [Fin.val_mk] using congrArg (fun z ↦ z.2.val) hnext
    have hstartST : y.componentStart (y.indexEquiv ITarget).1 =
        y.componentStart (y.indexEquiv ISource).1 := by rw [hcomponentST]
    have hstopST : y.componentStop (y.indexEquiv ITarget).1 =
        y.componentStop (y.indexEquiv ISource).1 := by rw [hcomponentST]
    have hresolvedStartEq : Rtarget.coordinates.start =
        Rsource.coordinates.start :=
      htargetCoordinates.1.trans (hstartST.trans hsourceStart.symm)
    have hresolvedStopEq : Rtarget.coordinates.stop =
        Rsource.coordinates.stop :=
      htargetCoordinates.2.trans (hstopST.trans hsourceStop.symm)
    rcases hsourceEndpoints with hsourceFirst | hsourceLast | hsourcePenultimate
    · rcases htargetEndpoints with htargetFirst | htargetLast |
          htargetPenultimate
      · exfalso
        rw [hsourceStart] at hsourceFirst
        rw [htargetCoordinates.1] at htargetFirst
        omega
      · left
        refine ⟨?_, htargetLast⟩
        calc
          ISource.val + 2 = ITarget.val + 1 := by omega
          _ = Rtarget.coordinates.stop := htargetLast
          _ = Rsource.coordinates.stop := hresolvedStopEq
      · have hsourceRank :
            Rsource.jordan.componentRank Rsource.component = 3 := by
          have hstopFormula : Rsource.coordinates.stop =
              Rsource.coordinates.start +
                Rsource.jordan.componentRank Rsource.component := rfl
          omega
        have htargetRank :
            Rtarget.jordan.componentRank Rtarget.component = 3 := by
          have hstopFormula : Rtarget.coordinates.stop =
              Rtarget.coordinates.start +
                Rtarget.jordan.componentRank Rtarget.component := rfl
          omega
        exact Or.inr (Or.inr
          ⟨hsourceFirst, htargetPenultimate, hcomponentST.symm,
            hsourceRank, htargetRank⟩)
    · exfalso
      rw [hsourceStop, hsourceStopFormula] at hsourceLast
      omega
    · left
      refine ⟨hsourcePenultimate, ?_⟩
      calc
        ITarget.val + 1 = ISource.val + 2 := by omega
        _ = Rsource.coordinates.stop := hsourcePenultimate
        _ = Rtarget.coordinates.stop := hresolvedStopEq.symm
  · have hsourceTerminal : (y.indexEquiv ISource).2.val + 1 =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv ISource).1).carrier := by
      have hbound := (y.indexEquiv ISource).2.isLt
      omega
    have hnext := y.indexEquiv_global_succ_of_terminal
      ISource ITarget hsucc hsourceTerminal
    right
    left
    constructor
    · rw [hsourceStop, hsourceStopFormula]
      change ISource.val + 1 =
        y.componentStart (y.indexEquiv ISource).1 +
          finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ISource).1).carrier
      omega
    · rw [htargetCoordinates.1]
      rw [htargetGlobal, hnext.2, Nat.add_zero]

set_option maxHeartbeats 0 in
/-- The aligned source-penultimate branch of Lemma 3.7(iii), with its outer
two-step equality kept explicit.  The source complement model lies in the
complete source prefix, which is identified with the carrier of the target
boundary model by the aligned almost-Jordan decomposition. -/
theorem centralCertificate_of_sourcePenultimate_iii_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hsourcePositive : 0 < i.val - 2)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      1 < R.jordan.componentRank R.component)
    (hsourceNext :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.component.val + 1 < R.componentCount)
    (A : Kˣ)
    (hA :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      Lattice.IsNormGeneratorValue q
        (R.jordan.fundamentalLattice R.component) A)
    (hline :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space.Represents
          (QuadraticSpace.scaledLine A))
    (houter : b.order
        ⟨i.val - 3, by have := i.lt_large; omega⟩ =
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1)) →
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  intro hprefixCarrier
  classical
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  change 1 < Rsource.jordan.componentRank Rsource.component at hrank
  change Rsource.component.val + 1 < Rsource.componentCount at hsourceNext
  change Lattice.IsNormGeneratorValue q
    (Rsource.jordan.fundamentalLattice Rsource.component) A at hA
  change (Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    (Rsource.component.val + 1)).space.Represents
      (QuadraticSpace.scaledLine A) at hline
  have houter' : b.order
        ⟨gSource.val - 1, by have := gSource.isLt; omega⟩ =
      b.order ⟨gSource.val + 1, by have := gSource.isLt; omega⟩ := by
    convert houter using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;> dsimp only [gSource, Fin.val_mk] <;> omega
  rcases Rsource.exists_spaceModel_iii_of_penultimate_with_outer
      gSource rfl hsourcePositive hpenultimate hrank hsourceNext A hA hline
        houter'
    with ⟨source, hsourceModelCarrier⟩
  have hsourcePrefix :=
    D.smallStrictCoordinateResolution_prefixCarrier_succ_eq_of_lt
      b ISource hsourceBefore.le hsourceBefore
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hprefixCarrier
  have hweakNext' : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  have hcarrier : source.carrier ≤ Rtarget.lemma37Model_i.carrier := by
    rw [Rtarget.lemma37Model_i_carrier_eq]
    calc
      source.carrier ≤
          Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
            (Rsource.component.val + 1) := hsourceModelCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := hsourcePrefix
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := haligned.symm
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val := by rw [hweakNext']
  exact centralCertificate_of_sourceModel_to_boundary
    a b hdefect i htrigger Rtarget source hcarrier

set_option maxHeartbeats 0 in
/-- In Lemma 3.7(iii), an odd source component supplies its own represented
fundamental norm generator.  This removes the quaternary-universality bound
from the proper rank-three source case. -/
theorem weakAligned_centralCertificate_of_sourcePenultimate_iii_of_odd_component
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hsourcePositive : 0 < i.val - 2)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      1 < R.jordan.componentRank R.component)
    (hodd :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      Odd (R.jordan.componentRank R.component))
    (hsourceNext :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.component.val + 1 < R.componentCount)
    (houter : b.order
        ⟨i.val - 3, by have := i.lt_large; omega⟩ =
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change Odd (Rsource.jordan.componentRank Rsource.component) at hodd
  let G := BONG.RepresentedFundamentalNormGenerator.ofOddComponent
    Rsource.strictWeak Rsource.hasImproperEvenRank
      Rsource.scaleOrder_strict Rsource.component hodd
  apply D.centralCertificate_of_sourcePenultimate_iii_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore hsourcePositive
      hpenultimate hrank hsourceNext G.value G.fundamental
        (G.prefixSpace_represents_scaledLine
          (Nat.lt_succ_self Rsource.component.val)) houter Rtarget
          hweakNext
  exact D.aligned_prefixCarrier_eq hselected
    (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1)

set_option maxHeartbeats 0 in
/-- The binary source-penultimate branch of Lemma 3.7(iv).  The right
two-step inequality is forced by the active central trigger and the aligned
weak profiles; the left strict inequality is kept as the branch hypothesis.
The resulting complement model is contained in the complete source prefix
and hence in the target boundary model. -/
theorem centralCertificate_of_sourcePenultimate_iv_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hsourcePositive : 0 < i.val - 2)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 2)
    (hcomponentPositive :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      0 < R.component.val)
    (hsourceNext :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.component.val + 1 < R.componentCount)
    (hleftOuter : b.order
        ⟨i.val - 3, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (hrightOuter : b.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩)
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1))
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  have hsourcePositive' : 0 < ISource.val := by
    simpa only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk] using
      hsourcePositive
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  change Rsource.jordan.componentRank Rsource.component = 2 at hrank
  change 0 < Rsource.component.val at hcomponentPositive
  change Rsource.component.val + 1 < Rsource.componentCount at hsourceNext
  have hrightBound : ISource.val + 2 < n + 2 := by
    dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
    have hiOne := i.one_lt
    have hiLt := i.lt_large
    omega
  have hleftOuter' : b.order
        ⟨ISource.val - 1, by omega⟩ <
      b.order ⟨ISource.val + 1, by omega⟩ := by
    convert hleftOuter using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk] <;> omega
  have hrightOuterLocal : b.order ISource <
      b.order ⟨ISource.val + 2, hrightBound⟩ := by
    convert hrightOuter using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk] <;> omega
  rcases Rsource.exists_spaceModel_iv_of_binary_penultimate
      gSource rfl hsourcePositive' hpenultimate hrank hcomponentPositive
        hsourceNext hrightBound hleftOuter' hrightOuterLocal
    with ⟨source, hsourceModelCarrier⟩
  have hsourcePrefix :=
    D.smallStrictCoordinateResolution_prefixCarrier_succ_eq_of_lt
      b ISource hsourceBefore.le hsourceBefore
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hprefixCarrier
  have hweakNext' : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  have hcarrier : source.carrier ≤ Rtarget.lemma37Model_i.carrier := by
    rw [Rtarget.lemma37Model_i_carrier_eq]
    calc
      source.carrier ≤
          Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
            (Rsource.component.val + 1) := hsourceModelCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := hsourcePrefix
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := haligned.symm
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val := by rw [hweakNext']
  exact centralCertificate_of_sourceModel_to_boundary
    a b hdefect i htrigger Rtarget source hcarrier

set_option maxHeartbeats 0 in
/-- The aligned high-rank `3.7(iii) -> 3.7(i)` branch of condition
2.1(iii).  All cross-lattice geometry is reduced to the equality of the
two almost-Jordan prefix carriers. -/
theorem centralCertificate_of_sourcePenultimate_four_le_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hsourcePositive : 0 < i.val - 2)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      2 < R.jordan.componentRank R.component)
    (hsourceNext :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.component.val + 1 < R.componentCount)
    (hfour :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      4 ≤ finrank K
        (R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1)))
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1)) →
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  intro hprefixCarrier
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  change 2 < Rsource.jordan.componentRank Rsource.component at hrank
  change Rsource.component.val + 1 < Rsource.componentCount at hsourceNext
  change 4 ≤ finrank K
    (Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
      (Rsource.component.val + 1)) at hfour
  have hsourceCarrier :=
    D.smallStrictCoordinateResolution_prefixCarrier_succ_eq_of_lt
      b ISource hsourceBefore.le hsourceBefore
  have hweakNext' : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  have htargetCarrier :
      (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rtarget.boundary.val + 1) =
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.weakNext.val := by
    rw [← Rtarget.jordan_eq]
    exact Rtarget.prefixCarrier_eq
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hprefixCarrier
  have hcarrier :
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          (Rsource.component.val + 1) =
        (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
            (Rtarget.boundary.val + 1) := by
    calc
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          (Rsource.component.val + 1) =
          D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := hsourceCarrier
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := haligned.symm
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val := by rw [hweakNext']
      _ = (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixCarrier
              (Rtarget.boundary.val + 1) := htargetCarrier.symm
  let C := Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    (Rsource.component.val + 1)
  let E := (Rtarget.strictWeak.toJordan Rtarget.scaleOrder_strict).toOrthogonalDecomposition.prefixQuadraticSublattice
      (Rtarget.boundary.val + 1)
  have hprefix : QuadraticSpace.Isometry C.space E.space :=
    C.spaceIsometryOfCarrierEq E hcarrier
  let A := Rsource.jordan.fundamentalNormGenerator Rsource.component
  have hA : Lattice.IsNormGeneratorValue q
      (Rsource.jordan.fundamentalLattice Rsource.component) A :=
    Rsource.jordan.fundamentalNormGenerator_spec Rsource.component
  letI : Module.Finite K V := N.moduleFinite
  change 4 ≤ finrank K C.carrier at hfour
  have hline : C.space.Represents (QuadraticSpace.scaledLine A) :=
    C.space.represents_scaledLine_of_four_le_finrank A hfour
  rcases Rsource.exists_diagonalModel_iii_of_penultimate_with_representation
      gSource rfl hsourcePositive hpenultimate hrank hsourceNext A hA
        (by simpa only [C] using hline) Rtarget.strictProfile Rtarget.boundary
          (by simpa only [C, E] using hprefix)
    with ⟨source, hrep, _hstruct⟩
  let targetBase :=
    BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
      a Rtarget.strictWeak Rtarget.hasImproperEvenRank
        Rtarget.scaleOrder_strict Rtarget.strictProfile Rtarget.boundary
  let targetSpace : BONG.GoodBONG.SpaceApproximationModel a gTarget :=
    targetBase.castIndex Rtarget.strictProfile_boundaryIndex_eq
  let target := targetSpace.toDiagonal
  have hmodels : DiagonalRepresents
      (diagonalUnitCoefficients source.units)
      (diagonalUnitCoefficients target.units) := by
    exact targetBase.castIndex_diagonalRepresentedBy
      Rtarget.strictProfile_boundaryIndex_eq hrep
  exact .represented
    (target.centralRepresentation a b hdefect i htrigger source hmodels)

set_option maxHeartbeats 0 in
/-- The other ordinary aligned adjacency: a complete source boundary is
represented by the target prefix with one fundamental line appended. -/
theorem centralCertificate_of_sourceBoundary_targetFirst_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      2 < R.jordan.componentRank R.component)
    (Rsource : BONG.StrictBoundaryResolution b D.smallAlmostJordan
      (D.smallWeakProfileWitness b)
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rsource.weakNext.val =
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val)
    (hprefixCarrier :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val)) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let x := D.largeWeakProfileWitness a
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change 2 < Rtarget.jordan.componentRank Rtarget.component at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero hoffset
  have hweakNext' : Rsource.weakNext.val = (x.indexEquiv ITarget).1.val := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hweakNext
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
            (x.indexEquiv ITarget).1.val := by rw [hweakNext']
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
/-- The aligned specialization of the target-first high-rank carrier
argument. -/
theorem weakAligned_centralCertificate_of_sourceBoundary_targetFirst
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      2 < R.jordan.componentRank R.component)
    (Rsource : BONG.StrictBoundaryResolution b D.smallAlmostJordan
      (D.smallWeakProfileWitness b)
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rsource.weakNext.val =
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hprefix := D.aligned_prefixCarrier_eq hselected
    ((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val
  exact D.centralCertificate_of_sourceBoundary_targetFirst_of_prefixAlignment
    a b hdefect i htrigger htargetBefore hfirst hrank Rsource hweakNext
      (by simpa only [ITarget] using hprefix)

set_option maxHeartbeats 0 in
/-- For a binary target block beginning immediately after a source boundary,
the strict left outer comparison leaves exactly cases 3.7(ii) and 3.7(iv).
The equality/right branch uses the abstract diagonal case-(ii) model; the
strict/right branch uses the concrete prefix-plus-line member of the
case-(iv) pair, whose carrier contains the preceding target prefix. -/
theorem centralCertificate_of_sourceBoundary_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (Rsource : BONG.StrictBoundaryResolution b D.smallAlmostJordan
      (D.smallWeakProfileWitness b)
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rsource.weakNext.val =
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val)
    (hprefixCarrier :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val))
    (hleftOuter : a.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let x := D.largeWeakProfileWitness a
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change Rtarget.jordan.componentRank Rtarget.component = 2 at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have htargetCarrier :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero hoffset
  have hweakNext' : Rsource.weakNext.val = (x.indexEquiv ITarget).1.val := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hweakNext
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
            (x.indexEquiv ITarget).1.val := by rw [hweakNext']
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            (x.indexEquiv ITarget).1.val := haligned.symm
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.component.val := htargetCarrier.symm
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have hi := i.one_lt
    omega
  have hpenultimate : ITarget.val + 2 = Rtarget.coordinates.stop := by
    have hstopFormula : Rtarget.coordinates.stop =
        Rtarget.coordinates.start +
          Rtarget.jordan.componentRank Rtarget.component := by
      rfl
    omega
  have hcomponentPositive : 0 < Rtarget.component.val :=
    Rtarget.component_pos_of_first_of_positive htargetPositive hfirst
  have hcomponentNext : Rtarget.component.val + 1 <
      Rtarget.componentCount := by
    have hraw :=
      D.largeStrictCoordinateResolution_component_succ_lt_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le (by
          simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using htargetBefore)
          (by simpa only [x, ITarget, gTarget, Fin.castSucc_mk]
            using hnotCollisionLeft)
    simpa only [Rtarget] using hraw
  have hrightBound : ITarget.val + 2 < n + 2 := by
    rw [hpenultimate]
    exact Rtarget.coordinates_stop_lt_of_component_succ hcomponentNext
  have hleftOuter' : a.order ⟨ITarget.val - 1, by omega⟩ <
      a.order ⟨ITarget.val + 1, by omega⟩ := by
    have hleftIndex :
        (⟨ITarget.val - 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val - 2, by have := i.lt_large; omega⟩ := by
      apply Fin.ext
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      have hi := i.one_lt
      omega
    have hrightIndex :
        (⟨ITarget.val + 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      have hi := i.one_lt
      omega
    rw [hleftIndex, hrightIndex]
    exact hleftOuter
  have hrightLe : a.order ITarget ≤
      a.order ⟨ITarget.val + 2, hrightBound⟩ := by
    exact a.good ITarget hrightBound
  rcases lt_or_eq_of_le hrightLe with hrightOuter | hrightOuter
  · rcases Rtarget.exists_leftSpaceModel_iv_of_binary_penultimate
        gTarget rfl htargetPositive hpenultimate hrank hcomponentPositive
          hcomponentNext hrightBound hleftOuter' hrightOuter
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
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk] at hrightBound
      omega
    have houter : a.order gTarget.castSucc =
        a.order (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
      have hleftIndex : gTarget.castSucc = ITarget := rfl
      have hrightIndex :
          (⟨gTarget.val + 1, hinternal⟩ : Fin (n + 1)).succ =
            ⟨ITarget.val + 2, hrightBound⟩ := by
        apply Fin.ext
        rfl
      rw [hleftIndex, hrightIndex]
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
    let sourceSpace : BONG.GoodBONG.SpaceApproximationModel b
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) :=
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
/-- The aligned specialization of the binary target-first carrier
argument. -/
theorem weakAligned_centralCertificate_of_sourceBoundary_targetFirst_rank_two_of_left_lt
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (Rsource : BONG.StrictBoundaryResolution b D.smallAlmostJordan
      (D.smallWeakProfileWitness b)
      (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rsource.weakNext.val =
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val)
    (hleftOuter : a.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hprefix := D.aligned_prefixCarrier_eq hselected
    ((D.largeWeakProfileWitness a).indexEquiv ITarget).1.val
  exact D.centralCertificate_of_sourceBoundary_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    a b hdefect i htrigger htargetBefore hfirst hrank hnotCollisionLeft
      Rsource hweakNext (by simpa only [ITarget] using hprefix) hleftOuter

set_option maxHeartbeats 0 in
/-- Before the selected block, a binary target component beginning at the
central target coordinate forces the two-step large-side order comparison to
be strict.  Indeed, equality would turn the central trigger into a strict
effective-norm comparison on the preceding common component.  Propagation to
the binary component makes both large effective norms equal to the selected
norm, while the two component scales are strictly increasing, contradicting
the last-coordinate formulas.  This eliminates Beli's case 3.7(iii) away from
the selected binary exception. -/
theorem targetFirst_rank_two_leftOuter_lt_of_notCollision_of_prefixAlignment
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    (htargetCoordinatesInput :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val) →
    (hsourceCoordinatesInput :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ISource).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ISource).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ISource).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ISource).2.val) →
    (hscaleAlignment : ∀ p, p < D.largeSelectedPosition →
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator p)) →
    a.order (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2)) <
      a.order ⟨i.val, i.lt_large⟩ := by
  intro htargetCoordinatesInput hsourceCoordinatesInput hscaleAlignment
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
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change Rtarget.jordan.componentRank Rtarget.component = 2 at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hcomponentEq :=
    D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
      a ITarget htargetBefore.le htargetBefore hnotCollisionLeft
  have htargetRank : finrank K
      (D.largeAlmostJordan.component (x.indexEquiv ITarget).1).carrier = 2 := by
    change finrank K (Rtarget.strictWeak.component Rtarget.component).carrier = 2 at hrank
    rw [hcomponentEq] at hrank
    exact hrank
  have htargetCoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val = (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget] using htargetCoordinatesInput
  have htargetSmallZero : (y.indexEquiv ITarget).2.val = 0 := by
    have h := htargetCoordinates.2
    omega
  have hadjacentLarge :=
    x.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetZero
  have hadjacentSmall :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, Fin.val_mk]
        have := i.one_lt
        omega) htargetSmallZero
  have hsourceCoordinates :
      (x.indexEquiv ISource).1 = (y.indexEquiv ISource).1 ∧
        (x.indexEquiv ISource).2.val = (y.indexEquiv ISource).2.val := by
    simpa only [x, y, ISource] using hsourceCoordinatesInput
  let pPrev := (x.indexEquiv ISource).1
  let pSmallPrev := (y.indexEquiv ISource).1
  let pCurrent := (x.indexEquiv ITarget).1
  have hpPrevSmall : pPrev = pSmallPrev := by
    simpa only [pPrev, pSmallPrev] using hsourceCoordinates.1
  have hpPrevCurrent : pPrev < pCurrent := by
    change (x.indexEquiv ISource).1.val < (x.indexEquiv ITarget).1.val
    omega
  have hpCurrentSelected : pCurrent < D.largeSelectedPosition := by
    simpa only [pCurrent, x, ITarget] using htargetBefore
  have hpPrevSelected : pPrev < D.largeSelectedPosition :=
    hpPrevCurrent.trans hpCurrentSelected
  let prevScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pPrev)
  let currentScale := ordUnit K (D.largeAlmostJordan.scaleGenerator pCurrent)
  let selectedScale := ordUnit K D.input.block.enlargedScaleGenerator
  let largeEffectivePrev :=
    D.largeAlmostJordan.effectiveNormOrderAt pPrev prevScale
  let smallEffectivePrev :=
    D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev prevScale
  let largeEffectiveCurrent :=
    D.largeAlmostJordan.effectiveNormOrderAt pCurrent currentScale
  let selectedNorm := ordUnit K
    (D.largeAlmostJordan.normGeneratorUnit D.largeSelectedPosition)
  have hscaleAligned : ordUnit K
        (D.smallAlmostJordan.scaleGenerator pSmallPrev) = prevScale := by
    rw [← hpPrevSmall]
    exact hscaleAlignment pPrev hpPrevSelected
  have hlargePreviousOrder : a.order ISource =
      2 * prevScale - largeEffectivePrev := by
    rw [D.largeWeak_order_eq_localOrder a ISource]
    change JordanProfileOrder.localOrder prevScale largeEffectivePrev
        (x.indexEquiv ISource).2.val = _
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pPrev
    have hlocalLast : (x.indexEquiv ISource).2.val =
        finrank K (D.largeAlmostJordan.component pPrev).carrier - 1 := by
      have hterminal := hadjacentLarge.2
      change (x.indexEquiv ISource).2.val + 1 =
        finrank K (D.largeAlmostJordan.component pPrev).carrier at hterminal
      omega
    simpa only [hlocalLast, prevScale, largeEffectivePrev] using hlast
  have hsmallPreviousOrder : b.order ISource =
      2 * prevScale - smallEffectivePrev := by
    rw [D.smallWeak_order_eq_localOrder b ISource]
    change JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev))
        (D.smallAlmostJordan.effectiveNormOrderAt pSmallPrev
          (ordUnit K (D.smallAlmostJordan.scaleGenerator pSmallPrev)))
        (y.indexEquiv ISource).2.val = _
    rw [hscaleAligned]
    change JordanProfileOrder.localOrder prevScale smallEffectivePrev
        (y.indexEquiv ISource).2.val = _
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank pSmallPrev
    have hlocalLast : (y.indexEquiv ISource).2.val =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier - 1 := by
      have hterminal := hadjacentSmall.2
      change (y.indexEquiv ISource).2.val + 1 =
        finrank K (D.smallAlmostJordan.component pSmallPrev).carrier at hterminal
      omega
    simpa only [hlocalLast, prevScale, smallEffectivePrev,
      hscaleAligned] using hlast
  have houterLe : a.order ISource ≤ a.order INext := by
    have hbound : ISource.val + 2 < n + 2 := by
      dsimp only [ISource, Fin.val_mk]
      have hi := i.one_lt
      have hibound := i.lt_large
      omega
    have hgood := a.good ISource hbound
    calc
      a.order ISource ≤ a.order ⟨ISource.val + 2, hbound⟩ := hgood
      _ = a.order INext := by
        apply congrArg a.order
        apply Fin.ext
        dsimp only [ISource, INext, Fin.val_mk]
        have hi := i.one_lt
        omega
  refine lt_of_le_of_ne houterLe ?_
  intro houterEq
  have heffectiveStrict : largeEffectivePrev < smallEffectivePrev := by
    have htriggerOrder : b.order ISource < a.order INext := by
      simpa only [ISource, INext] using htrigger.1
    rw [← houterEq, hsmallPreviousOrder, hlargePreviousOrder] at htriggerOrder
    omega
  have hprevScaleLeCurrent : prevScale ≤ currentScale := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hpPrevCurrent.le
    simpa only [prevScale, currentScale] using hmono
  have hprevScaleLtCurrent : prevScale < currentScale := by
    refine lt_of_le_of_ne hprevScaleLeCurrent ?_
    intro heq
    rcases D.largeEqualScale_involves_selected
        (ne_of_lt hpPrevCurrent) heq with hprev | hcurrent
    · exact (ne_of_lt hpPrevSelected) hprev
    · exact (ne_of_lt hpCurrentSelected) hcurrent
  have hcurrentScaleLeSelected : currentScale ≤ selectedScale := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hpCurrentSelected.le
    simpa only [currentScale, selectedScale,
      D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hlargeEffectivePrev : largeEffectivePrev = selectedNorm := by
    exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
      pPrev pSmallPrev pPrev prevScale prevScale le_rfl
        (hprevScaleLeCurrent.trans hcurrentScaleLeSelected) heffectiveStrict
  have hlargeEffectiveCurrent : largeEffectiveCurrent = selectedNorm := by
    exact D.large_effectiveNormOrderAt_eq_selectedNorm_of_lt
      pPrev pSmallPrev pCurrent prevScale currentScale hprevScaleLeCurrent
        hcurrentScaleLeSelected heffectiveStrict
  have hlocalSucc : (x.indexEquiv ITarget).2.val + 1 <
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    have hzero := htargetZero
    have hrankTwo := htargetRank
    omega
  have hnextCoordinates := x.indexEquiv_global_succ_eq_local_succ
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      have := i.one_lt
      omega) hlocalSucc
  have hlargeNextOrder : a.order INext =
      2 * currentScale - largeEffectiveCurrent := by
    rw [D.largeWeak_order_eq_localOrder a INext, hnextCoordinates]
    change JordanProfileOrder.localOrder currentScale largeEffectiveCurrent
        ((x.indexEquiv ITarget).2.val + 1) = _
    rw [htargetZero]
    have hlast := WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
      D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank pCurrent
    have htargetRank' : finrank K
        (D.largeAlmostJordan.component pCurrent).carrier = 2 := by
      simpa only [pCurrent] using htargetRank
    rw [htargetRank'] at hlast
    simpa only [Nat.reduceSubDiff, currentScale,
      largeEffectiveCurrent] using hlast
  rw [hlargePreviousOrder, hlargeNextOrder,
    hlargeEffectivePrev, hlargeEffectiveCurrent] at houterEq
  omega

set_option maxHeartbeats 0 in
/-- The aligned specialization of the binary target-first outer
comparison. -/
theorem weakAligned_targetFirst_rank_two_leftOuter_lt_of_notCollision
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    a.order (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2)) <
      a.order ⟨i.val, i.lt_large⟩ := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  exact D.targetFirst_rank_two_leftOuter_lt_of_notCollision_of_prefixAlignment
    a b i htrigger htargetBefore hfirst hrank hnotCollisionLeft
      (by simpa only [ITarget] using
        D.weakProfile_coordinates_eq hselected a b ITarget)
      (by simpa only [ISource] using
        D.weakProfile_coordinates_eq hselected a b ISource)
      (fun p hp => (D.aligned_scaleOrder_eq_of_lt hselected p hp).symm)

set_option maxHeartbeats 0 in
/-- Global-coordinate wrapper for the preceding binary target branch.  The
source boundary resolution and its alignment with the target block start are
reconstructed from the consecutive coordinates. -/
theorem centralCertificate_of_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
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
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hleftOuter : a.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩) :
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
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change Rtarget.jordan.componentRank Rtarget.component = 2 at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
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
    have hlocalEq := hcoordinates'.2
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
  exact D.centralCertificate_of_sourceBoundary_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    a b hdefect i htrigger htargetBefore hfirst hrank
      hnotCollisionLeft Rsource (by
        simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hweakNext)
      hprefixCarrier hleftOuter

set_option maxHeartbeats 0 in
/-- The aligned specialization of the global binary target-first carrier
wrapper. -/
theorem weakAligned_centralCertificate_of_targetFirst_rank_two_of_left_lt
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hleftOuter : a.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      a.order ⟨i.val, i.lt_large⟩) :
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
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  have hfirst' : ITarget.val = Rtarget.coordinates.start := by
    simpa only [ITarget, Rtarget] using hfirst
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hsmallZero : (y.indexEquiv ITarget).2.val = 0 := by omega
  have hadjacent := y.terminal_and_component_succ_eq_of_global_succ_local_zero
    ISource ITarget (by
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega) hsmallZero
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have htargetBeforeVal := htargetBefore'
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBeforeVal
    have hselectedVal := congrArg Fin.val hselected
    have hcomponentEq := congrArg Fin.val hcoordinates.1
    have hadjacentVal := hadjacent.1
    change (y.indexEquiv ISource).1.val < D.smallSelectedPosition.val
    omega
  have hprefix := D.aligned_prefixCarrier_eq hselected
    (x.indexEquiv ITarget).1.val
  exact D.centralCertificate_of_targetFirst_rank_two_of_left_lt_of_prefixAlignment
    a b hdefect i htrigger htargetBefore
      (by simpa only [x, y, ITarget] using hcoordinates)
      (by simpa only [y, ISource] using hsourceBefore)
      (by simpa only [x, ITarget] using hprefix)
      hfirst hrank hnotCollisionLeft hleftOuter

set_option maxHeartbeats 0 in
/-- Complete ordinary binary target-first branch before the selected block.
The effective-norm argument above supplies the strict outer comparison, so
the actual Lemma 3.7(iv) model construction applies without any order-law
input. -/
theorem weakAligned_centralCertificate_of_targetFirst_rank_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 2)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  have hleftOuter :=
    D.weakAligned_targetFirst_rank_two_leftOuter_lt_of_notCollision
      hselected a b i htrigger htargetBefore hfirst hrank hnotCollisionLeft
  exact D.weakAligned_centralCertificate_of_targetFirst_rank_two_of_left_lt
    hselected a b hdefect i htrigger htargetBefore hfirst hrank
      hnotCollisionLeft hleftOuter

set_option maxHeartbeats 0 in
/-- The ordinary target-first branch with its source boundary constructed
from global adjacency.  In particular, no boundary resolution or component
successor equality remains as an input to the Section 5 argument. -/
theorem weakAligned_centralCertificate_of_targetFirst
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hfirst :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val = R.coordinates.start)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
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
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ITarget.val = Rtarget.coordinates.start at hfirst
  change 2 < Rtarget.jordan.componentRank Rtarget.component at hrank
  have hoffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hresolvedZero : (Rtarget.profile.indexEquiv ITarget).2.val = 0 := by
    have hindex := Rtarget.index_val_eq_coordinates_start_add_local
    omega
  have htargetZero : (x.indexEquiv ITarget).2.val = 0 := by
    have hlocal := Rtarget.localCoordinate_eq
    rw [hoffset, Nat.zero_add] at hlocal
    exact hlocal.symm.trans hresolvedZero
  have hcoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcoordinates' :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hcoordinates
  have hsourceNextZero : (y.indexEquiv ITarget).2.val = 0 := by
    have hlocalEq := hcoordinates'.2
    omega
  have hadjacent :=
    y.terminal_and_component_succ_eq_of_global_succ_local_zero
      ISource ITarget (by
        dsimp only [ISource, ITarget, gSource, gTarget,
          Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) hsourceNextZero
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    have htargetBefore' : (x.indexEquiv ITarget).1 <
        D.largeSelectedPosition := by
      simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using htargetBefore
    have htargetBeforeVal := htargetBefore'
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val at htargetBeforeVal
    have hselectedVal := congrArg Fin.val hselected
    have hcomponentEq := congrArg Fin.val hcoordinates'.1
    have hadjacentVal := hadjacent.1
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val
    omega
  obtain ⟨Rsource⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSource (by simpa only [y, ISource] using hsourceBefore)
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
  exact D.weakAligned_centralCertificate_of_sourceBoundary_targetFirst
    hselected a b hdefect i htrigger htargetBefore hfirst hrank Rsource
      (by simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using hweakNext)

set_option maxHeartbeats 0 in
/-- In the source-penultimate branch with a ternary source prefix, the
discriminant-twist choice following Beli's Lemma 3.7 supplies a fundamental
norm-generator line represented by that prefix. -/
theorem centralCertificate_of_sourcePenultimate_iii_of_prefix_rank_three_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hsourcePositive : 0 < i.val - 2)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      1 < R.jordan.componentRank R.component)
    (hsourceNext :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.component.val + 1 < R.componentCount)
    (hthree :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      finrank K
        (R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1)) = 3)
    (houter : b.order
        ⟨i.val - 3, by have := i.lt_large; omega⟩ =
      b.order ⟨i.val - 1, by have := i.lt_large; omega⟩)
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1)) →
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  intro hprefixCarrier
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  let C := Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
    (Rsource.component.val + 1)
  let A₀ := Rsource.jordan.fundamentalNormGenerator Rsource.component
  have hA₀ : Lattice.IsNormGeneratorValue q
      (Rsource.jordan.fundamentalLattice Rsource.component) A₀ :=
    Rsource.jordan.fundamentalNormGenerator_spec Rsource.component
  letI : Module.Finite K V := N.moduleFinite
  change finrank K C.carrier = 3 at hthree
  obtain ⟨A, hA, hline⟩ :=
    QuadraticSpace.exists_normGeneratorValue_represents_scaledLine_of_finrank_eq_three
      C.space hthree A₀ hA₀
  apply D.centralCertificate_of_sourcePenultimate_iii_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore hsourcePositive
      hpenultimate hrank hsourceNext A hA
        (by simpa only [C] using hline) houter Rtarget hweakNext
  exact hprefixCarrier

set_option maxHeartbeats 0 in
/-- The global-left endpoint of the source-penultimate branch (`i = 2`).
The source coordinate is zero, so its resolved component is the first binary
Jordan component.  The endpoint form of Lemma 3.7(iv) supplies the source
line model, while aligned prefix carriers place it in the target boundary. -/
theorem centralCertificate_of_sourcePenultimate_at_two_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = 2)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hrightOuter : b.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩)
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1))
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  have hzero : ISource.val = 0 := by
    dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
    omega
  have hrank : Rsource.jordan.componentRank Rsource.component = 2 := by
    have hstart := Rsource.coordinates_start_le_index
    have hstop : Rsource.coordinates.stop = Rsource.coordinates.start +
        Rsource.jordan.componentRank Rsource.component := by
      rfl
    omega
  have hrightBound : ISource.val + 2 < n + 2 := by
    dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
    have hiLt := i.lt_large
    omega
  have hsourceNext : Rsource.component.val + 1 <
      Rsource.componentCount :=
    Rsource.component_succ_lt_of_penultimate hpenultimate hrightBound
  have hrightOuter' : b.order ISource <
      b.order ⟨ISource.val + 2, hrightBound⟩ := by
    convert hrightOuter using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk] <;> omega
  rcases Rsource.exists_spaceModel_iv_of_binary_penultimate_at_zero
      gSource rfl hzero hpenultimate hrank hsourceNext hrightBound hrightOuter'
    with ⟨source, hsourceModelCarrier⟩
  have hsourcePrefix :=
    D.smallStrictCoordinateResolution_prefixCarrier_succ_eq_of_lt
      b ISource hsourceBefore.le hsourceBefore
  have haligned :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((y.indexEquiv ISource).1.val + 1) := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hprefixCarrier
  have hweakNext' : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  have hcarrier : source.carrier ≤ Rtarget.lemma37Model_i.carrier := by
    rw [Rtarget.lemma37Model_i_carrier_eq]
    calc
      source.carrier ≤
          Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
            (Rsource.component.val + 1) := hsourceModelCarrier
      _ = D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := hsourcePrefix
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            ((y.indexEquiv ISource).1.val + 1) := haligned.symm
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
            Rtarget.weakNext.val := by rw [hweakNext']
  exact centralCertificate_of_sourceModel_to_boundary
    a b hdefect i htrigger Rtarget source hcarrier

set_option maxHeartbeats 0 in
/-- The aligned specialization of the initial source-penultimate branch. -/
theorem weakAligned_centralCertificate_of_sourcePenultimate_at_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = 2)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (Rtarget : BONG.StrictBoundaryResolution a D.largeAlmostJordan
      (D.largeWeakProfileWitness a)
      (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)))
    (hweakNext : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hright := D.weakAligned_source_rightTwoStep_lt_of_penultimate
    hselected a b i htrigger hsourceBefore hpenultimate
  have hprefix := D.aligned_prefixCarrier_eq hselected
    (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1)
  exact D.centralCertificate_of_sourcePenultimate_at_two_of_prefixAlignment
    a b hdefect i htrigger hindex hsourceBefore hpenultimate hright
      (by simpa only [ISource] using hprefix) Rtarget hweakNext

set_option maxHeartbeats 0 in
/-- Reconstruct the target boundary in the initial source-penultimate branch
from local target coordinate/rank agreement.  This is the common form used by
both the aligned and adjacent-unary orderings. -/
theorem centralCertificate_of_sourcePenultimate_of_notCollision_at_two_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = 2)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hcoordinatesInput :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (htargetRankEq :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1).carrier)
    (hrightOuter : b.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩)
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1))
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  have hsourceTerminal := D.smallWeak_globalSucc_terminal_of_strictPenultimate
    b ISource ITarget hsourceBefore.le hsourceBefore (by
      dsimp only [ISource, ITarget, Fin.val_mk]
      have := i.one_lt
      omega) hpenultimate
  have hsourceTerminal' :
      (y.indexEquiv ITarget).1 = (y.indexEquiv ISource).1 ∧
        (y.indexEquiv ITarget).2.val + 1 =
          finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ITarget).1).carrier := by
    simpa only [y] using hsourceTerminal
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget] using hcoordinatesInput
  have htargetLast : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    have hlargeSmallRank :
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier := by
      simpa only [x, ITarget] using htargetRankEq
    have hsmallRankTransport := congrArg
      (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
      hcoordinates.1
    omega
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget] using htargetBefore
  have hITarget : ITarget = gTarget.castSucc := by
    apply Fin.ext
    rfl
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution
    a gTarget (by rw [← hITarget]; simpa only [x] using htargetBefore')
      (by rw [← hITarget]; simpa only [x] using htargetLast)
      (by rw [← hITarget]; simpa only [x] using hnotCollisionLeft)
  have hweakNext : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    have htargetWeakNext : Rtarget.weakNext.val =
        (x.indexEquiv ITarget).1.val + 1 := by
      rw [hITarget]
      simpa only [x] using Rtarget.weakNext_val
    have hterminalComponent := congrArg Fin.val hsourceTerminal'.1
    have hcoordinateComponent := congrArg Fin.val hcoordinates.1
    omega
  exact D.centralCertificate_of_sourcePenultimate_at_two_of_prefixAlignment
    a b hdefect i htrigger hindex hsourceBefore hpenultimate hrightOuter
      (by simpa only [y, ISource] using hprefixCarrier) Rtarget
      (by simpa only [y, ISource] using hweakNext)

set_option maxHeartbeats 0 in
/-- Complete source-penultimate endpoint branch away from the large-side
collision.  The target boundary and its successor coordinate are reconstructed
from the aligned weak profiles, leaving no boundary-resolution input. -/
theorem weakAligned_centralCertificate_of_sourcePenultimate_of_notCollision_at_two
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hindex : i.val = 2)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
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
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  have hsourceTerminal := D.smallWeak_globalSucc_terminal_of_strictPenultimate
    b ISource ITarget hsourceBefore.le hsourceBefore (by
      dsimp only [ISource, ITarget, gSource, gTarget,
        Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega) hpenultimate
  have hsourceTerminal' :
      (y.indexEquiv ITarget).1 = (y.indexEquiv ISource).1 ∧
        (y.indexEquiv ITarget).2.val + 1 =
          finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ITarget).1).carrier := by
    simpa only [y] using hsourceTerminal
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y] using hcoordinatesRaw
  have htargetLast : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    have hlargeSmallRank :
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier := by
      simpa only [Lattice.OrthogonalDecomposition.componentRank] using
        congrFun (D.almostJordan_componentRank_eq hselected)
          (x.indexEquiv ITarget).1
    have hsmallRankTransport := congrArg
      (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
      hcoordinates.1
    omega
  have htargetBefore : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    have hsourceBeforeFin : (y.indexEquiv ISource).1 <
        D.smallSelectedPosition := by
      simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore
    have hsourceBefore' := hsourceBeforeFin
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val at hsourceBefore'
    have hselectedVal := congrArg Fin.val hselected
    have hterminalComponent := congrArg Fin.val hsourceTerminal'.1
    have hcoordinateComponent := congrArg Fin.val hcoordinates.1
    change (x.indexEquiv ITarget).1.val <
      D.largeSelectedPosition.val
    omega
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution
    a gTarget (by simpa only [x, ITarget] using htargetBefore)
      (by simpa only [x, ITarget] using htargetLast)
      (by simpa only [x, ITarget, gTarget, Fin.castSucc_mk]
        using hnotCollisionLeft)
  have hweakNext : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    have htargetWeakNext : Rtarget.weakNext.val =
        (x.indexEquiv ITarget).1.val + 1 := by
      simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using
        Rtarget.weakNext_val
    have hterminalComponent := congrArg Fin.val hsourceTerminal'.1
    have hcoordinateComponent := congrArg Fin.val hcoordinates.1
    omega
  have hweakNextArg : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  exact D.weakAligned_centralCertificate_of_sourcePenultimate_at_two
    hselected a b hdefect i htrigger hindex hsourceBefore hpenultimate
      Rtarget hweakNextArg

set_option maxHeartbeats 0 in
/-- The ordinary source-penultimate branch away from the unique large-side
collision.  The target boundary, the existence of the following strict
component, and the rank-four prefix bound are all reconstructed from the
global coordinates.  Rank at least three uses Lemma 3.7(iii) directly.  In
rank two, good-BONG monotonicity splits the left outer comparison into the
equality case 3.7(iii) and the strict case 3.7(iv). -/
theorem centralCertificate_of_sourcePenultimate_of_notCollision_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hcoordinatesInput :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).1 ∧
        ((D.largeWeakProfileWitness a).indexEquiv ITarget).2.val =
          ((D.smallWeakProfileWitness b).indexEquiv ITarget).2.val)
    (htargetRankEq :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1).carrier)
    (hrightOuter : b.order
        ⟨i.val - 2, by have := i.lt_large; omega⟩ <
      b.order ⟨i.val, i.lt_large⟩)
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1) =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (((D.smallWeakProfileWitness b).indexEquiv ISource).1.val + 1))
    (hpenultimate :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val + 2 = R.coordinates.stop)
    (hthreeIndex : 3 ≤ i.val)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val + 2 = Rsource.coordinates.stop at hpenultimate
  have hrank : 1 < Rsource.jordan.componentRank Rsource.component := by
    have hindex := Rsource.index_val_eq_coordinates_start_add_local
    have hstop : Rsource.coordinates.stop = Rsource.coordinates.start +
        Rsource.jordan.componentRank Rsource.component := by
      rfl
    omega
  have hsourceTerminal := D.smallWeak_globalSucc_terminal_of_strictPenultimate
    b ISource ITarget hsourceBefore.le hsourceBefore (by
      dsimp only [ISource, ITarget, gSource, gTarget,
        Fin.castSucc_mk, Fin.val_mk]
      have := i.one_lt
      omega) hpenultimate
  have hsourceTerminal' :
      (y.indexEquiv ITarget).1 = (y.indexEquiv ISource).1 ∧
        (y.indexEquiv ITarget).2.val + 1 =
          finrank K (D.smallAlmostJordan.component
            (y.indexEquiv ITarget).1).carrier := by
    simpa only [y] using hsourceTerminal
  have hcoordinates :
      (x.indexEquiv ITarget).1 = (y.indexEquiv ITarget).1 ∧
        (x.indexEquiv ITarget).2.val =
          (y.indexEquiv ITarget).2.val := by
    simpa only [x, y, ITarget, gTarget, Fin.castSucc_mk] using
      hcoordinatesInput
  have htargetLast : (x.indexEquiv ITarget).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv ITarget).1).carrier := by
    have hlargeSmallRank :
        finrank K (D.largeAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier =
        finrank K (D.smallAlmostJordan.component
          (x.indexEquiv ITarget).1).carrier := by
      convert htargetRankEq using 1
    have hsmallRankTransport := congrArg
      (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
      hcoordinates.1
    omega
  have htargetBefore' : (x.indexEquiv ITarget).1 <
      D.largeSelectedPosition := by
    simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using htargetBefore
  have hITarget : ITarget = gTarget.castSucc := by
    apply Fin.ext
    rfl
  obtain ⟨Rtarget⟩ := D.nonempty_largeStrictBoundaryResolution
    a gTarget (by rw [← hITarget]; simpa only [x] using htargetBefore')
      (by rw [← hITarget]; simpa only [x] using htargetLast)
      (by rw [← hITarget]; simpa only [x] using hnotCollisionLeft)
  have hweakNext : Rtarget.weakNext.val =
      (y.indexEquiv ISource).1.val + 1 := by
    have htargetWeakNext : Rtarget.weakNext.val =
        (x.indexEquiv ITarget).1.val + 1 := by
      rw [hITarget]
      simpa only [x] using Rtarget.weakNext_val
    have hterminalComponent := congrArg Fin.val hsourceTerminal'.1
    have hcoordinateComponent := congrArg Fin.val hcoordinates.1
    omega
  have hsourcePositive : 0 < i.val - 2 := by omega
  have hsourceNext : Rsource.component.val + 1 <
      Rsource.componentCount :=
    Rsource.component_succ_lt_of_penultimate hpenultimate (by
      dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
      have hiOne := i.one_lt
      have hiLt := i.lt_large
      omega)
  have hprefixRank :=
    Rsource.finrank_prefixCarrier_succ_eq_coordinates_stop hsourceNext
  have hprefixIndex : finrank K
      (Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
        (Rsource.component.val + 1)) = i.val := by
    rw [hprefixRank, ← hpenultimate]
    dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
    omega
  have hweakNextArg : Rtarget.weakNext.val =
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1.val + 1 := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hweakNext
  by_cases hrankTwo : Rsource.jordan.componentRank Rsource.component = 2
  · have hsourceCoordinatePositive : 0 < ISource.val := by
      dsimp only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk]
      omega
    have hcomponentPositive : 0 < Rsource.component.val :=
      Rsource.component_pos_of_binary_penultimate_of_pos
        hsourceCoordinatePositive hpenultimate hrankTwo
    have hleftLe : b.order
          ⟨i.val - 3, by have := i.lt_large; omega⟩ ≤
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
      have hstart : i.val - 3 < n + 2 := by
        have hiLt := i.lt_large
        omega
      have hstep :
          (⟨i.val - 3, hstart⟩ : Fin (n + 2)).val + 2 < n + 2 := by
        change i.val - 3 + 2 < n + 2
        have hiLt := i.lt_large
        omega
      have hgood := b.good ⟨i.val - 3, hstart⟩ hstep
      have hend :
          (⟨(⟨i.val - 3, hstart⟩ : Fin (n + 2)).val + 2, hstep⟩ :
              Fin (n + 2)) =
            ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
        apply Fin.ext
        change i.val - 3 + 2 = i.val - 1
        omega
      rwa [hend] at hgood
    rcases lt_or_eq_of_le hleftLe with hleftStrict | hleftEq
    · apply D.centralCertificate_of_sourcePenultimate_iv_of_prefixAlignment
        (Rtarget := Rtarget) a b hdefect i htrigger hsourceBefore hsourcePositive
          hpenultimate hrankTwo hcomponentPositive hsourceNext hleftStrict
      · exact hrightOuter
      · exact hprefixCarrier
      · exact hweakNextArg
    · by_cases hindexThree : i.val = 3
      · have hthree : finrank K
            (Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
              (Rsource.component.val + 1)) = 3 := by
          omega
        apply D.centralCertificate_of_sourcePenultimate_iii_of_prefix_rank_three_of_prefixAlignment
          a b hdefect i htrigger hsourceBefore hsourcePositive
            hpenultimate hrank hsourceNext hthree hleftEq Rtarget hweakNextArg
        exact hprefixCarrier
      · let A := Rsource.jordan.fundamentalNormGenerator Rsource.component
        have hA : Lattice.IsNormGeneratorValue q
            (Rsource.jordan.fundamentalLattice Rsource.component) A :=
          Rsource.jordan.fundamentalNormGenerator_spec Rsource.component
        letI : Module.Finite K V := N.moduleFinite
        have hfour' : 4 ≤ finrank K
            (Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
              (Rsource.component.val + 1)).carrier := by
          rw [Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice_carrier]
          omega
        have hline :
            (Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
              (Rsource.component.val + 1)).space.Represents
                (QuadraticSpace.scaledLine A) :=
          (Rsource.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
            (Rsource.component.val + 1)).space
              |>.represents_scaledLine_of_four_le_finrank A hfour'
        apply D.centralCertificate_of_sourcePenultimate_iii_of_prefixAlignment
          a b hdefect i htrigger hsourceBefore hsourcePositive
            hpenultimate hrank hsourceNext A hA hline hleftEq Rtarget
              hweakNextArg
        exact hprefixCarrier
  · have hrankHigh : 2 <
        Rsource.jordan.componentRank Rsource.component := by omega
    by_cases hindexThree : i.val = 3
    · have hthree : finrank K
          (Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
            (Rsource.component.val + 1)) = 3 := by
        omega
      have hcoordinateStart : Rsource.coordinates.start ≤ i.val - 3 := by
        have hstop : Rsource.coordinates.stop = Rsource.coordinates.start +
            Rsource.jordan.componentRank Rsource.component := by
          rfl
        omega
      have hcoordinateNext : (i.val - 3) + 2 <
          Rsource.coordinates.stop := by
        omega
      have houterRaw := Rsource.coordinates.order_add_two_eq
        (i.val - 3) hcoordinateStart hcoordinateNext
      have houter : b.order
          ⟨i.val - 3, by have := i.lt_large; omega⟩ =
        b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
        convert houterRaw using 1 <;> apply congrArg b.order <;>
          apply Fin.ext <;>
            simp only [BONG.GoodBONG.JordanBlockCoordinates.index_val] <;>
              omega
      apply D.centralCertificate_of_sourcePenultimate_iii_of_prefix_rank_three_of_prefixAlignment
        a b hdefect i htrigger hsourceBefore hsourcePositive
          hpenultimate hrank hsourceNext hthree houter Rtarget hweakNextArg
      exact hprefixCarrier
    · have hfour : 4 ≤ finrank K
          (Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
            (Rsource.component.val + 1)) := by
        omega
      apply D.centralCertificate_of_sourcePenultimate_four_le_of_prefixAlignment
        a b hdefect i htrigger hsourceBefore hsourcePositive
          hpenultimate hrankHigh hsourceNext hfour Rtarget hweakNextArg
      exact hprefixCarrier

end Lattice.Beli2019Lemma51Data

end Bong
