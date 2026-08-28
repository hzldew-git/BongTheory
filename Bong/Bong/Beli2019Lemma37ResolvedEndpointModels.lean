/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37ResolvedCarriers
import Bong.Bong.Beli2019Lemma37Endpoints
import Bong.Bong.Beli2019Lemma37UniversalModels
import Bong.Bong.Beli2019Lemma37BoundaryModels

/-!
# Lemma 3.7 models selected by a strict coordinate resolution

This file converts the numerical first/penultimate/last positions of a
`StrictCoordinateResolution` into the actual approximation models of
Lemma 3.7.  The first construction below is the interior instance of
case (ii); endpoint and one-before constructions follow in the same layer.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.StrictCoordinateResolution

set_option maxHeartbeats 0 in
/-- A positive first coordinate of a resolved component of rank at least two
gives the interior Lemma 3.7(ii) abstract approximation model. -/
noncomputable def diagonalModel_ii_of_first_interior
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 1 < R.jordan.componentRank R.component)
    (hinternal : g.val + 1 < n + 1)
    (houter : a.order g.castSucc =
      a.order (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ) :
    BONG.GoodBONG.DiagonalApproximationModel a g := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefix, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict
      strictWeak hstrict profile
    have hfirst' : I.val = w.componentStart p := by
      simpa only [BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, w, p]
        using hfirst
    have hp : 0 < p.val := by
      by_contra hnot
      have hpzero : p = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hnot
      have hstartZero : w.componentStart p = 0 := by
        rw [hpzero]
        unfold BONG.WeakJordanOrderProfileWitness.componentStart
        simp
      rw [hfirst', hstartZero] at hpositive
      omega
    let z : Fin t := ⟨p.val - 1, by omega⟩
    have hright :
        Lattice.JordanDecomposition.boundaryRightIndex z = p := by
      apply Fin.ext
      change z.val + 1 = p.val
      dsimp only [z]
      omega
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
      rw [hright]
      exact hrank
    have hboundary := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hright] at hboundary
    have hstart : (profile.boundaryIndex z).val + 1 = w.componentStart p := by
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio p, finrank K (strictWeak.component k).carrier
      exact hboundary
    have hindex : profile.boundaryOneAfterIndex z hrank' = g := by
      apply Fin.ext
      simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex]
      rw [hstart, ← hfirst']
      exact congrArg Fin.val hI
    let A := (strictWeak.toJordan hstrict).fundamentalNormGenerator p
    have hA : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryRightIndex z)) A := by
      rw [hright]
      exact (strictWeak.toJordan hstrict).fundamentalNormGenerator_spec p
    have hinternal' :
        (profile.boundaryOneAfterIndex z hrank').val + 1 < n + 1 := by
      rw [hindex]
      exact hinternal
    have houter' :
        a.order (profile.boundaryOneAfterIndex z hrank').castSucc =
          a.order (⟨(profile.boundaryOneAfterIndex z hrank').val + 1,
            hinternal'⟩ : Fin (n + 1)).succ := by
      simpa only [hindex] using houter
    let model :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37DiagonalModel_ii
        a strictWeak hparity hstrict profile z A hA hrank'
          hinternal' houter'
    exact model.castIndex hindex

set_option maxHeartbeats 0 in
/-- Choice-flexible geometric form of resolved Lemma 3.7(ii).  A prescribed
represented fundamental generator supplies the adjoined line, and the result
is carried by every ambient subspace containing both the preceding Jordan
prefix and that line. -/
theorem exists_spaceModel_ii_of_first_interior_with_generator_carrier_le
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 1 < R.jordan.componentRank R.component)
    (G : BONG.RepresentedFundamentalNormGenerator R.jordan R.component)
    (v : (R.jordan.component R.component).carrier)
    (hv : (R.jordan.component R.component).space.quadratic v =
      (G.value : K))
    (hinternal : g.val + 1 < n + 1)
    (houter : a.order g.castSucc =
      a.order (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ)
    (T : Submodule K V)
    (hprefix : R.jordan.toOrthogonalDecomposition.prefixCarrier
      R.component.val ≤ T)
    (hvector : (v : V) ∈ T) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      model.carrier ≤ T := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let w := BONG.WeakJordanOrderProfileWitness.ofStrict
      strictWeak hstrict profile
    have hfirst' : I.val = w.componentStart p := by
      simpa only [BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, w, p]
        using hfirst
    have hp : 0 < p.val := by
      by_contra hnot
      have hpzero : p = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hnot
      have hstartZero : w.componentStart p = 0 := by
        rw [hpzero]
        unfold BONG.WeakJordanOrderProfileWitness.componentStart
        simp
      rw [hfirst', hstartZero] at hpositive
      omega
    let z : Fin t := ⟨p.val - 1, by omega⟩
    have hright :
        Lattice.JordanDecomposition.boundaryRightIndex z = p := by
      apply Fin.ext
      change z.val + 1 = p.val
      dsimp only [z]
      omega
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
      rw [hright]
      exact hrank
    have hA' : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryRightIndex z)) G.value := by
      rw [hright]
      exact G.fundamental
    have hboundary := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hright] at hboundary
    have hstart : (profile.boundaryIndex z).val + 1 = w.componentStart p := by
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio p, finrank K (strictWeak.component k).carrier
      exact hboundary
    have hindex : profile.boundaryOneAfterIndex z hrank' = g := by
      apply Fin.ext
      simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex]
      rw [hstart, ← hfirst']
      exact congrArg Fin.val hI
    have hinternal' :
        (profile.boundaryOneAfterIndex z hrank').val + 1 < n + 1 := by
      rw [hindex]
      exact hinternal
    have houter' :
        a.order (profile.boundaryOneAfterIndex z hrank').castSucc =
          a.order (⟨(profile.boundaryOneAfterIndex z hrank').val + 1,
            hinternal'⟩ : Fin (n + 1)).succ := by
      simpa only [hindex] using houter
    let J := strictWeak.toJordan hstrict
    have hpval : (Lattice.JordanDecomposition.boundaryRightIndex z).val =
        z.val + 1 := rfl
    have horth : ∀ y : (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (z.val + 1)).carrier,
        q.bilin (y : V) (v : V) = 0 := by
      intro y
      let y' : (J.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice p.val).carrier :=
        ⟨(y : V), by rw [← hright, hpval]; exact y.property⟩
      exact J.toOrthogonalDecomposition.prefix_orthogonal_component p y' v
    have happroximation :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_ii
        a strictWeak hparity hstrict profile z G.value hA'
          hrank' hinternal' houter'
    let base :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneAfter_ofOrthogonalVector
        a J profile z G.value hrank' (v : V) hv horth happroximation
    let model : BONG.GoodBONG.SpaceApproximationModel a g :=
      base.castIndex hindex
    refine ⟨model, ?_⟩
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    apply BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneAfter_ofOrthogonalVector_carrier_le
      a J profile z G.value hrank' (v : V) hv horth happroximation T
    · have hzsucc : z.val + 1 = p.val := by
        dsimp only [z]
        omega
      change J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) ≤ T
      rw [hzsucc]
      simpa only [J, BONG.StrictCoordinateResolution.jordan,
        BONG.StrictCoordinateResolution.component] using hprefix
    · exact hvector

set_option maxHeartbeats 0 in
/-- If at least three coordinates remain in the resolved component, the
two-step equality needed by case (ii) is the alternating Jordan order
identity, so no order equality has to be supplied separately. -/
noncomputable def diagonalModel_ii_of_first
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 2 < R.jordan.componentRank R.component) :
    BONG.GoodBONG.DiagonalApproximationModel a g := by
  have hstopFormula : R.coordinates.stop =
      R.coordinates.start + R.jordan.componentRank R.component := by
    rfl
  have hstopTwo : I.val + 2 < R.coordinates.stop := by
    rw [hstopFormula, hfirst]
    omega
  have hinternal : g.val + 1 < n + 1 := by
    have hstop := R.coordinates.stop_le
    have hIval : I.val = g.val := congrArg Fin.val hI
    omega
  have hperiod := R.coordinates.order_add_two_eq I.val
    (by rw [hfirst]) hstopTwo
  have houter : a.order g.castSucc =
      a.order (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
    have hIval : I.val = g.val := congrArg Fin.val hI
    have hleft (h : I.val < R.coordinates.stop) :
        R.coordinates.index I.val h = g.castSucc := by
      apply Fin.ext
      exact hIval
    have hright (h : I.val + 2 < R.coordinates.stop) :
        R.coordinates.index (I.val + 2) h =
          (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
      apply Fin.ext
      change I.val + 2 = g.val + 2
      omega
    simpa only [hleft, hright] using hperiod
  exact R.diagonalModel_ii_of_first_interior g hI hpositive hfirst
    (lt_trans (by omega) hrank) hinternal houter

set_option maxHeartbeats 0 in
/-- A source boundary prefix is represented by the Lemma 3.7(ii) model at a
resolved target first coordinate once the required two-step order equality is
given explicitly.  Unlike the periodic wrapper below, this form also applies
to a binary target component. -/
theorem exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first_with_outer
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n m c d : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 1 < R.jordan.componentRank R.component)
    (hinternal : g.val + 1 < n + 1)
    (houter : a.order g.castSucc =
      a.order (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ)
    {M : Lattice K V} {b : BONG.GoodBONG q M (m + 2)}
    {H : Lattice.JordanDecomposition q M (d + 1)}
    (Q : BONG.JordanOrderProfileWitness b.toBONG H) (w : Fin d)
    (hprefix : QuadraticSpace.Isometry (H.prefixSpace (w.val + 1))
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        R.component.val).space) :
    ∃ model : BONG.GoodBONG.DiagonalApproximationModel a g,
      DiagonalRepresents
        (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w))
        (diagonalUnitCoefficients model.units) := by
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
    let wTarget := BONG.WeakJordanOrderProfileWitness.ofStrict
      strictWeak hstrict profile
    have hfirst' : I.val = wTarget.componentStart p := by
      simpa only [resolved, BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, wTarget, p]
        using hfirst
    have hp : 0 < p.val := by
      by_contra hnot
      have hpzero : p = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hnot
      have hstartZero : wTarget.componentStart p = 0 := by
        rw [hpzero]
        unfold BONG.WeakJordanOrderProfileWitness.componentStart
        simp
      rw [hfirst', hstartZero] at hpositive
      omega
    let z : Fin t := ⟨p.val - 1, by omega⟩
    have hright :
        Lattice.JordanDecomposition.boundaryRightIndex z = p := by
      apply Fin.ext
      change z.val + 1 = p.val
      dsimp only [z]
      omega
    have hrankP : 1 < (strictWeak.toJordan hstrict).componentRank p := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
      rw [hright]
      exact hrankP
    have hboundary := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hright] at hboundary
    have hstart : (profile.boundaryIndex z).val + 1 =
        wTarget.componentStart p := by
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio p, finrank K (strictWeak.component k).carrier
      exact hboundary
    have hindex : profile.boundaryOneAfterIndex z hrank' = g := by
      apply Fin.ext
      simp only [BONG.JordanOrderProfileWitness.boundaryOneAfterIndex]
      rw [hstart, ← hfirst']
      exact congrArg Fin.val hI
    let A := (strictWeak.toJordan hstrict).fundamentalNormGenerator p
    have hA : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryRightIndex z)) A := by
      rw [hright]
      exact (strictWeak.toJordan hstrict).fundamentalNormGenerator_spec p
    have hinternal' :
        (profile.boundaryOneAfterIndex z hrank').val + 1 < n + 1 := by
      rw [hindex]
      exact hinternal
    have houter' :
        a.order (profile.boundaryOneAfterIndex z hrank').castSucc =
          a.order (⟨(profile.boundaryOneAfterIndex z hrank').val + 1,
            hinternal'⟩ : Fin (n + 1)).succ := by
      simpa only [hindex] using houter
    have hprefix' : QuadraticSpace.Isometry
        (H.prefixSpace (w.val + 1))
        ((strictWeak.toJordan hstrict).prefixSpace (z.val + 1)) := by
      change QuadraticSpace.Isometry (H.prefixSpace (w.val + 1))
        ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice p.val).space at hprefix
      have hz : z.val + 1 = p.val := by
        dsimp only [z]
        omega
      rw [hz]
      exact hprefix
    let base :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37DiagonalModel_ii
        a strictWeak hparity hstrict profile z A hA hrank'
          hinternal' houter'
    let model := base.castIndex hindex
    refine ⟨model, ?_⟩
    have hrep := Q.boundaryPrefix_diagonalRepresents_oneAfter_of_prefixIsometry
      profile w z A hprefix'
    exact base.castIndex_diagonalRepresentedBy hindex hrep

set_option maxHeartbeats 0 in
/-- A source boundary prefix is represented by the Lemma 3.7(ii) model at a
resolved target first coordinate whenever the two preceding prefixes are
isometric. -/
theorem exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n m c d : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 2 < R.jordan.componentRank R.component)
    {M : Lattice K V} {b : BONG.GoodBONG q M (m + 2)}
    {H : Lattice.JordanDecomposition q M (d + 1)}
    (Q : BONG.JordanOrderProfileWitness b.toBONG H) (w : Fin d)
    (hprefix : QuadraticSpace.Isometry (H.prefixSpace (w.val + 1))
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        R.component.val).space) :
    ∃ model : BONG.GoodBONG.DiagonalApproximationModel a g,
      DiagonalRepresents
        (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w))
        (diagonalUnitCoefficients model.units) := by
  classical
  have hstopFormula : R.coordinates.stop =
      R.coordinates.start + R.jordan.componentRank R.component := by
    rfl
  have hstopTwo : I.val + 2 < R.coordinates.stop := by
    rw [hstopFormula, hfirst]
    omega
  have hinternal : g.val + 1 < n + 1 := by
    have hstop := R.coordinates.stop_le
    have hIval : I.val = g.val := congrArg Fin.val hI
    omega
  have hperiod := R.coordinates.order_add_two_eq I.val
    (by rw [hfirst]) hstopTwo
  have houter : a.order g.castSucc =
      a.order (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
    have hIval : I.val = g.val := congrArg Fin.val hI
    have hleft (h : I.val < R.coordinates.stop) :
        R.coordinates.index I.val h = g.castSucc := by
      apply Fin.ext
      exact hIval
    have hright (h : I.val + 2 < R.coordinates.stop) :
        R.coordinates.index (I.val + 2) h =
          (⟨g.val + 1, hinternal⟩ : Fin (n + 1)).succ := by
      apply Fin.ext
      change I.val + 2 = g.val + 2
      omega
    simpa only [hleft, hright] using hperiod
  exact R.exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first_with_outer
    g hI hpositive hfirst (by omega) hinternal houter Q w hprefix

set_option maxHeartbeats 0 in
/-- A terminal coordinate of a resolved strict component gives the concrete
Lemma 3.7(i) prefix model.  The following strict component is required only
to express the current component as a Jordan boundary; in the Section 5
central application it is supplied by the global successor of the target
coordinate. -/
noncomputable def spaceModel_i_of_last
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hlast : I.val + 1 = R.coordinates.stop)
    (hcomponentNext : R.component.val + 1 < R.componentCount) :
    BONG.GoodBONG.SpaceApproximationModel a g := by
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
    have hpNext : p.val + 1 < t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hcomponentNext
    let z : Fin t := ⟨p.val, by omega⟩
    have hright :
        Lattice.JordanDecomposition.boundaryRightIndex z =
          ⟨p.val + 1, hpNext⟩ := by
      apply Fin.ext
      rfl
    have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < z.val + 1 ↔ k = p ∨ k.val < p.val
      dsimp only [z]
      constructor
      · intro hk
        by_cases hkp : k.val = p.val
        · exact Or.inl (Fin.ext hkp)
        · exact Or.inr (by omega)
      · rintro (rfl | hk) <;> omega
    have hboundaryStop : (profile.boundaryIndex z).val + 1 =
        (BONG.WeakJordanOrderProfileWitness.ofStrict
          strictWeak hstrict profile).componentStop p := by
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (strictWeak.component k).carrier at hb
      rw [hIio, Finset.sum_insert (by simp)] at hb
      change (profile.boundaryIndex z).val + 1 =
        (∑ k ∈ Finset.Iio p,
          finrank K (strictWeak.component k).carrier) +
            finrank K (strictWeak.component p).carrier
      simpa only [Nat.add_comm] using hb
    have hstop : (profile.boundaryIndex z).val + 1 =
        resolved.coordinates.stop := by
      simpa only [resolved, BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates] using
          hboundaryStop
    have hindex : profile.boundaryIndex z = g := by
      apply Fin.ext
      have hIval : I.val = g.val := congrArg Fin.val hI
      have hlast' : I.val + 1 = resolved.coordinates.stop := by
        simpa only [resolved] using hlast
      omega
    exact
      (BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
        a strictWeak hparity hstrict profile z).castIndex hindex

set_option maxHeartbeats 0 in
/-- The preceding resolved case-(i) model is carried by the strict Jordan
prefix through the resolved component. -/
theorem spaceModel_i_of_last_carrier
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hlast : I.val + 1 = R.coordinates.stop)
    (hcomponentNext : R.component.val + 1 < R.componentCount) :
    (R.spaceModel_i_of_last g hI hlast hcomponentNext).carrier =
      R.jordan.toOrthogonalDecomposition.prefixCarrier
        (R.component.val + 1) := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    simp only [spaceModel_i_of_last,
      BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    rfl

set_option maxHeartbeats 0 in
/-- Pair a resolved source case-(i) model with a resolved target
case-(ii) model.  This is the ordinary adjacency in Section 5 where the
source coordinate is terminal in the preceding component and the target
coordinate is first in a component of rank at least three. -/
theorem exists_models_i_to_ii_of_prefixIsometry
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start)
    (hrank : 2 < R.jordan.componentRank R.component)
    {m d : Nat} {M : Lattice K V}
    {b : BONG.GoodBONG q M (m + 2)}
    {T : Lattice.WeakJordanDecomposition q M d}
    {y : BONG.WeakJordanOrderProfileWitness b.toBONG T}
    {J : Fin (m + 2)}
    (S : StrictCoordinateResolution b.toBONG T y J)
    (h : Fin (m + 1)) (hJ : J = h.castSucc)
    (hlast : J.val + 1 = S.coordinates.stop)
    (hnext : S.component.val + 1 < S.componentCount)
    (hprefix : QuadraticSpace.Isometry
      (S.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (S.component.val + 1)).space
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        R.component.val).space) :
    ∃ (source : BONG.GoodBONG.SpaceApproximationModel b h)
      (target : BONG.GoodBONG.DiagonalApproximationModel a g),
      DiagonalRepresents (diagonalUnitCoefficients source.units)
        (diagonalUnitCoefficients target.units) := by
  classical
  rcases S with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv J).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let resolved : StrictCoordinateResolution b.toBONG T y J :=
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hpNext : p.val + 1 < t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hnext
    let z : Fin t := ⟨p.val, by omega⟩
    have hprefix' : QuadraticSpace.Isometry
        ((strictWeak.toJordan hstrict).prefixSpace (z.val + 1))
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          R.component.val).space := by
      change QuadraticSpace.Isometry
        ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (p.val + 1)).space
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          R.component.val).space at hprefix
      simpa only [z] using hprefix
    rcases R.exists_boundaryPrefix_representation_to_diagonalModel_ii_of_first
        g hI hpositive hfirst hrank profile z hprefix'
      with ⟨target, hrep⟩
    let base :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
        b strictWeak hparity hstrict profile z
    have hboundaryComponentStop : (profile.boundaryIndex z).val + 1 =
        (BONG.WeakJordanOrderProfileWitness.ofStrict
          strictWeak hstrict profile).componentStop p := by
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
      have hIio : Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z) =
            insert p (Finset.Iio p) := by
        ext k
        simp only [Finset.mem_Iio, Finset.mem_insert]
        change k.val < z.val + 1 ↔ k = p ∨ k.val < p.val
        dsimp only [z]
        constructor
        · intro hk
          by_cases hkp : k.val = p.val
          · exact Or.inl (Fin.ext hkp)
          · exact Or.inr (by omega)
        · rintro (rfl | hk) <;> omega
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (strictWeak.component k).carrier at hb
      rw [hIio, Finset.sum_insert (by simp)] at hb
      change (profile.boundaryIndex z).val + 1 =
        (∑ k ∈ Finset.Iio p,
          finrank K (strictWeak.component k).carrier) +
            finrank K (strictWeak.component p).carrier
      simpa only [Nat.add_comm] using hb
    have hboundaryStop : (profile.boundaryIndex z).val + 1 =
        resolved.coordinates.stop := by
      simpa only [resolved, BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates] using
          hboundaryComponentStop
    have hindex : profile.boundaryIndex z = h := by
      apply Fin.ext
      have hJval : J.val = h.val := congrArg Fin.val hJ
      have hlast' : J.val + 1 = resolved.coordinates.stop := by
        simpa only [resolved] using hlast
      omega
    let source : BONG.GoodBONG.SpaceApproximationModel b h :=
      base.castIndex hindex
    refine ⟨source, target, ?_⟩
    exact base.castIndex_diagonalRepresents hindex hrep

set_option maxHeartbeats 0 in
/-- A resolved penultimate coordinate in a component of rank at least three
gives Lemma 3.7(iii).  The represented-line hypothesis is stated on the full
Jordan prefix, which is exactly what the notation `F L_(k) ⊤ [A_k]`
requires; it is deliberately weaker than integral representation by the
single component.  The result is packaged together with its representation
by any isometric target boundary prefix. -/
theorem exists_diagonalModel_iii_of_penultimate_with_representation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n m c d : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 2 < R.jordan.componentRank R.component)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (R.jordan.fundamentalLattice R.component) A)
    (hline : (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space.Represents
      (QuadraticSpace.scaledLine A))
    {M : Lattice K V}
    {b : BONG.GoodBONG q M (m + 2)}
    {H : Lattice.JordanDecomposition q M (d + 1)}
    (Q : BONG.JordanOrderProfileWitness b.toBONG H)
    (w : Fin d)
    (hprefix : QuadraticSpace.Isometry
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space
      (H.prefixSpace (w.val + 1))) :
    ∃ model : BONG.GoodBONG.DiagonalApproximationModel a g,
      DiagonalRepresents (diagonalUnitCoefficients model.units)
          (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w)) ∧
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (R.component.val + 1)).space.Represents
            (QuadraticSpace.finiteDiagonal
              (diagonalUnitCoefficients model.units)
              (QuadraticSpace.diagonalUnitCoefficients_ne_zero
                model.units)) := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let C := BONG.StrictCoordinateResolution.coordinates
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hpenultimate' : I.val + 2 = C.stop := by
      simpa only [C] using hpenultimate
    have hrankP : 2 < (strictWeak.toJordan hstrict).componentRank p := by
      simpa only [p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hcomponentNext' : p.val + 1 < t + 1 := by
      simpa only [p, BONG.StrictCoordinateResolution.component] using
        hcomponentNext
    let z : Fin t := ⟨p.val, by omega⟩
    have hleft :
        Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
      apply Fin.ext
      rfl
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
      rw [hleft]
      exact lt_trans (by omega) hrankP
    have hA' : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) A := by
      rw [hleft]
      exact hA
    have hline' : ((strictWeak.toJordan hstrict).prefixSpace
        (z.val + 1)).Represents (QuadraticSpace.scaledLine A) := by
      change ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)).space.Represents
          (QuadraticSpace.scaledLine A) at hline
      simpa only [z] using hline
    have hprefix' : QuadraticSpace.Isometry
        ((strictWeak.toJordan hstrict).prefixSpace (z.val + 1))
        (H.prefixSpace (w.val + 1)) := by
      change QuadraticSpace.Isometry
        ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (p.val + 1)).space
        (H.prefixSpace (w.val + 1)) at hprefix
      simpa only [z] using hprefix
    let B :=
      BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofLineRepresentation
        (P := profile) (z := z) (A := A) hline'
    have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < z.val + 1 ↔ k = p ∨ k.val < p.val
      dsimp only [z]
      constructor
      · intro hk
        by_cases hkp : k.val = p.val
        · exact Or.inl (Fin.ext hkp)
        · exact Or.inr (by omega)
      · rintro (rfl | hk) <;> omega
    have hboundaryStop : (profile.boundaryIndex z).val + 1 =
        (BONG.WeakJordanOrderProfileWitness.ofStrict
          strictWeak hstrict profile).componentStop p := by
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (strictWeak.component k).carrier at hb
      rw [hIio, Finset.sum_insert (by simp)] at hb
      change (profile.boundaryIndex z).val + 1 =
        (∑ k ∈ Finset.Iio p,
          finrank K (strictWeak.component k).carrier) +
            finrank K (strictWeak.component p).carrier
      simpa only [Nat.add_comm] using hb
    have hstop : (profile.boundaryIndex z).val + 1 =
        C.stop := by
      simpa only [BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, C] using
          hboundaryStop
    have hbefore := profile.boundaryOneBeforeIndex_succ_val z hrank'
    have hindex : profile.boundaryOneBeforeIndex z hrank' = g := by
      apply Fin.ext
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have hstartFormula :
        C.stop = C.start +
            (strictWeak.toJordan hstrict).componentRank p := by
      rfl
    have hstartLe : C.start ≤ I.val - 1 := by omega
    have hnextInside : (I.val - 1) + 2 < C.stop := by omega
    have hperiod := C.order_add_two_eq
      (I.val - 1) hstartLe hnextInside
    have houter : a.order
        ⟨(profile.boundaryOneBeforeIndex z hrank').val - 1, by omega⟩ =
      a.order ⟨(profile.boundaryOneBeforeIndex z hrank').val + 1,
        by omega⟩ := by
      have hbeforeVal :
          (profile.boundaryOneBeforeIndex z hrank').val = I.val := by
        have hIval : I.val = g.val := congrArg Fin.val hI
        have hindexVal := congrArg Fin.val hindex
        omega
      have hleftIndex (h : I.val - 1 <
          C.stop) : C.index (I.val - 1) h =
            ⟨(profile.boundaryOneBeforeIndex z hrank').val - 1,
              by omega⟩ := by
        apply Fin.ext
        change I.val - 1 =
          (profile.boundaryOneBeforeIndex z hrank').val - 1
        omega
      have hrightIndex (h : (I.val - 1) + 2 <
          C.stop) : C.index ((I.val - 1) + 2) h =
            ⟨(profile.boundaryOneBeforeIndex z hrank').val + 1,
              by omega⟩ := by
        apply Fin.ext
        change (I.val - 1) + 2 =
          (profile.boundaryOneBeforeIndex z hrank').val + 1
        omega
      simpa only [hleftIndex, hrightIndex] using hperiod
    let base :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37DiagonalModel_iii
        a strictWeak hparity hstrict profile z A hA' B hrank'
          (by
            rw [hindex]
            have hIval : I.val = g.val := congrArg Fin.val hI
            omega) houter
    let model := base.castIndex hindex
    refine ⟨model, ?_, ?_⟩
    have hrep := B.diagonalRepresents_boundaryPrefix_of_prefixIsometry
      Q w hrank' hprefix'
    exact base.castIndex_diagonalRepresents hindex hrep
    have hown := B.diagonalRepresents_boundaryPrefix hrank'
    have hfinite :
        (QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients (profile.boundaryPrefixDiagonalUnits z))
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero
            (profile.boundaryPrefixDiagonalUnits z))).Represents
          (QuadraticSpace.finiteDiagonal
            (diagonalUnitCoefficients model.units)
            (QuadraticSpace.diagonalUnitCoefficients_ne_zero model.units)) := by
      apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
        model.units (profile.boundaryPrefixDiagonalUnits z)).2
      exact base.castIndex_diagonalRepresents hindex hown
    let finiteToPrefix :=
      (profile.boundaryPrefixDiagonalizationIsometry z).symm.toRepresentation
    have hstruct : ((strictWeak.toJordan hstrict).prefixSpace
        (z.val + 1)).Represents
          (QuadraticSpace.finiteDiagonal
            (diagonalUnitCoefficients model.units)
            (QuadraticSpace.diagonalUnitCoefficients_ne_zero model.units)) :=
      ⟨finiteToPrefix.trans (Classical.choice hfinite)⟩
    change ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (p.val + 1)).space.Represents _
    simpa only [z] using hstruct

set_option maxHeartbeats 0 in
/-- A resolved penultimate coordinate of any component of rank at least two
gives the geometric model of Lemma 3.7(iii), provided its two outside BONG
orders agree.  Unlike the periodic high-rank wrapper above, this statement
keeps that equality explicit, so it also applies to binary components.  The
returned carrier is contained in the complete Jordan prefix from which the
represented norm-generator line is removed. -/
theorem exists_spaceModel_iii_of_penultimate_with_outer
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 1 < R.jordan.componentRank R.component)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (R.jordan.fundamentalLattice R.component) A)
    (hline : (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space.Represents
      (QuadraticSpace.scaledLine A))
    (houter : a.order
        ⟨g.val - 1, by have := g.isLt; omega⟩ =
      a.order ⟨g.val + 1, by have := g.isLt; omega⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      model.carrier ≤
        R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1) := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let C := BONG.StrictCoordinateResolution.coordinates
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hpenultimate' : I.val + 2 = C.stop := by
      simpa only [C] using hpenultimate
    have hrankP : 1 < (strictWeak.toJordan hstrict).componentRank p := by
      simpa only [p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hcomponentNext' : p.val + 1 < t + 1 := by
      simpa only [p, BONG.StrictCoordinateResolution.component] using
        hcomponentNext
    let z : Fin t := ⟨p.val, by omega⟩
    have hleft :
        Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
      apply Fin.ext
      rfl
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
      rw [hleft]
      exact hrankP
    have hA' : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) A := by
      rw [hleft]
      exact hA
    have hline' : ((strictWeak.toJordan hstrict).prefixSpace
        (z.val + 1)).Represents (QuadraticSpace.scaledLine A) := by
      change ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)).space.Represents
          (QuadraticSpace.scaledLine A) at hline
      simpa only [z] using hline
    let B :=
      BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofLineRepresentation
        (P := profile) (z := z) (A := A) hline'
    have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < z.val + 1 ↔ k = p ∨ k.val < p.val
      dsimp only [z]
      constructor
      · intro hk
        by_cases hkp : k.val = p.val
        · exact Or.inl (Fin.ext hkp)
        · exact Or.inr (by omega)
      · rintro (rfl | hk) <;> omega
    have hboundaryStop : (profile.boundaryIndex z).val + 1 =
        (BONG.WeakJordanOrderProfileWitness.ofStrict
          strictWeak hstrict profile).componentStop p := by
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (strictWeak.component k).carrier at hb
      rw [hIio, Finset.sum_insert (by simp)] at hb
      change (profile.boundaryIndex z).val + 1 =
        (∑ k ∈ Finset.Iio p,
          finrank K (strictWeak.component k).carrier) +
            finrank K (strictWeak.component p).carrier
      simpa only [Nat.add_comm] using hb
    have hstop : (profile.boundaryIndex z).val + 1 = C.stop := by
      simpa only [BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, C] using
          hboundaryStop
    have hbefore := profile.boundaryOneBeforeIndex_succ_val z hrank'
    have hindex : profile.boundaryOneBeforeIndex z hrank' = g := by
      apply Fin.ext
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have hpositive' : 0 <
        (profile.boundaryOneBeforeIndex z hrank').val := by
      rw [hindex]
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have houter' : a.order
        ⟨(profile.boundaryOneBeforeIndex z hrank').val - 1, by omega⟩ =
      a.order
        ⟨(profile.boundaryOneBeforeIndex z hrank').val + 1, by omega⟩ := by
      simpa only [hindex] using houter
    have happroximation : a.IsSpaceApproximation
        (profile.boundaryOneBeforeIndex z hrank')
        (B.approximationUnits hrank') :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_iii
        a strictWeak hparity hstrict profile z A hA' B hrank'
          hpositive' houter'
    let base : BONG.GoodBONG.SpaceApproximationModel a
        (profile.boundaryOneBeforeIndex z hrank') :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneBefore
        a (strictWeak.toJordan hstrict) profile z A B hrank' happroximation
    let model : BONG.GoodBONG.SpaceApproximationModel a g :=
      base.castIndex hindex
    refine ⟨model, ?_⟩
    have hcarrier :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneBefore_carrier_le
        a (strictWeak.toJordan hstrict) profile z A B hrank' happroximation
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    change base.carrier ≤
      ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)).carrier
    simpa only [base, z, B] using hcarrier

set_option maxHeartbeats 0 in
/-- Choice-flexible geometric form of resolved Lemma 3.7(iii).  The returned
model is the canonical orthogonal complement of the prescribed represented
fundamental generator; hence every vector in the complete component prefix
which is orthogonal to that generator belongs to the model. -/
theorem exists_spaceModel_iii_of_penultimate_with_generator
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 1 < R.jordan.componentRank R.component)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (G : BONG.RepresentedFundamentalNormGenerator R.jordan R.component)
    (v : (R.jordan.component R.component).carrier)
    (hv : (R.jordan.component R.component).space.quadratic v =
      (G.value : K))
    (houter : a.order
        ⟨g.val - 1, by have := g.isLt; omega⟩ =
      a.order ⟨g.val + 1, by have := g.isLt; omega⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      ∀ y : V,
        y ∈ R.jordan.toOrthogonalDecomposition.prefixCarrier
            (R.component.val + 1) →
          q.bilin y (v : V) = 0 →
          y ∈ model.carrier := by
  classical
  rcases R with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv I).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let C := BONG.StrictCoordinateResolution.coordinates
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hpenultimate' : I.val + 2 = C.stop := by
      simpa only [C] using hpenultimate
    have hrankP : 1 < (strictWeak.toJordan hstrict).componentRank p := by
      simpa only [p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hcomponentNext' : p.val + 1 < t + 1 := by
      simpa only [p, BONG.StrictCoordinateResolution.component] using
        hcomponentNext
    let z : Fin t := ⟨p.val, by omega⟩
    have hleft :
        Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
      apply Fin.ext
      rfl
    have hrank' : 1 < (strictWeak.toJordan hstrict).componentRank
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
      rw [hleft]
      exact hrankP
    have hA' : Lattice.IsNormGeneratorValue q
        ((strictWeak.toJordan hstrict).fundamentalLattice
          (Lattice.JordanDecomposition.boundaryLeftIndex z)) G.value := by
      rw [hleft]
      exact G.fundamental
    let J := strictWeak.toJordan hstrict
    have hxmem : (v : V) ∈
        J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := by
      apply J.toOrthogonalDecomposition.component_carrier_le_prefixCarrier
        p (by dsimp only [z]; omega)
      exact v.property
    let xv : (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (z.val + 1)).carrier :=
      ⟨(v : V), hxmem⟩
    have hxA : (J.prefixSpace (z.val + 1)).quadratic xv =
        (G.value : K) := hv
    let B :=
      BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel.ofRepresentedVector
        (P := profile) (z := z) (A := G.value) xv hxA
    have hIio : Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < z.val + 1 ↔ k = p ∨ k.val < p.val
      dsimp only [z]
      constructor
      · intro hk
        by_cases hkp : k.val = p.val
        · exact Or.inl (Fin.ext hkp)
        · exact Or.inr (by omega)
      · rintro (rfl | hk) <;> omega
    have hboundaryStop : (profile.boundaryIndex z).val + 1 =
        (BONG.WeakJordanOrderProfileWitness.ofStrict
          strictWeak hstrict profile).componentStop p := by
      have hb := profile.boundaryIndex_succ_val_eq_componentRankPrefix z
      change (profile.boundaryIndex z).val + 1 =
        ∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (strictWeak.component k).carrier at hb
      rw [hIio, Finset.sum_insert (by simp)] at hb
      change (profile.boundaryIndex z).val + 1 =
        (∑ k ∈ Finset.Iio p,
          finrank K (strictWeak.component k).carrier) +
            finrank K (strictWeak.component p).carrier
      simpa only [Nat.add_comm] using hb
    have hstop : (profile.boundaryIndex z).val + 1 = C.stop := by
      simpa only [BONG.StrictCoordinateResolution.coordinates,
        BONG.StrictCoordinateResolution.component,
        BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates, C] using
          hboundaryStop
    have hbefore := profile.boundaryOneBeforeIndex_succ_val z hrank'
    have hindex : profile.boundaryOneBeforeIndex z hrank' = g := by
      apply Fin.ext
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have hpositive' : 0 <
        (profile.boundaryOneBeforeIndex z hrank').val := by
      rw [hindex]
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have houter' : a.order
        ⟨(profile.boundaryOneBeforeIndex z hrank').val - 1, by omega⟩ =
      a.order
        ⟨(profile.boundaryOneBeforeIndex z hrank').val + 1, by omega⟩ := by
      simpa only [hindex] using houter
    have happroximation : a.IsSpaceApproximation
        (profile.boundaryOneBeforeIndex z hrank')
        (B.approximationUnits hrank') :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_iii
        a strictWeak hparity hstrict profile z G.value hA' B hrank'
          hpositive' houter'
    let base : BONG.GoodBONG.SpaceApproximationModel a
        (profile.boundaryOneBeforeIndex z hrank') :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_oneBefore_ofRepresentedVector
        a J profile z G.value xv hxA hrank' happroximation
    let model : BONG.GoodBONG.SpaceApproximationModel a g :=
      base.castIndex hindex
    refine ⟨model, ?_⟩
    intro y hyPrefix hyOrthogonal
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    apply BONG.JordanOrderProfileWitness.PrescribedJordanComparison.mem_spaceApproximationModel_oneBefore_ofRepresentedVector_carrier
      a J profile z G.value xv hxA hrank' happroximation y
    · change y ∈ J.toOrthogonalDecomposition.prefixCarrier (z.val + 1)
      simpa only [J, z, BONG.StrictCoordinateResolution.jordan,
        BONG.StrictCoordinateResolution.component] using hyPrefix
    · exact hyOrthogonal

set_option maxHeartbeats 0 in
/-- At the global zeroth coordinate, a resolved binary penultimate component
is the first strict Jordan component.  The right outer inequality and Lemma
3.6 make its chosen component norm generator fundamental and represented;
the endpoint form of Lemma 3.7(iv) then supplies the one-dimensional space
model contained in the complete component prefix. -/
theorem exists_spaceModel_iv_of_binary_penultimate_at_zero
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hzero : I.val = 0)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (hrightBound : I.val + 2 < n + 2)
    (hrightOuter : a.order I <
      a.order ⟨I.val + 2, hrightBound⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      model.carrier ≤
        R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1) := by
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
    let C := resolved.coordinates
    have hpzero : p.val = 0 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using resolved.component_val_eq_zero_of_index_val_eq_zero hzero
    have hpEq : p = (0 : Fin (t + 1)) := Fin.ext hpzero
    have hrankP : (strictWeak.toJordan hstrict).componentRank p = 2 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hpnext : p.val + 1 < t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hcomponentNext
    have hstartFormula : C.stop = C.start +
        (strictWeak.toJordan hstrict).componentRank p := by
      rfl
    have hpenultimate' : I.val + 2 = C.stop := by
      simpa only [resolved, C] using hpenultimate
    have hIStart : I.val = C.start := by omega
    have hstartSum : C.start =
        ∑ k ∈ Finset.Iio p,
          (strictWeak.toJordan hstrict).componentRank k := by
      rfl
    have hfirst : profile.profileComponentFirstIndex p = I := by
      apply Fin.ext
      rw [BONG.JordanOrderProfileWitness.profileComponentFirstIndex_val,
        ← hstartSum, hIStart]
    let pNext : Fin (t + 1) := ⟨p.val + 1, hpnext⟩
    have hIioNext : Finset.Iio pNext = insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < pNext.val ↔ k = p ∨ k.val < p.val
      dsimp only [pNext]
      constructor
      · intro hk
        by_cases heq : k.val = p.val
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (heq | hk)
        · subst k
          omega
        · omega
    have hnextFirst : profile.profileComponentFirstIndex pNext =
        ⟨I.val + 2, hrightBound⟩ := by
      apply Fin.ext
      change (profile.profileComponentFirstIndex pNext).val = I.val + 2
      rw [BONG.JordanOrderProfileWitness.profileComponentFirstIndex_val,
        hIioNext, Finset.sum_insert (by simp)]
      omega
    have hleftProfile : ∀ _hp : 0 < p.val,
        a.order (profile.profileComponentLastIndex
          ⟨p.val - 1, by omega⟩) <
        a.order (profile.profileComponentSecondIndex p (by omega)) := by
      intro hp
      omega
    have hrightProfile : ∀ hp : p.val + 1 < t + 1,
        a.order (profile.profileComponentFirstIndex p) <
        a.order (profile.profileComponentFirstIndex
          ⟨p.val + 1, hp⟩) := by
      intro hp
      have hnextEq : (⟨p.val + 1, hp⟩ : Fin (t + 1)) = pNext := by
        apply Fin.ext
        rfl
      rw [hfirst, hnextEq, hnextFirst]
      exact hrightOuter
    have heffectiveP := profile.beli2019Lemma36 strictWeak hparity hstrict
      p hrankP hleftProfile hrightProfile
    change strictWeak.effectiveNormOrderAt p
        (ordUnit K (strictWeak.scaleGenerator p)) =
      ordUnit K (strictWeak.normGeneratorUnit p) at heffectiveP
    have hmin : JordanProfileOrder.adjustedAt strictWeak.scaleOrderFamily
        strictWeak.normOrderFamily
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
    have hnonterminal : 1 < t + 1 := by omega
    have hrightProfileZero :
        ∀ hp : (0 : Fin (t + 1)).val + 1 < t + 1,
          a.order (profile.profileComponentFirstIndex 0) <
          a.order (profile.profileComponentFirstIndex
            ⟨(0 : Fin (t + 1)).val + 1, by omega⟩) := by
      simpa only [hpEq] using hrightProfile
    rcases BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37_iv_first_nonterminal
        a strictWeak hparity hstrict profile hnonterminal G.value
          (by rw [← hpEq]; exact G.fundamental)
          (by rw [← hpEq]; exact G.componentValue)
          (by rw [← hpEq]; exact hrankP) hrightProfileZero
      with ⟨_A', _M, _hrightRank, _hindex, happroximation,
        _hrightApproximation, _hmodels⟩
    let base :=
      BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_firstLine
        a G.value (G.vector : V) G.quadratic_ambientVector happroximation
    have hbaseCarrier : base.carrier ≤
        (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          (p.val + 1) := by
      exact BONG.JordanOrderProfileWitness.PrescribedJordanComparison.spaceApproximationModel_firstLine_carrier_le
        a G.value (G.vector : V) G.quadratic_ambientVector happroximation
          ((strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
            (p.val + 1))
          (G.vector_mem_prefixCarrier (Nat.lt_succ_self p.val))
    have hgzero : (0 : Fin (n + 1)) = g := by
      apply Fin.ext
      calc
        (0 : Fin (n + 1)).val = I.val := hzero.symm
        _ = g.castSucc.val := congrArg Fin.val hI
        _ = g.val := rfl
    let model : BONG.GoodBONG.SpaceApproximationModel a g :=
      base.castIndex hgzero
    refine ⟨model, ?_⟩
    rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
    simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
      BONG.StrictCoordinateResolution.jordan] using hbaseCarrier

set_option maxHeartbeats 0 in
/-- A resolved penultimate coordinate in an interior binary component satisfies
Lemma 3.7(iv) whenever both neighbouring outer two-step inequalities are
strict.  Lemma 3.6 supplies the represented fundamental norm generator, so
the resulting model has no additional representation-law hypothesis. -/
theorem exists_spaceModels_iv_of_binary_penultimate
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2)
    (hcomponentPositive : 0 < R.component.val)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (hrightBound : I.val + 2 < n + 2)
    (hleftOuter : a.order ⟨I.val - 1, by omega⟩ <
      a.order ⟨I.val + 1, by omega⟩)
    (hrightOuter : a.order I <
      a.order ⟨I.val + 2, hrightBound⟩) :
    ∃ (left right : BONG.GoodBONG.SpaceApproximationModel a g),
      R.jordan.toOrthogonalDecomposition.prefixCarrier R.component.val ≤
          left.carrier ∧
        left.carrier ≤
          R.jordan.toOrthogonalDecomposition.prefixCarrier
            (R.component.val + 1) ∧
        right.carrier ≤
          R.jordan.toOrthogonalDecomposition.prefixCarrier
            (R.component.val + 1) := by
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
    let C := resolved.coordinates
    have hpenultimate' : I.val + 2 = C.stop := by
      simpa only [resolved, C] using hpenultimate
    have hrankP : (strictWeak.toJordan hstrict).componentRank p = 2 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component,
        BONG.StrictCoordinateResolution.jordan] using hrank
    have hppos : 0 < p.val := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hcomponentPositive
    have hpnext : p.val + 1 < t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hcomponentNext
    have hstartFormula : C.stop = C.start +
        (strictWeak.toJordan hstrict).componentRank p := by
      rfl
    have hIStart : I.val = C.start := by omega
    have hstartSum : C.start =
        ∑ k ∈ Finset.Iio p,
          (strictWeak.toJordan hstrict).componentRank k := by
      rfl
    have hfirst : profile.profileComponentFirstIndex p = I := by
      apply Fin.ext
      rw [BONG.JordanOrderProfileWitness.profileComponentFirstIndex_val,
        ← hstartSum, hIStart]
    have hsecond : profile.profileComponentSecondIndex p (by omega) =
        ⟨I.val + 1, by omega⟩ := by
      apply Fin.ext
      change (profile.profileComponentSecondIndex p (by omega)).val =
        I.val + 1
      rw [BONG.JordanOrderProfileWitness.profileComponentSecondIndex_val,
        ← hstartSum]
      omega
    let pPrev : Fin (t + 1) := ⟨p.val - 1, by omega⟩
    let pNext : Fin (t + 1) := ⟨p.val + 1, hpnext⟩
    have hIioPrev : Finset.Iio p = insert pPrev (Finset.Iio pPrev) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < p.val ↔ k = pPrev ∨ k.val < pPrev.val
      dsimp only [pPrev]
      constructor
      · intro hk
        by_cases heq : k.val = p.val - 1
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (heq | hk)
        · subst k
          dsimp only [pPrev]
          omega
        · omega
    have hprevRankPos : 0 <
        (strictWeak.toJordan hstrict).componentRank pPrev :=
      strictWeak.component_finrank_pos pPrev
    have hprevSum : C.start =
        (strictWeak.toJordan hstrict).componentRank pPrev +
          ∑ k ∈ Finset.Iio pPrev,
            (strictWeak.toJordan hstrict).componentRank k := by
      rw [hstartSum, hIioPrev, Finset.sum_insert (by simp)]
    have hprevLast : profile.profileComponentLastIndex pPrev =
        ⟨I.val - 1, by omega⟩ := by
      apply Fin.ext
      change (profile.profileComponentLastIndex pPrev).val = I.val - 1
      rw [BONG.JordanOrderProfileWitness.profileComponentLastIndex_val]
      omega
    have hIioNext : Finset.Iio pNext = insert p (Finset.Iio p) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert]
      change k.val < pNext.val ↔ k = p ∨ k.val < p.val
      dsimp only [pNext]
      constructor
      · intro hk
        by_cases heq : k.val = p.val
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr (by omega)
      · rintro (heq | hk)
        · subst k
          omega
        · omega
    have hnextFirst : profile.profileComponentFirstIndex pNext =
        ⟨I.val + 2, hrightBound⟩ := by
      apply Fin.ext
      change (profile.profileComponentFirstIndex pNext).val = I.val + 2
      rw [BONG.JordanOrderProfileWitness.profileComponentFirstIndex_val,
        hIioNext, Finset.sum_insert (by simp)]
      omega
    have hleftProfile : ∀ _hp : 0 < p.val,
        a.order (profile.profileComponentLastIndex
          ⟨p.val - 1, by omega⟩) <
        a.order (profile.profileComponentSecondIndex p (by omega)) := by
      intro _hp
      simpa only [show (⟨p.val - 1, by omega⟩ : Fin (t + 1)) = pPrev by
          apply Fin.ext; rfl,
        hprevLast, hsecond] using hleftOuter
    have hrightProfile : ∀ hp : p.val + 1 < t + 1,
        a.order (profile.profileComponentFirstIndex p) <
        a.order (profile.profileComponentFirstIndex
          ⟨p.val + 1, hp⟩) := by
      intro hp
      have hnextEq : (⟨p.val + 1, hp⟩ : Fin (t + 1)) = pNext := by
        apply Fin.ext
        rfl
      rw [hfirst, hnextEq, hnextFirst]
      exact hrightOuter
    have heffectiveP := profile.beli2019Lemma36 strictWeak hparity hstrict
      p hrankP hleftProfile hrightProfile
    change strictWeak.effectiveNormOrderAt p
        (ordUnit K (strictWeak.scaleGenerator p)) =
      ordUnit K (strictWeak.normGeneratorUnit p) at heffectiveP
    have hmin : JordanProfileOrder.adjustedAt strictWeak.scaleOrderFamily
        strictWeak.normOrderFamily
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
    rcases BONG.JordanOrderProfileWitness.PrescribedJordanComparison.exists_beli2019Lemma37Models_iv_interior
        a strictWeak hparity hstrict profile p hppos hpnext G.value
          G.fundamental G.componentValue hrankP hleftProfile hrightProfile
      with ⟨hleftRank, hrightRank, left, right, hmodelsIndex,
        hleftLower, hleftCarrier, hrightCarrier⟩
    let zLeft : Fin t := ⟨p.val - 1, by omega⟩
    let zRight : Fin t := ⟨p.val, by omega⟩
    have hboundary := profile.boundaryIndex_succ_val_eq_componentRankPrefix
      zRight
    have hrightComponent :
        Lattice.JordanDecomposition.boundaryRightIndex zRight = pNext := by
      apply Fin.ext
      rfl
    rw [hrightComponent, hIioNext,
      Finset.sum_insert (by simp)] at hboundary
    have hbefore := profile.boundaryOneBeforeIndex_succ_val
      zRight hrightRank
    have hsum :
        (∑ k ∈ Finset.Iio p,
          (strictWeak.toJordan hstrict).componentRank k) = I.val :=
      hstartSum.symm.trans hIStart.symm
    have hboundary' : (profile.boundaryIndex zRight).val + 1 =
        2 + ∑ k ∈ Finset.Iio p,
          (strictWeak.toJordan hstrict).componentRank k := by
      calc
        (profile.boundaryIndex zRight).val + 1 =
            (strictWeak.toJordan hstrict).componentRank p +
              ∑ k ∈ Finset.Iio p,
                (strictWeak.toJordan hstrict).componentRank k := hboundary
        _ = _ := by rw [hrankP]
    have hboundaryVal : (profile.boundaryIndex zRight).val =
        I.val + 1 := by
      omega
    have hindex : profile.boundaryOneBeforeIndex zRight hrightRank = g := by
      apply Fin.ext
      have hIval : I.val = g.val := congrArg Fin.val hI
      omega
    have hleftIndex : profile.boundaryOneAfterIndex zLeft hleftRank = g := by
      exact hmodelsIndex.trans hindex
    let leftModel : BONG.GoodBONG.SpaceApproximationModel a g :=
      left.castIndex hleftIndex
    let rightModel : BONG.GoodBONG.SpaceApproximationModel a g :=
      right.castIndex hindex
    refine ⟨leftModel, rightModel, ?_, ?_, ?_⟩
    · rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
      change (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          p.val ≤ left.carrier
      simpa only [zLeft, zRight] using hleftLower
    · rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
      change left.carrier ≤
        (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          (p.val + 1)
      simpa only [zLeft, zRight] using hleftCarrier
    · rw [BONG.GoodBONG.SpaceApproximationModel.castIndex_carrier]
      change right.carrier ≤
        (strictWeak.toJordan hstrict).toOrthogonalDecomposition.prefixCarrier
          (p.val + 1)
      simpa only [zLeft, zRight] using hrightCarrier

set_option maxHeartbeats 0 in
/-- The right/complement model in the binary case-(iv) pair. -/
theorem exists_spaceModel_iv_of_binary_penultimate
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2)
    (hcomponentPositive : 0 < R.component.val)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (hrightBound : I.val + 2 < n + 2)
    (hleftOuter : a.order ⟨I.val - 1, by omega⟩ <
      a.order ⟨I.val + 1, by omega⟩)
    (hrightOuter : a.order I <
      a.order ⟨I.val + 2, hrightBound⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      model.carrier ≤
        R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1) := by
  rcases R.exists_spaceModels_iv_of_binary_penultimate g hI hpositive
      hpenultimate hrank hcomponentPositive hcomponentNext hrightBound
        hleftOuter hrightOuter with
          ⟨_left, right, _hleftLower, _hleft, hright⟩
  exact ⟨right, hright⟩

set_option maxHeartbeats 0 in
/-- The left/prefix-plus-line model in the same binary case-(iv) pair. -/
theorem exists_leftSpaceModel_iv_of_binary_penultimate
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n c : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2)
    (hcomponentPositive : 0 < R.component.val)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (hrightBound : I.val + 2 < n + 2)
    (hleftOuter : a.order ⟨I.val - 1, by omega⟩ <
      a.order ⟨I.val + 1, by omega⟩)
    (hrightOuter : a.order I <
      a.order ⟨I.val + 2, hrightBound⟩) :
    ∃ model : BONG.GoodBONG.SpaceApproximationModel a g,
      R.jordan.toOrthogonalDecomposition.prefixCarrier R.component.val ≤
          model.carrier ∧
        model.carrier ≤
        R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1) := by
  rcases R.exists_spaceModels_iv_of_binary_penultimate g hI hpositive
      hpenultimate hrank hcomponentPositive hcomponentNext hrightBound
        hleftOuter hrightOuter with
          ⟨left, _right, hleftLower, hleft, _hright⟩
  exact ⟨left, hleftLower, hleft⟩

set_option maxHeartbeats 0 in
/-- High-rank form of the preceding construction.  Quaternary universality
discharges the represented-line premise, so no component-representation law
is required. -/
theorem exists_diagonalModel_iii_of_penultimate_of_four_le
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n m c d : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 2 < R.jordan.componentRank R.component)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (R.jordan.fundamentalLattice R.component) A)
    (hfour : 4 ≤ finrank K
      (R.jordan.toOrthogonalDecomposition.prefixCarrier
        (R.component.val + 1)))
    {M : Lattice K V} {b : BONG.GoodBONG q M (m + 2)}
    {H : Lattice.JordanDecomposition q M (d + 1)}
    (Q : BONG.JordanOrderProfileWitness b.toBONG H)
    (w : Fin d)
    (hprefix : QuadraticSpace.Isometry
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space
      (H.prefixSpace (w.val + 1))) :
    ∃ model : BONG.GoodBONG.DiagonalApproximationModel a g,
      DiagonalRepresents (diagonalUnitCoefficients model.units)
        (diagonalUnitCoefficients (Q.boundaryPrefixDiagonalUnits w)) := by
  letI : Module.Finite K V := L.moduleFinite
  have hline :=
    (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
      (R.component.val + 1)).space.represents_scaledLine_of_four_le_finrank
        A hfour
  rcases R.exists_diagonalModel_iii_of_penultimate_with_representation
      g hI hpositive hpenultimate hrank hcomponentNext A hA hline Q w hprefix
    with ⟨model, hrep, _hstruct⟩
  exact ⟨model, hrep⟩

set_option maxHeartbeats 0 in
/-- Pair a resolved source case-(iii) model with a resolved target
case-(i) model.  The only cross-lattice datum is the isometry of the two
complete prefixes; the source line representation and both approximation
proofs are constructed on their own sides. -/
theorem exists_models_iii_to_i_of_prefixIsometry
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n m c d : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {W : Lattice.WeakJordanDecomposition q L c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (n + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (g : Fin (n + 1)) (hI : I = g.castSucc)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : 2 < R.jordan.componentRank R.component)
    (hcomponentNext : R.component.val + 1 < R.componentCount)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (R.jordan.fundamentalLattice R.component) A)
    (hline : (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space.Represents
      (QuadraticSpace.scaledLine A))
    {M : Lattice K V} {b : BONG.GoodBONG q M (m + 2)}
    {T : Lattice.WeakJordanDecomposition q M d}
    {y : BONG.WeakJordanOrderProfileWitness b.toBONG T}
    {J : Fin (m + 2)}
    (S : StrictCoordinateResolution b.toBONG T y J)
    (h : Fin (m + 1)) (hJ : J = h.castSucc)
    (hlast : J.val + 1 = S.coordinates.stop)
    (hnext : S.component.val + 1 < S.componentCount)
    (hprefix : QuadraticSpace.Isometry
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (R.component.val + 1)).space
      (S.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        (S.component.val + 1)).space) :
    ∃ (source : BONG.GoodBONG.DiagonalApproximationModel a g)
      (target : BONG.GoodBONG.SpaceApproximationModel b h),
      DiagonalRepresents (diagonalUnitCoefficients source.units)
        (diagonalUnitCoefficients target.units) := by
  classical
  rcases S with ⟨componentCount, strictWeak, hstrict, hparity, profile,
    offset, hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
  let p := (profile.indexEquiv J).1
  cases componentCount with
  | zero => exact Fin.elim0 p
  | succ t =>
    let resolved : StrictCoordinateResolution b.toBONG T y J :=
      ⟨Nat.succ t, strictWeak, hstrict, hparity, profile, offset,
        hlocal, hcomponent, hprefixComponents, hscale, heffective⟩
    have hpNext : p.val + 1 < t + 1 := by
      simpa only [resolved, p, BONG.StrictCoordinateResolution.component]
        using hnext
    let z : Fin t := ⟨p.val, by omega⟩
    have hprefix' : QuadraticSpace.Isometry
        (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          (R.component.val + 1)).space
        ((strictWeak.toJordan hstrict).prefixSpace (z.val + 1)) := by
      change QuadraticSpace.Isometry _
        ((strictWeak.toJordan hstrict).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (p.val + 1)).space at hprefix
      simpa only [z] using hprefix
    rcases R.exists_diagonalModel_iii_of_penultimate_with_representation
        g hI hpositive hpenultimate hrank hcomponentNext A hA hline
          profile z hprefix'
      with ⟨source, hrep, _hstruct⟩
    let target : BONG.GoodBONG.SpaceApproximationModel b h :=
      resolved.spaceModel_i_of_last h hJ (by
        simpa only [resolved] using hlast) (by
          simpa only [resolved] using hnext)
    refine ⟨source, target, ?_⟩
    change DiagonalRepresents (diagonalUnitCoefficients source.units)
      (diagonalUnitCoefficients
        ((BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
          b strictWeak hparity hstrict profile z).castIndex _).units)
    exact
      (BONG.JordanOrderProfileWitness.PrescribedJordanComparison.beli2019Lemma37Model_i
        b strictWeak hparity hstrict profile z).castIndex_diagonalRepresentedBy
          _ hrep

end BONG.StrictCoordinateResolution

end Bong
