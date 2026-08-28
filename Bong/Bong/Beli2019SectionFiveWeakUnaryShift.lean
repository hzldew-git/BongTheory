/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveOddBound
import Bong.Bong.Beli2019Lemma517CollisionProfiles
import Bong.Bong.Beli2019SectionFiveGapTwoAlpha
import Bong.Bong.Beli2019Lemma515
import Bong.Bong.BinaryModularInvariant
import Bong.Bong.Beli2019PrefixThroughApproximation
import Bong.Bong.Beli2019SectionFiveWeakAligned

/-!
# Collision-safe weak unary-shift direct range

This module proves the direct Lemma 5.17 range of condition 2.1(ii) when a
rank-one selected component crosses the unique common Jordan component of
intermediate scale.  Both almost-Jordan decompositions may contain their
unique scale collision.  In particular, the selected unary boundary is
resolved through the collision-safe Lemma 5.13 determinant argument rather
than by assuming strict Jordan decompositions.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Before the exceptional unary transposition, the two weak profiles use
the same numerical component and local coordinate. -/
theorem weakUnaryDirect_coordinates_eq_before
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
        ((D.smallWeakProfileWitness b).indexEquiv I).2.val :=
  D.weakUnaryShift_profile_coordinates_eq_before hfin i₀ hi₀ a b I hbefore

/-- A large weak coordinate before the selected unary component is also
strictly before the small selected component. -/
theorem weakUnaryDirect_small_before
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
    ((D.smallWeakProfileWitness b).indexEquiv I).1 <
      D.smallSelectedPosition := by
  have hcoordinates :=
    D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hadjacent :=
    D.smallSelectedPosition_val_eq_large_add_one_of_rank_one hfin i₀ hi₀
  change ((D.smallWeakProfileWitness b).indexEquiv I).1.val <
    D.smallSelectedPosition.val
  change ((D.largeWeakProfileWitness a).indexEquiv I).1.val <
    D.largeSelectedPosition.val at hbefore
  have hposition := congrArg Fin.val hcoordinates.1
  omega

/-- Component ranks agree before the exceptional unary transposition. -/
theorem weakUnaryDirect_componentRank_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hbefore : p < D.largeSelectedPosition) :
    finrank K (D.largeAlmostJordan.component p).carrier =
      finrank K (D.smallAlmostJordan.component p).carrier := by
  rw [D.unaryShift_component_eq_before hfin i₀ hi₀ p hbefore]

/-- Scale interval needed by the collision-resolved fundamental-lattice
comparison before the unary exceptional transposition. -/
theorem weakUnaryDirect_fundamentalScale_interval_before
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
    let pLarge := ((D.largeWeakProfileWitness a).indexEquiv I).1
    let pSmall := ((D.smallWeakProfileWitness b).indexEquiv I).1
    ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
        ordUnit K (D.smallAlmostJordan.scaleGenerator pSmall) ∧
      ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
  dsimp only
  have hcoordinates :=
    D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hscale := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀
      ((D.largeWeakProfileWitness a).indexEquiv I).1 hbefore
  constructor
  · rw [← hcoordinates.1]
    exact hscale.le
  · have hmono := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hmono

/-- Reuse the complete adjacent-unary order certificate at an arbitrary
coordinate. -/
theorem weakUnaryDirect_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : Nat) (hi : i < n) :
    Beli2019IndexPOrderCoordinateCertificate
      a.orderSequence b.orderSequence i hi :=
  (D.weakUnaryShift_orderCertificate hfin i₀ hi₀ a b).coordinate i hi

/-- The literal Lemma 5.17 range lies inside the direct reduced range in the
adjacent unary case.  The latter extends through the common component moved
across the selected unary block. -/
theorem weakUnaryDirect_defectReducedRange_of_lemma517Range
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i) : D.DefectReducedRange i := by
  have hstart := D.weakUnaryShift_smallSelectedStart_eq_intervalEnd
    hfin i₀ hi₀
  change D.smallSelectedStart = D.largeSelectedStart +
    finrank K (D.complementStrictWeak.component i₀).carrier at hstart
  have hcommonRankPos :
      0 < finrank K (D.complementStrictWeak.component i₀).carrier :=
    D.complementStrictWeak.component_finrank_pos i₀
  change i.val ≤ D.largeSelectedStart +
    finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1 at hi
  change i.val ≤ D.smallSelectedStart +
    finrank K
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
  rw [D.largeAlmostJordan_finrank_selected, hfin] at hi
  rw [D.smallAlmostJordan_finrank_selected, hfin, hstart]
  omega
/-- In the aligned case, collision resolution does not change the common
block start at a coordinate strictly before the selected component. -/
theorem weakUnaryDirect_strictResolution_start_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      exact (D.weakUnaryDirect_small_before
        hfin i₀ hi₀ a b I hbefore).le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    Rlarge.coordinates.start = Rsmall.coordinates.start := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hstartLarge := Rlarge.coordinates_start_add_offset_eq_weak_componentStart
  have hstartSmall := Rsmall.coordinates_start_add_offset_eq_weak_componentStart
  rw [hoffLarge, Nat.add_zero] at hstartLarge
  rw [hoffSmall, Nat.add_zero] at hstartSmall
  have hweakStart : x.componentStart (x.indexEquiv I).1 =
      y.componentStart (y.indexEquiv I).1 := by
    rw [hcoordinates.1]
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < (x.indexEquiv I).1 := by
      rw [hcoordinates.1]
      simpa only [Finset.mem_Iio] using hk
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ k
      (hk'.trans hbefore)
  exact hstartLarge.trans (hweakStart.trans hstartSmall.symm)

/-- The resolved local coordinates also agree strictly before the aligned
selected component. -/
theorem weakUnaryDirect_strictResolution_local_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      exact (D.weakUnaryDirect_small_before
        hfin i₀ hi₀ a b I hbefore).le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    (Rlarge.profile.indexEquiv I).2.val =
      (Rsmall.profile.indexEquiv I).2.val := by
  dsimp only
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hsmallBefore :
      ((D.smallWeakProfileWitness b).indexEquiv I).1 <
        D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  rw [Rlarge.localCoordinate_eq, Rsmall.localCoordinate_eq,
    hoffLarge, hoffSmall, hcoordinates.2]

/-- The determinant seeds of the two collision-resolved blocks differ by a
square at every coordinate strictly before the aligned selected component.
The proof compares equal-length prefixes of strict decompositions whose
ambient component counts may differ. -/
theorem weakUnaryDirect_strictResolution_determinantSeeds_square_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      exact (D.weakUnaryDirect_small_before
        hfin i₀ hi₀ a b I hbefore).le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    ∃ s : Kˣ,
      Rsmall.determinantSeedData.leftDet =
        Rlarge.determinantSeedData.leftDet * s ^ 2 := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hcomponentLarge : Rlarge.component.val = (x.indexEquiv I).1.val :=
    Rlarge.component_val_eq_of_offset_zero hoffLarge
  have hcomponentSmall : Rsmall.component.val = (y.indexEquiv I).1.val :=
    Rsmall.component_val_eq_of_offset_zero hoffSmall
  have hcomponentVal : Rlarge.component.val = Rsmall.component.val :=
    hcomponentLarge.trans <|
      (congrArg Fin.val hcoordinates.1).trans hcomponentSmall.symm
  by_cases hpzero : Rlarge.component.val = 0
  · have hsmallZero : Rsmall.component.val = 0 := hcomponentVal.symm.trans hpzero
    refine ⟨1, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_zero hsmallZero,
      Rlarge.determinantSeedData_leftDet_of_component_zero hpzero]
    simp
  · let cut := Rlarge.component.val
    let P := Rlarge.jordan.toOrthogonalDecomposition
    let Q := Rsmall.jordan.toOrthogonalDecomposition
    have hcut : cut - 1 + 1 = cut := by
      dsimp only [cut]
      omega
    have hP : cut - 1 + 1 ≤ Rlarge.componentCount := by
      rw [hcut]
      exact Rlarge.component.isLt.le
    have hQ : cut - 1 + 1 ≤ Rsmall.componentCount := by
      rw [hcut]
      have hsmallLt := Rsmall.component.isLt
      omega
    have hprefixComponent (z : Fin (cut - 1 + 1)) :
        P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
          Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
      let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
      let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
      have hjPVal : jP.val = z.val := by
        exact P.prefixIndexEquiv_val (cut - 1 + 1) hP z
      have hjQVal : jQ.val = z.val := by
        exact Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
      have hzCut : z.val < cut := by
        have hz := z.isLt
        omega
      have hjP : jP < Rlarge.component := by
        change jP.val < Rlarge.component.val
        dsimp only [cut] at hzCut
        omega
      have hjQ : jQ < Rsmall.component := by
        change jQ.val < Rsmall.component.val
        omega
      obtain ⟨oldP, holdPVal, holdP⟩ :=
        Rlarge.prefixComponent_eq jP hjP
      obtain ⟨oldQ, holdQVal, holdQ⟩ :=
        Rsmall.prefixComponent_eq jQ hjQ
      have holdEq : oldP = oldQ := by
        apply Fin.ext
        rw [holdPVal, holdQVal, hjPVal, hjQVal]
      have holdPBefore : oldP < D.largeSelectedPosition := by
        change oldP.val < D.largeSelectedPosition.val
        calc
          oldP.val = jP.val := holdPVal
          _ < Rlarge.component.val := hjP
          _ = (x.indexEquiv I).1.val := hcomponentLarge
          _ < D.largeSelectedPosition.val := hbefore
      change Rlarge.strictWeak.component jP = Rsmall.strictWeak.component jQ
      rw [holdP, holdQ, ← holdEq]
      exact D.unaryShift_component_eq_before hfin i₀ hi₀ oldP holdPBefore
    have hsquare :=
      P.exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry_of_differentCounts
        Q hP hQ (fun z ↦ by
          rw [hprefixComponent z]
          exact Lattice.Isometry.refl _ _)
    rcases hsquare with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_ne_zero (by
        omega),
      Rlarge.determinantSeedData_leftDet_of_component_ne_zero hpzero]
    change
      (Q.prefixQuadraticSublattice Rsmall.component.val).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice Rlarge.component.val).refinedDeterminantUnit *
          s ^ 2
    rw [← hcomponentVal]
    simpa only [hcut] using hs

/-- At an odd local boundary, a one-step rise of the two weak effective norm
orders would force exactly the current-order jump excluded in Lemma 5.13. -/
theorem weakUnaryDirect_effectiveNormOrder_ne_add_one_of_current_ne
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hodd : Odd ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).2.val)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
    let x := D.largeWeakProfileWitness a
    let p := (x.indexEquiv R).1
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    D.smallAlmostJordan.effectiveNormOrderAt p target ≠
      D.largeAlmostJordan.effectiveNormOrderAt p target + 1 := by
  dsimp only
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv R).1
  let j := (x.indexEquiv R).2.val
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  change (x.indexEquiv R).1 < D.largeSelectedPosition at hbefore
  change Odd j at hodd
  intro hone
  apply hcurrent
  rcases hodd with ⟨k, hk⟩
  let I : Fin (n + 2) := ⟨i.val - 1, by
    have := i.pos
    have := i.lt_large
    omega⟩
  let localPrevious : Fin
      (finrank K (D.largeAlmostJordan.component p).carrier) :=
    ⟨j - 1, by
      have hjlt := (x.indexEquiv R).2.isLt
      change j < finrank K (D.largeAlmostJordan.component p).carrier at hjlt
      omega⟩
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = x.componentStart p + j := by
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    simpa only [R, p, j] using hglobal
  have hI : I = x.indexEquiv.symm ⟨p, localPrevious⟩ := by
    apply Fin.ext
    rw [x.inverse_index_val]
    change i.val - 1 = x.componentStart p + (j - 1)
    rw [hiStart]
    omega
  have hxI : x.indexEquiv I = ⟨p, localPrevious⟩ := by
    rw [hI, x.indexEquiv.apply_symm_apply]
  have hbeforeI : (x.indexEquiv I).1 < D.largeSelectedPosition := by
    rw [hxI]
    simpa only [p] using hbefore
  have hxyI := D.weakUnaryDirect_coordinates_eq_before
    hfin i₀ hi₀ a b I hbeforeI
  have hscale : ordUnit K (D.smallAlmostJordan.scaleGenerator p) = target :=
    (D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ p hbefore).symm
  have hevenPrevious : Even (j - 1) := ⟨k, by omega⟩
  have hlargeScale : target ≤
      D.largeAlmostJordan.effectiveNormOrderAt p target :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p target
  have hsmallScale : target ≤
      D.smallAlmostJordan.effectiveNormOrderAt p target := by
    rw [← hscale]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt p
      (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
  have hlargeOrder := D.largeWeak_order_eq_localOrder a I
  have hsmallOrder := D.smallWeak_order_eq_localOrder b I
  have hxIPosition : (x.indexEquiv I).1 = p := by rw [hxI]
  have hxILocal : (x.indexEquiv I).2.val = j - 1 := by rw [hxI]
  have hyIPosition : (y.indexEquiv I).1 = p :=
    hxyI.1.symm.trans hxIPosition
  have hyILocal : (y.indexEquiv I).2.val = j - 1 :=
    hxyI.2.symm.trans hxILocal
  have hlargeOrder' : a.order I =
      JordanProfileOrder.localOrder target
        (D.largeAlmostJordan.effectiveNormOrderAt p target) (j - 1) := by
    simpa only [x, hxIPosition, hxILocal, target] using hlargeOrder
  have hsmallOrder' : b.order I =
      JordanProfileOrder.localOrder target
        (D.smallAlmostJordan.effectiveNormOrderAt p target) (j - 1) := by
    simpa only [y, hyIPosition, hyILocal, hscale, target] using hsmallOrder
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hlargeScale hevenPrevious] at hlargeOrder'
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsmallScale hevenPrevious] at hsmallOrder'
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (by have := i.lt_large; omega),
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence
      (by have := i.lt_large; omega)]
  change b.order I = a.order I + 1
  exact hsmallOrder'.trans <| hone.trans <|
    congrArg (fun z : Int ↦ z + 1) hlargeOrder'.symm

/-- Lemma 5.13(i) at every aligned coordinate strictly before the selected
component, allowing either or both almost-Jordan families to contain their
unique scale collision. -/
theorem weakUnaryDirect_commonApproximation_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let j := (x.indexEquiv I).2.val
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  let C := Rlarge.coordinates
  let E := Rsmall.coordinates
  let dLarge := Rlarge.determinantSeedData
  let dSmall := Rsmall.determinantSeedData
  have hstart : C.start = E.start := by
    exact D.weakUnaryDirect_strictResolution_start_eq_before_selected
      hfin i₀ hi₀ a b I hbefore
  have hlocal : (Rlarge.profile.indexEquiv I).2.val = j := by
    have hoff :=
      D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
        a I hlargeLe hbefore
    rw [Rlarge.localCoordinate_eq, hoff, Nat.zero_add]
  have hiStartRaw := Rlarge.index_val_eq_coordinates_start_add_local
  have hiStart : i.val = C.start + j := by
    rw [hlocal] at hiStartRaw
    exact hiStartRaw
  have hiC : i.val < C.stop := Rlarge.index_val_lt_coordinates_stop
  have hiE : i.val < E.stop := Rsmall.index_val_lt_coordinates_stop
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.weakUnaryDirect_strictResolution_determinantSeeds_square_before_selected
      hfin i₀ hi₀ a b I hbefore
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt p target
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt p target
  have hscale : ordUnit K (D.smallAlmostJordan.scaleGenerator p) = target :=
    (D.weakUnaryShift_scaleOrder_eq_before_selected hfin i₀ hi₀ p hbefore).symm
  have htargetLarge : target ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [target, D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hinclude : Rsmall.fundamentalLattice ≤ Rlarge.fundamentalLattice := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation,
      Rlarge.fundamentalLattice_eq_scaleTruncation]
    change Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) ≤
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
    rw [← hcoordinates.1, hscale]
    exact D.scaleTruncation_small_le_large target htargetLarge
  have hrescale : Lattice.rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))) ≤
      Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
    rw [← hcoordinates.1, hscale]
    exact D.rescale_largeScaleTruncation_le_small target
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := Rlarge.approximationSeedsWith dLarge
      Rlarge.fundamentalNormGenerator Rlarge.fundamentalNormGenerator_spec
    let T := Rsmall.approximationSeedsWith dSmall
      Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
    have hdet' : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2 := by
      simpa only [S, T,
        BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using hdet
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet'
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    have hbounds := D.common_effectiveNormOrder_bounds p hbefore
    change eLarge ≤ eSmall ∧ eSmall ≤ eLarge + 2 at hbounds
    have hcases : eSmall = eLarge ∨ eSmall = eLarge + 1 ∨
        eSmall = eLarge + 2 := by omega
    have hnotOne : eSmall ≠ eLarge + 1 := by
      exact D.weakUnaryDirect_effectiveNormOrder_ne_add_one_of_current_ne
        hfin i₀ hi₀ a b i hbefore ⟨k, hk⟩ hcurrent
    have heffectiveEq (hzero : eSmall = eLarge) :
        D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)) =
          D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) := by
      change eLarge = _
      rw [← hcoordinates.1, hscale]
      exact hzero.symm
    have heffectiveTwo (htwo : eSmall = eLarge + 2) :
        D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) =
          D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
              (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)) + 2 := by
      rw [← hcoordinates.1, hscale]
      exact htwo
    rcases hcases with hzero | hone | htwo
    · obtain ⟨A, hALarge, hASmall⟩ :=
        Rlarge.exists_commonNormGenerator_of_effective_eq Rsmall hinclude
          (heffectiveEq hzero)
      let S := Rlarge.approximationSeedsWith dLarge A hALarge
      let T := Rsmall.approximationSeedsWith dSmall A hASmall
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · exact (hnotOne hone).elim
    · have hpos : 0 < finrank K V := by
        rw [← a.toBONG.length_eq_finrank]
        omega
      have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
        hpos hrescale (heffectiveTwo htwo)
      let A := Rlarge.fundamentalNormGenerator
      let B := (uniformizerUnit K) ^ 2 * A
      let S := Rlarge.approximationSeedsWith dLarge A hpair.1
      let T := Rsmall.approximationSeedsWith dSmall B hpair.2
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

/-- Collision-safe gap-two weight equality at an aligned coordinate before
the selected component. -/
theorem weakUnaryDirect_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    Lattice.weightIdeal q
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1))) =
      Lattice.weightIdeal q
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            ((D.smallWeakProfileWitness b).indexEquiv i.castSucc).1))) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective :=
    D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates :=
    D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hsmallBefore : r < D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by
        change b.order i.castSucc < a.order i.castSucc
        omega
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap : targetEffective = sourceEffective + 2 := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
      at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
      at htargetLocalNormalized
    change a.order I = b.order I + 2 at hcurrent
    omega
  let Rlarge := D.largeStrictCoordinateResolution a I hbefore.le
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBefore.le
  have hrescale : Lattice.rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p))) ≤
      Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp, hscaleRaw]
    exact D.rescale_largeScaleTruncation_le_small
      (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
  have hpos : 0 < finrank K V := by
    rw [← a.toBONG.length_eq_finrank]
    omega
  have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
    hpos hrescale (by
      change targetEffective = sourceEffective + 2
      exact heffectiveGap)
  let A := Rlarge.fundamentalNormGenerator
  change Lattice.IsNormGeneratorValue q Rlarge.fundamentalLattice A ∧
      Lattice.IsNormGeneratorValue q Rsmall.fundamentalLattice
        ((uniformizerUnit K) ^ 2 * A) at hpair
  obtain ⟨z, hz, hzanis⟩ :=
    Lattice.exists_isNormGenerator_of_finrank_pos q
      Rlarge.fundamentalLattice hpos
  let X : Kˣ := Units.mk0 (q.quadratic z) hzanis
  have hXcoe : (X : K) = q.quadratic z := rfl
  have hprincipalXA :
      Lattice.principalIdeal (K := K) (X : K) =
        Lattice.principalIdeal (K := K) (A : K) := by
    rw [hXcoe]
    exact hz.normIdeal_eq.symm.trans hpair.1.2
  have hXA : ordUnit K X = ordUnit K A :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq X A).mp hprincipalXA
  have hznot : z ∉ Rsmall.fundamentalLattice := by
    intro hzSmall
    have hqzSmall : q.quadratic z ∈
        Lattice.principalIdeal (K := K)
          ((((uniformizerUnit K) ^ 2 * A : Kˣ) : K)) := by
      rw [← hpair.2.2]
      exact Lattice.quadratic_mem_normIdeal_of_mem q
        Rsmall.fundamentalLattice hzSmall
    have hord := Lattice.ord_le_of_mem_principalIdeal
      (Units.ne_zero ((uniformizerUnit K) ^ 2 * A)) hqzSmall
    have hord' : ordUnit K ((uniformizerUnit K) ^ 2 * A) ≤
        ordUnit K X := by
      apply WithTop.coe_le_coe.mp
      simpa only [Dyadic.coe_ordUnit, hXcoe] using hord
    have hpi : ordUnit K (uniformizerUnit K) = 1 := by
      simpa [uniformizerPowerUnit] using
        (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
    simp only [ordUnit_mul, ordUnit_pow, hpi] at hord'
    rw [hXA] at hord'
    omega
  let enlarged : V := ((D.input.enlargedVector :
    D.input.block.component.carrier) : V)
  have hadjoinY : Lattice.adjoinVector Rsmall.fundamentalLattice enlarged =
      Rlarge.fundamentalLattice := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation,
      Rlarge.fundamentalLattice_eq_scaleTruncation]
    change Lattice.adjoinVector
        (Lattice.scaleTruncation q N
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r))) enlarged =
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p))
    rw [← hrp]
    simpa only [enlarged] using
      D.adjoin_enlargedVector_smallScaleTruncation_eq_large
        p hbefore hscaleRaw
  have hyLarge : enlarged ∈ Rlarge.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation]
    change enlarged ∈ Lattice.scaleTruncation q M
      (ordUnit K (D.largeAlmostJordan.scaleGenerator p))
    simpa only [enlarged] using
      D.enlargedVector_mem_largeScaleTruncation_before_selected p hbefore
  have hpiYField : (uniformizer K) • enlarged ∈
      Rsmall.fundamentalLattice := by
    apply hrescale
    exact Lattice.smul_mem_rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice hyLarge
  have hpiY : (uniformizerInteger K) • enlarged ∈
      Rsmall.fundamentalLattice := by
    change (uniformizer K) • enlarged ∈ Rsmall.fundamentalLattice
    exact hpiYField
  have hadjoinX : Lattice.adjoinVector Rsmall.fundamentalLattice z =
      Rlarge.fundamentalLattice :=
    Lattice.adjoinVector_eq_of_uniformizer_smul_mem_of_not_mem
      hadjoinY hpiY hz.mem hznot
  have hpiXField : (uniformizer K) • z ∈ Rsmall.fundamentalLattice := by
    apply hrescale
    exact Lattice.smul_mem_rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice hz.mem
  have hpiX : (uniformizerInteger K) • z ∈
      Rsmall.fundamentalLattice := by
    change (uniformizer K) • z ∈ Rsmall.fundamentalLattice
    exact hpiXField
  have hsmallX : Lattice.IsNormGeneratorValue q
      Rsmall.fundamentalLattice ((uniformizerUnit K) ^ 2 * X) := by
    constructor
    · refine ⟨(uniformizerInteger K) • z, hpiX, 0,
        Submodule.zero_mem _, ?_⟩
      have hscalar :
          algebraMap (IntegerRing K) K (uniformizerInteger K) =
            uniformizer K := rfl
      rw [add_zero, ← IsScalarTower.algebraMap_smul K
        (uniformizerInteger K) z, q.quadratic_smul, hscalar]
      change ((((uniformizerUnit K) ^ 2 * X : Kˣ) : K)) =
        uniformizer K ^ 2 * q.quadratic z
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, X,
        Units.val_mk0, coe_uniformizerUnit]
    · apply hpair.2.2.trans
      apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
        ((uniformizerUnit K) ^ 2 * A)
        ((uniformizerUnit K) ^ 2 * X)).2
      simp only [ordUnit_mul, ordUnit_pow, hXA]
  have hscaleResolved :
      Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
        Rlarge.jordan.fundamentalScaleOrder Rlarge.component := by
    calc
      Rsmall.jordan.fundamentalScaleOrder Rsmall.component =
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) :=
        Rsmall.scaleOrder_eq
      _ = ordUnit K (D.largeAlmostJordan.scaleGenerator p) := by
        rw [← hrp]
        exact hscaleRaw.symm
      _ = Rlarge.jordan.fundamentalScaleOrder Rlarge.component :=
        Rlarge.scaleOrder_eq.symm
  have htwo : Lattice.twoScaleIdeal q Rsmall.fundamentalLattice =
      Lattice.twoScaleIdeal q Rlarge.fundamentalLattice := by
    unfold Lattice.twoScaleIdeal
    congr 1
    calc
      Lattice.scaleIdeal q Rsmall.fundamentalLattice =
          Lattice.powerIdeal (K := K)
            (Rsmall.jordan.fundamentalScaleOrder Rsmall.component) :=
        Rsmall.jordan.scaleIdeal_scaleTruncation_at_component Rsmall.component
      _ = Lattice.powerIdeal (K := K)
          (Rlarge.jordan.fundamentalScaleOrder Rlarge.component) := by
        rw [hscaleResolved]
      _ = Lattice.scaleIdeal q Rlarge.fundamentalLattice :=
        (Rlarge.jordan.scaleIdeal_scaleTruncation_at_component
          Rlarge.component).symm
  have hweight := Lattice.weightIdeal_eq_of_adjoin_normGenerator_gapTwo
    hz hzanis hadjoinX hsmallX htwo
  rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
    Rsmall.fundamentalLattice_eq_scaleTruncation] at hweight
  simpa only [x, y, p, r, I] using hweight

/-- A reverse strict order inequality before the selected component forces
the current weak local coordinate to be positive. -/
theorem weakUnaryDirect_current_local_pos_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    0 < ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).2.val := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized : b.order I =
      JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by simpa only [I] using hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have hpos : 0 < localIndex := by
    by_contra hnot
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  simpa only [localIndex, x, I] using hpos

/-- In the collision-safe gap-two branch, the common intrinsic fundamental
weight gives equality of the two preceding alpha endpoints. -/
theorem weakUnaryDirect_previous_order_add_alpha_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    ∃ hpos : 0 < i.val,
      (a.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          a.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
        (b.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          b.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hsmallBefore : r < D.smallSelectedPosition :=
    D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore
  let Rlarge := D.largeStrictCoordinateResolution a I hbefore.le
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBefore.le
  have hgt : b.order i.castSucc < a.order i.castSucc := by omega
  have hsourceWeakPos :=
    D.weakUnaryDirect_current_local_pos_of_current_gt
      hfin i₀ hi₀ a b i hbefore hgt
  have htargetWeakPos : 0 < (y.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    simpa only [x, I] using hsourceWeakPos
  have hlargeOffset :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hbefore.le hbefore
  have hsmallOffset :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallBefore.le
  have hsourceResolvedPos :
      0 < (Rlarge.profile.indexEquiv I).2.val := by
    rw [Rlarge.localCoordinate_eq, hlargeOffset, Nat.zero_add]
    simpa only [x] using hsourceWeakPos
  have htargetResolvedPos :
      0 < (Rsmall.profile.indexEquiv I).2.val := by
    rw [Rsmall.localCoordinate_eq, hsmallOffset, Nat.zero_add]
    exact htargetWeakPos
  rcases previous_profile_coordinate_internal_of_current_local_pos
      a Rlarge.profile i hsourceResolvedPos with
    ⟨hipos, hsourceComponent, hsourceInternal⟩
  rcases previous_profile_coordinate_internal_of_current_local_pos
      b Rsmall.profile i htargetResolvedPos with
    ⟨_, htargetComponent, htargetInternal⟩
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hweightIdeal :=
    D.weakUnaryDirect_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
      hfin i₀ hi₀ a b i hbefore hcurrent
  have hweightOrder :
      Rlarge.jordan.fundamentalWeightOrder Rlarge.component =
        Rsmall.jordan.fundamentalWeightOrder Rsmall.component := by
    unfold Lattice.JordanDecomposition.fundamentalWeightOrder
    apply Lattice.powerIdeal_injective (K := K)
    rw [← Lattice.weightIdeal_eq_powerIdeal,
      ← Lattice.weightIdeal_eq_powerIdeal]
    change Lattice.weightIdeal q Rlarge.fundamentalLattice =
      Lattice.weightIdeal q Rsmall.fundamentalLattice
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    simpa only [x, y, I] using hweightIdeal
  have hsourceFormula :=
    Rlarge.profile.internal_weightOrder_eq_order_add_alpha
      previous hsourceInternal
  have htargetFormula :=
    Rsmall.profile.internal_weightOrder_eq_order_add_alpha
      previous htargetInternal
  have hsourceComponent' :
      (Rlarge.profile.indexEquiv previous.castSucc).1 =
        Rlarge.component := by
    simpa only [previous, I, BONG.StrictCoordinateResolution.component] using
      hsourceComponent
  have htargetComponent' :
      (Rsmall.profile.indexEquiv previous.castSucc).1 =
        Rsmall.component := by
    simpa only [previous, I, BONG.StrictCoordinateResolution.component] using
      htargetComponent
  rw [hsourceComponent'] at hsourceFormula
  rw [htargetComponent'] at htargetFormula
  have hweightQ :
      (Rlarge.jordan.fundamentalWeightOrder Rlarge.component : ℚ) =
        (Rsmall.jordan.fundamentalWeightOrder Rsmall.component : ℚ) := by
    exact_mod_cast hweightOrder
  refine ⟨hipos, ?_⟩
  change (a.order previous.castSucc : ℚ) + a.alphaValue previous =
    (b.order previous.castSucc : ℚ) + b.alphaValue previous
  linarith

/-- Collision-safe version of the weight endpoint comparison in case 1(b).
The possible equal-scale neighbours are first merged by the coordinate-local
strict resolutions. -/
theorem weakUnaryDirect_order_add_alphaValue_le_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    (a.order i.castSucc : ℚ) + a.alphaValue i ≤
      (b.order i.castSucc : ℚ) + b.alphaValue i := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ p hbefore
  have hweakInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hlargeLe : (x.indexEquiv I).1 ≤ D.largeSelectedPosition :=
    hbefore.le
  have hsmallLe : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    exact (D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore).le
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe (Or.inl (by simpa only [p, localIndex] using hweakInternal))
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hscales := D.weakUnaryDirect_fundamentalScale_interval_before
    hfin i₀ hi₀ a b I hbefore
  change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
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
  have hfundamental :
      Rsmall.jordan.fundamentalLattice (Rsmall.profile.indexEquiv I).1 ≤
        Rlarge.jordan.fundamentalLattice (Rlarge.profile.indexEquiv I).1 := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan)
      (Rsmall.profile.indexEquiv I).1 (Rlarge.profile.indexEquiv I).1
      hscale hbound
  exact BONG.order_add_alphaValue_le_of_fundamentalLattice_le
    a b Rlarge.profile Rsmall.profile i Rlarge.internal hfundamental

/-- Collision-safe one-step specialization used in case 2. -/
theorem weakUnaryDirect_alphaValue_le_one_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    a.alphaValue i ≤ 1 := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex =
        JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ = a.order I + 1 := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex + 1 :=
        congrArg (fun z : Int ↦ z + 1) hsourceLocal
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_succ
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective := by
    rw [← htargetOrderLocal, hcurrent, hsourceOrderLocal]
    omega
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ p hbefore
  have hweakInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hlargeLe : (x.indexEquiv I).1 ≤ D.largeSelectedPosition :=
    hbefore.le
  have hsmallLe : (y.indexEquiv I).1 ≤ D.smallSelectedPosition := by
    exact (D.weakUnaryDirect_small_before hfin i₀ hi₀ a b I hbefore).le
  obtain ⟨Rlarge⟩ := D.nonempty_largeInternalStrictCoordinateResolution
    a I hlargeLe (Or.inl (by simpa only [p, localIndex] using hweakInternal))
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hscales := D.weakUnaryDirect_fundamentalScale_interval_before
    hfin i₀ hi₀ a b I hbefore
  change ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) ∧
    ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
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
  have hfundamental :
      Rsmall.jordan.fundamentalLattice (Rsmall.profile.indexEquiv I).1 ≤
        Rlarge.jordan.fundamentalLattice (Rlarge.profile.indexEquiv I).1 := by
    apply D.smallFundamentalLattice_le_large_of_scale_le
      (J := Rsmall.jordan) (H := Rlarge.jordan)
      (Rsmall.profile.indexEquiv I).1 (Rlarge.profile.indexEquiv I).1
      hscale hbound
  have hsourceGeneratorOrder :
      ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) = a.order I := by
    have hgen := Rlarge.jordan.fundamentalNormGenerator_order_eq_effective
      (Rlarge.profile.indexEquiv I).1
    change ordUnit K (Rlarge.jordan.fundamentalNormGenerator
        (Rlarge.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rlarge.jordan
        (Rlarge.profile.indexEquiv I).1
        (Rlarge.jordan.fundamentalScaleOrder
          (Rlarge.profile.indexEquiv I).1) at hgen
    rw [Rlarge.scaleOrder_eq, Rlarge.effectiveNormOrder_eq] at hgen
    exact hgen.trans hsourceOrderLocal.symm
  have htargetGeneratorOrder :
      ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) = b.order I := by
    have hgen := Rsmall.jordan.fundamentalNormGenerator_order_eq_effective
      (Rsmall.profile.indexEquiv I).1
    change ordUnit K (Rsmall.jordan.fundamentalNormGenerator
        (Rsmall.profile.indexEquiv I).1) =
      BONG.jordanEffectiveNormOrderAt Rsmall.jordan
        (Rsmall.profile.indexEquiv I).1
        (Rsmall.jordan.fundamentalScaleOrder
          (Rsmall.profile.indexEquiv I).1) at hgen
    rw [Rsmall.scaleOrder_eq, Rsmall.effectiveNormOrder_eq] at hgen
    exact hgen.trans htargetOrderLocal.symm
  exact BONG.alphaValue_le_one_of_fundamentalLattice_le_current_succ
    a b Rlarge.profile Rsmall.profile i Rlarge.internal hfundamental
      hsourceGeneratorOrder htargetGeneratorOrder hcurrent

/-- Collision-safe two-step rigidity in case 1(b). -/
theorem weakUnaryDirect_source_twoStep_eq_before_selected_of_current_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc < b.order i.castSucc) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceScaleAt : ordUnit K (D.largeAlmostJordan.scaleGenerator
      (x.indexEquiv I).1) = scale := rfl
  have hsourceEffectiveAt :
      D.largeAlmostJordan.effectiveNormOrderAt
          (x.indexEquiv I).1 scale = sourceEffective := rfl
  have htargetScaleAt : ordUnit K (D.smallAlmostJordan.scaleGenerator
      (y.indexEquiv I).1) = scale := hscaleTarget
  have htargetEffectiveAt :
      D.smallAlmostJordan.effectiveNormOrderAt
          (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator
              (y.indexEquiv I).1)) = targetEffective := rfl
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ p hbefore
  have hsourceInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have htargetInternal : (y.indexEquiv I).2.val + 1 <
      finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hlocal, ← hrankEq]
    exact hsourceInternal
  have hglobalNext : i.val + 1 < n + 2 := by omega
  have hoddNext : ¬Even (localIndex + 1) := by
    intro h
    exact (Nat.even_add_one.mp h) heven
  have hsourceNext :
      a.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - sourceEffective := by
    have h := x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hglobalNext hsourceInternal
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [hsourceScaleAt, hsourceEffectiveAt] at h
    change a.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex + 1) at h
    rw [JordanProfileOrder.localOrder_odd_of_scale_le
      hsourceScale hoddNext] at h
    exact h
  have htargetNext :
      b.order ⟨i.val + 1, hglobalNext⟩ =
        2 * scale - targetEffective := by
    have h := y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hglobalNext htargetInternal
    simp only [BONG.weakJordanExpectedOrder] at h
    simp only [I] at h
    rw [htargetScaleAt] at h
    have htargetEffectiveScale :
        D.smallAlmostJordan.effectiveNormOrderAt
            (y.indexEquiv I).1 scale = targetEffective := by
      rw [← htargetScaleAt]
    rw [htargetEffectiveScale] at h
    have hlocalNext : (y.indexEquiv I).2.val + 1 =
        localIndex + 1 := by omega
    change b.order ⟨i.val + 1, hglobalNext⟩ =
      JordanProfileOrder.localOrder scale targetEffective
        ((y.indexEquiv I).2.val + 1) at h
    rw [hlocalNext, JordanProfileOrder.localOrder_odd_of_scale_le
      htargetScale hoddNext] at h
    exact h
  have hnextReverse :
      b.order ⟨i.val + 1, hglobalNext⟩ <
        a.order ⟨i.val + 1, hglobalNext⟩ := by
    rw [hsourceNext, htargetNext]
    have heffectiveStrict : sourceEffective < targetEffective := by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrent
    omega
  rcases (D.weakUnaryDirect_coordinate hfin i₀ hi₀ a b
      (i.val + 1) hglobalNext).compare with hdirect |
        ⟨_hpositive, htwo, hpair⟩
  · have : False := by
      change a.order ⟨i.val + 1, hglobalNext⟩ ≤
        b.order ⟨i.val + 1, hglobalNext⟩ at hdirect
      exact (not_le_of_gt hnextReverse) hdirect
    contradiction
  · refine ⟨by omega, ?_⟩
    have htwoLe : a.order ⟨i.val + 2, by omega⟩ ≤ a.order I := by
      have hpair' : a.order ⟨i.val + 1, hglobalNext⟩ +
            a.order ⟨i.val + 2, by omega⟩ ≤
          b.order ⟨i.val, by omega⟩ +
            b.order ⟨i.val + 1, hglobalNext⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at,
          show i.val + 1 - 1 = i.val by omega,
          show i.val + 1 + 1 = i.val + 2 by omega] using hpair
      have hcurrentTarget : b.order ⟨i.val, by omega⟩ =
          targetEffective := by
        have hindex : (⟨i.val, by omega⟩ : Fin (n + 2)) = I := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact htargetOrderLocal
      rw [hsourceNext, htargetNext, hcurrentTarget] at hpair'
      rw [hsourceOrderLocal]
      omega
    apply le_antisymm
    · have htwoI : I.val + 2 < n + 2 := by
        change i.val + 2 < n + 2
        omega
      exact a.good I htwoI
    · exact htwoLe

theorem weakUnaryDirect_source_twoStep_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc = a.order i.castSucc + 1) :
    ∃ htwo : i.val + 2 < n + 2,
      a.order i.castSucc = a.order ⟨i.val + 2, htwo⟩ :=
  D.weakUnaryDirect_source_twoStep_eq_before_selected_of_current_lt
    hfin i₀ hi₀ a b i hbefore (by omega)

/-- A strict rise at the current comparison coordinate forces the next
global coordinate to stay in the same common weak component. -/
theorem weakUnaryDirect_next_before_selected_of_current_lt
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
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  let I : Fin (n + 2) := g.castSucc
  let J : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = I := by
    apply Fin.ext
    rfl
  have hcurrentI : a.order I < b.order I := by
    rw [← hpreviousIndex]
    exact hcurrent
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale sourceEffective localIndex <
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale sourceEffective localIndex =
          a.order I := hsourceLocal.symm
      _ < b.order I := hcurrentI
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex :=
        htargetLocalNormalized
  have heven : Even localIndex :=
    JordanProfileOrder.even_of_effective_le_of_localOrder_lt
      hsourceScale htargetScale heffective hlocalCurrent
  have hsourceOrderLocal : a.order I = sourceEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
  have htargetOrderLocal : b.order I = targetEffective := by
    rw [htargetLocalNormalized,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
  have htargetStrict : scale < targetEffective :=
    hsourceScale.trans_lt (by
      rw [← hsourceOrderLocal, ← htargetOrderLocal]
      exact hcurrentI)
  have hrankEven : Even
      (finrank K (D.smallAlmostJordan.component r).carrier) :=
    D.smallAlmostJordan_hasImproperEvenRank.componentRank_even_of_lt_effectiveNormOrderAt
      D.smallAlmostJordan r r (by
        calc
          ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale :=
            hscaleTarget
          _ < targetEffective := htargetStrict
          _ = D.smallAlmostJordan.effectiveNormOrderAt r
              (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) := rfl)
  have hrankEq :
      finrank K (D.largeAlmostJordan.component p).carrier =
        finrank K (D.smallAlmostJordan.component r).carrier := by
    rw [← hrp]
    exact D.weakUnaryDirect_componentRank_eq_before hfin i₀ hi₀ p hbefore
  have hsourceInternal : localIndex + 1 <
      finrank K (D.largeAlmostJordan.component p).carrier := by
    have hlocalLt : localIndex <
        finrank K (D.largeAlmostJordan.component p).carrier :=
      (x.indexEquiv I).2.isLt
    rw [hrankEq] at hlocalLt ⊢
    rcases heven with ⟨k, hk⟩
    rcases hrankEven with ⟨ell, hell⟩
    omega
  have hglobal : I.val + 1 < n + 2 :=
    x.global_succ_lt_of_local_succ I (by
      simpa only [p, localIndex] using hsourceInternal)
  have hnextPair :
      x.indexEquiv ⟨I.val + 1, hglobal⟩ =
        ⟨p, ⟨localIndex + 1, by
          simpa only [p, localIndex] using hsourceInternal⟩⟩ := by
    have hval := x.inverse_index_val_local_succ
      (x.indexEquiv I).1 (x.indexEquiv I).2
        (by simpa only [p, localIndex] using hsourceInternal)
    have hcurrentInverse : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    have hindex : (⟨I.val + 1, hglobal⟩ : Fin (n + 2)) =
        x.indexEquiv.symm
          ⟨p, ⟨localIndex + 1, by
            simpa only [p, localIndex] using hsourceInternal⟩⟩ := by
      apply Fin.ext
      calc
        I.val + 1 = (x.indexEquiv.symm (x.indexEquiv I)).val + 1 := by
          rw [hcurrentInverse]
        _ = (x.indexEquiv.symm
            ⟨p, ⟨localIndex + 1, by
              simpa only [p, localIndex] using hsourceInternal⟩⟩).val := by
          simpa only [p, localIndex] using hval.symm
    rw [hindex, x.indexEquiv.apply_symm_apply]
  have hJ : J = ⟨I.val + 1, hglobal⟩ := by
    apply Fin.ext
    simp only [J, I, g, BONG.GoodBONG.representationAlphaIndex,
      Fin.val_castSucc]
    have := i.pos
    omega
  change (x.indexEquiv J).1 < D.largeSelectedPosition
  rw [hJ, hnextPair]
  exact hbefore

theorem weakUnaryDirect_commonBound_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
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
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentG : a.order g.castSucc < b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hcurrent
  obtain ⟨htwo, houterRaw⟩ :=
    D.weakUnaryDirect_source_twoStep_eq_before_selected_of_current_lt
      hfin i₀ hi₀ a b g hbefore hcurrentG
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    omega
  have hrightIndex :
      (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
        ⟨i.val + 1, hnext⟩ := by
    apply Fin.ext
    change g.val + 2 = i.val + 1
    simp only [g, BONG.GoodBONG.representationAlphaIndex]
    have := i.pos
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := congrArg a.order hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ :=
        congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  push_cast at hcandidate hrecurrence
  have hupper : a.representationAlphaValue b i ≤
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
        a.alphaValue g := by
    calc
      a.representationAlphaValue b i ≤
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
            (b.order ⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue ⟨i.val, by omega⟩ := hcandidate
      _ = (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
            a.alphaValue g := by linarith [hrecurrence]
  have hweight :=
    D.weakUnaryDirect_order_add_alphaValue_le_before_selected_of_current_lt
      hfin i₀ hi₀ a b g hbefore hcurrentG
  have hcurrentQ :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) <
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) := by
    exact_mod_cast hcurrent
  have hweightCanonical :
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue g ≤
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          b.alphaValue g := by
    simpa only [← hpreviousIndex] using hweight
  have hsource : a.representationAlphaValue b i ≤ a.alphaValue g := by
    linarith
  have htarget : a.representationAlphaValue b i ≤ b.alphaValue g := by
    linarith
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsource
  · exact_mod_cast htarget

theorem weakUnaryDirect_commonCertificate_before_selected_of_current_lt
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrentLt : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
      b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩)
    (hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  have hrightBefore :=
    D.weakUnaryDirect_next_before_selected_of_current_lt
      hfin i₀ hi₀ a b i hbefore hcurrentLt
  obtain ⟨X, hsource, htarget⟩ :=
    D.weakUnaryDirect_commonApproximation_before_selected
      hfin i₀ hi₀ a b i hrightBefore hnotSucc
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
      (D.weakUnaryDirect_commonBound_before_selected_of_current_lt
        hfin i₀ hi₀ a b i hbefore hcurrentLt)

theorem weakUnaryDirect_representationAlphaValue_le_zero_before_selected
    [Beli2006AlphaLaws.{u, v} K]
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
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    a.representationAlphaValue b i ≤ 0 := by
  let g : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hprevious : i.val - 1 < n + 2 := by
    have := i.lt_large
    omega
  have hpreviousIndex :
      (⟨i.val - 1, hprevious⟩ : Fin (n + 2)) = g.castSucc := by
    apply Fin.ext
    rfl
  have hcurrentOrder : b.order g.castSucc = a.order g.castSucc + 1 := by
    have h := hcurrent
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hprevious,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hprevious] at h
    simp only [BONG.GoodBONG.orderSequence_at] at h
    rw [← hpreviousIndex]
    exact h
  have halpha : a.alphaValue g ≤ 1 :=
    D.weakUnaryDirect_alphaValue_le_one_before_selected
      hfin i₀ hi₀ a b g hbefore hcurrentOrder
  obtain ⟨htwo, houterRaw⟩ :=
    D.weakUnaryDirect_source_twoStep_eq_before_selected
      hfin i₀ hi₀ a b g hbefore hcurrentOrder
  have hnext : i.val + 1 < n + 2 := by
    have hg : g.val = i.val - 1 := rfl
    rw [hg] at htwo
    omega
  have houter : a.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val + 1, hnext⟩ := by
    have hrightIndex :
        (⟨g.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      change g.val + 2 = i.val + 1
      simp only [g, BONG.GoodBONG.representationAlphaIndex]
      have := i.pos
      omega
    calc
      a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          a.order g.castSucc := congrArg a.order hpreviousIndex
      _ = a.order ⟨g.val + 2, htwo⟩ := houterRaw
      _ = a.order ⟨i.val + 1, hnext⟩ :=
        congrArg a.order hrightIndex
  have hrecurrenceTop :=
    a.orderGap_add_nextAlpha_eq_alpha_of_twoStep_eq i hnext houter
  have hrecurrence :
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue g := by
    simpa only [g] using (show
      ((a.order ⟨i.val, i.lt_large⟩ -
        a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Int) : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ =
        a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) by
      exact_mod_cast hrecurrenceTop)
  have hcandidate :=
    a.representationAlphaValue_le_primary_nextAlpha b i hnext
  have hcurrentCanonical : b.order
        ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
      a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
    calc
      b.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ =
          b.order g.castSucc := congrArg b.order hpreviousIndex
      _ = a.order g.castSucc + 1 := hcurrentOrder
      _ = a.order ⟨i.val - 1,
          (Nat.sub_le _ _).trans_lt i.lt_large⟩ + 1 := by
        rw [← congrArg a.order hpreviousIndex]
  have hcurrentCanonicalQ :
      (b.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) =
      (a.order ⟨i.val - 1,
        (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) + 1 := by
    exact_mod_cast hcurrentCanonical
  push_cast at hcandidate hrecurrence
  calc
    a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩ := hcandidate
    _ = ((a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (a.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ : ℚ) +
          a.alphaValue ⟨i.val, by omega⟩) - 1 := by
      rw [hcurrentCanonicalQ]
      ring
    _ = a.alphaValue g - 1 := by rw [hrecurrence]
    _ ≤ 0 := by linarith

theorem weakUnaryDirect_oddCertificate_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) =
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.odd
  · have hiDefect : D.DefectReducedRange i :=
      D.weakUnaryDirect_defectReducedRange_of_lemma517Range
        hfin i₀ hi₀ i hi
    have hprevious :=
      D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
        a b i hiDefect hcurrent
    have hipos := i.pos
    rw [show i.val = (i.val - 1) + 1 by omega,
      b.orderSequence.prefixSum_succ,
      a.orderSequence.prefixSum_succ, ← hprevious, hcurrent]
    abel
  · rw [← a.coe_representationAlphaValue b i]
    exact_mod_cast
      D.weakUnaryDirect_representationAlphaValue_le_zero_before_selected
        hfin i₀ hi₀ a b i hbefore hcurrent

theorem weakUnaryDirect_representationAlphaValue_le_targetAlpha_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    a.representationAlphaValue b i ≤
      b.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  rcases (D.weakUnaryDirect_coordinate hfin i₀ hi₀ a b
      g.val g.castSucc.isLt).compare with hdirect | hpairData
  · have hdirect' : a.order g.castSucc ≤ b.order g.castSucc := by
      have hraw : a.order ⟨g.val, g.castSucc.isLt⟩ ≤
          b.order ⟨g.val, g.castSucc.isLt⟩ := by
        simpa only [BONG.GoodBONG.orderSequence_at] using hdirect
      have hindex : (⟨g.val, g.castSucc.isLt⟩ : Fin (n + 2)) =
          g.castSucc := by
        apply Fin.ext
        rfl
      rw [hindex] at hraw
      exact hraw
    omega
  · obtain ⟨hpositive, hnext, hpair⟩ := hpairData
    have hiPrevious : 1 < i.val := by
      change 0 < i.val - 1 at hpositive
      omega
    let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    have hpreviousLe : previousAlpha ≤ g := by
      change i.val - 2 ≤ i.val - 1
      omega
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousLe
    change (b.order previousAlpha.castSucc : ℚ) +
        b.alphaValue previousAlpha ≤
      (b.order g.castSucc : ℚ) + b.alphaValue g at hendpoint
    have hcandidate :=
      a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
    have hnextIndex :
        (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    have hpreviousIndex :
        (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
          previousAlpha.castSucc := by
      apply Fin.ext
      change (i.val - 1) - 1 = i.val - 2
      omega
    have hpairRaw :
        a.order ⟨g.val, g.castSucc.isLt⟩ +
            a.order ⟨g.val + 1, hnext⟩ ≤
          b.order ⟨g.val - 1, by omega⟩ +
            b.order ⟨g.val, g.castSucc.isLt⟩ := by
      simpa only [BONG.GoodBONG.orderSequence_at] using hpair
    have hpairQ :
        (a.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) +
            (a.order ⟨g.val + 1, hnext⟩ : ℚ) ≤
          (b.order ⟨g.val - 1, by omega⟩ : ℚ) +
            (b.order ⟨g.val, g.castSucc.isLt⟩ : ℚ) := by
      exact_mod_cast hpairRaw
    have hsourceCurrentValue :
        a.order ⟨g.val, g.castSucc.isLt⟩ = a.order g.castSucc := by
      apply congrArg a.order
      apply Fin.ext
      rfl
    have htargetCurrentValue :
        b.order ⟨g.val, g.castSucc.isLt⟩ = b.order g.castSucc := by
      apply congrArg b.order
      apply Fin.ext
      rfl
    have hsourceNextValue :
        a.order ⟨g.val + 1, hnext⟩ =
          a.order ⟨i.val, i.lt_large⟩ := congrArg a.order hnextIndex
    have htargetPreviousValue :
        b.order ⟨g.val - 1, by omega⟩ =
          b.order previousAlpha.castSucc := congrArg b.order hpreviousIndex
    have hcandidate' : a.representationAlphaValue b i ≤
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
          (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
      have hcurrentMathIndex :
          (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
            g.castSucc := by
        apply Fin.ext
        rfl
      have hpreviousAlphaIndex :
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
            previousAlpha := by
        apply Fin.ext
        rfl
      push_cast at hcandidate
      rw [hcurrentMathIndex, hpreviousAlphaIndex] at hcandidate
      exact hcandidate
    have hcurrentQ : (b.order g.castSucc : ℚ) <
        (a.order g.castSucc : ℚ) := by
      exact_mod_cast hcurrent
    rw [hsourceCurrentValue, htargetCurrentValue,
      hsourceNextValue, htargetPreviousValue] at hpairQ
    linarith

theorem weakUnaryDirect_source_previous_twoStep_eq_before_selected_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv i.castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    ∃ (hpos : 0 < i.val) (hnext : i.val + 1 < n + 2),
      a.order ⟨i.val - 1, by omega⟩ =
        a.order ⟨i.val + 1, hnext⟩ ∧
      a.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val - 1, by omega⟩ ∧
      (a.order i.castSucc = b.order i.castSucc + 1 ∨
        a.order i.castSucc = b.order i.castSucc + 2) ∧
      b.order ⟨i.val - 1, by omega⟩ -
          a.order ⟨i.val - 1, by omega⟩ =
        a.order i.castSucc - b.order i.castSucc ∧
      Even (a.order ⟨i.val - 1, by omega⟩ + a.order i.castSucc) ∧
      Even (a.orderGap i) ∧
      a.orderGap i < 2 * (ramificationIndex K : Int) := by
  let I : Fin (n + 2) := i.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let r := (y.indexEquiv I).1
  let localIndex := (x.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.weakUnaryDirect_coordinates_eq_before hfin i₀ hi₀ a b I hbefore
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (y.indexEquiv I).2.val := hcoordinates.2
  have hscaleRaw := D.weakUnaryShift_scaleOrder_eq_before_selected
    hfin i₀ hi₀ p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ p hbefore
  have heffectiveUpper : targetEffective ≤ sourceEffective + 2 := by
    have hupper := (D.common_effectiveNormOrder_bounds p hbefore).2
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2
    rw [← hrp, ← hscaleRaw]
    exact hupper
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have htargetCeiling :
      targetEffective ≤ scale + (ramificationIndex K : Int) := by
    have h :=
      D.smallAlmostJordan.effectiveNormOrderAt_scale_le_scale_add_ramificationIndex r
    change D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) ≤
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) +
        (ramificationIndex K : Int) at h
    simpa only [targetEffective, hscaleTarget] using h
  have hsourceLocal := D.largeWeak_order_eq_localOrder a I
  have htargetLocal := D.smallWeak_order_eq_localOrder b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (y.indexEquiv I).2.val := by
        simpa only [y, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap :
      targetEffective = sourceEffective + 1 ∨
        targetEffective = sourceEffective + 2 := by
    have hstrict : sourceEffective < targetEffective := by
      rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd,
        JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
        at hlocalCurrent
      omega
    omega
  have hcurrentGap :
      a.order I = b.order I + 1 ∨ a.order I = b.order I + 2 := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    rcases heffectiveGap with hgap | hgap
    · left
      omega
    · right
      omega
  have hlocalPos : 0 < localIndex := by
    by_contra h
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  have hglobalPos : 0 < i.val := by
    have hindex := x.index_val_eq_componentStart_add_local I
    change I.val = _ + localIndex at hindex
    change 0 < I.val
    omega
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hpreviousCast : previous.castSucc =
      x.indexEquiv.symm
        ⟨p, ⟨localIndex - 1, by
          change localIndex - 1 <
            finrank K (D.largeAlmostJordan.component p).carrier
          have := (x.indexEquiv I).2.isLt
          change localIndex <
            finrank K (D.largeAlmostJordan.component p).carrier at this
          omega⟩⟩ := by
    have hpredVal := x.inverse_index_val_local_pred
      p (x.indexEquiv I).2 (by simpa only [localIndex] using hlocalPos)
    have hcurrentInverse : x.indexEquiv.symm (x.indexEquiv I) = I :=
      x.indexEquiv.symm_apply_apply I
    apply Fin.ext
    change i.val - 1 = _
    have hpredVal' :
        (x.indexEquiv.symm
          ⟨p, ⟨localIndex - 1, by
            change localIndex - 1 <
              finrank K (D.largeAlmostJordan.component p).carrier
            have := (x.indexEquiv I).2.isLt
            change localIndex <
              finrank K (D.largeAlmostJordan.component p).carrier at this
            omega⟩⟩).val + 1 = I.val := by
      simpa only [p, localIndex] using
        hpredVal.trans (congrArg Fin.val hcurrentInverse)
    have hIval : I.val = i.val := rfl
    rw [hIval] at hpredVal'
    omega
  have hpreviousComponent : (x.indexEquiv previous.castSucc).1 = p := by
    rw [hpreviousCast, x.indexEquiv.apply_symm_apply]
  have hpreviousBefore :
      (x.indexEquiv previous.castSucc).1 < D.largeSelectedPosition := by
    rw [hpreviousComponent]
    exact hbefore
  have hevenPrevious : Even (localIndex - 1) := by
    rcases Nat.not_even_iff_odd.mp hodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hsourcePrevious : a.order previous.castSucc = sourceEffective := by
    have h := x.order_pred_eq_weakJordanExpectedOrder_of_local_pred I
      (by simpa only [localIndex] using hlocalPos)
    simp only [BONG.weakJordanExpectedOrder] at h
    change a.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder scale sourceEffective
        (localIndex - 1) at h
    rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsourceScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have htargetPrevious : b.order previous.castSucc = targetEffective := by
    have htargetPos : 0 < (y.indexEquiv I).2.val := by
      rw [← hlocal]
      exact hlocalPos
    have h := y.order_pred_eq_weakJordanExpectedOrder_of_local_pred I htargetPos
    simp only [BONG.weakJordanExpectedOrder] at h
    change b.order ⟨I.val - 1, by omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
          ((y.indexEquiv I).2.val - 1) at h
    have hprevLocal : (y.indexEquiv I).2.val - 1 = localIndex - 1 := by
      omega
    rw [hscaleTarget, hprevLocal,
      JordanProfileOrder.localOrder_even_of_scale_le
        htargetScale hevenPrevious] at h
    have hindex : (⟨I.val - 1, by omega⟩ : Fin (n + 2)) =
        previous.castSucc := by
      apply Fin.ext
      simp only [I, previous, Fin.val_castSucc]
    rw [hindex] at h
    exact h
  have heffectiveStrict : sourceEffective < targetEffective := by
    rw [hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
      at hcurrent
    omega
  have hpreviousStrict :
      a.order previous.castSucc < b.order previous.castSucc := by
    rw [hsourcePrevious, htargetPrevious]
    exact heffectiveStrict
  have hgapEquality :
      b.order previous.castSucc - a.order previous.castSucc =
        a.order I - b.order I := by
    rw [hsourcePrevious, htargetPrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd,
      htargetLocalNormalized,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
    ring
  have hevenPair : Even (a.order previous.castSucc + a.order I) := by
    refine ⟨scale, ?_⟩
    rw [hsourcePrevious, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    omega
  obtain ⟨htwo, htwoEq⟩ :=
    D.weakUnaryDirect_source_twoStep_eq_before_selected_of_current_lt
      hfin i₀ hi₀ a b previous hpreviousBefore hpreviousStrict
  have hnext : i.val + 1 < n + 2 := by
    change previous.val + 2 < n + 2 at htwo
    dsimp only [previous] at htwo
    omega
  have hrightGap :
      (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) = i.succ := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hleftGap : previous.castSucc =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have htwoGap :
      a.order ⟨i.val - 1, by omega⟩ = a.order i.succ := by
    rw [← hleftGap, ← hrightGap]
    exact htwoEq
  have hnextEffective : a.order i.succ = sourceEffective := by
    calc
      a.order i.succ = a.order ⟨i.val - 1, by omega⟩ := htwoGap.symm
      _ = a.order previous.castSucc := by rw [hleftGap]
      _ = sourceEffective := hsourcePrevious
  have hgapFormula : a.orderGap i = 2 * (sourceEffective - scale) := by
    unfold BONG.GoodBONG.orderGap
    rw [hnextEffective, hsourceLocal,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
    ring
  have hgapEven : Even (a.orderGap i) := by
    refine ⟨sourceEffective - scale, ?_⟩
    rw [hgapFormula]
    ring
  have hgapLt : a.orderGap i < 2 * (ramificationIndex K : Int) := by
    have hsourceCeiling :
        sourceEffective < scale + (ramificationIndex K : Int) :=
      heffectiveStrict.trans_le htargetCeiling
    rw [hgapFormula]
    omega
  refine ⟨hglobalPos, hnext, ?_, ?_, ?_, ?_, ?_, hgapEven, hgapLt⟩
  · have hright :
        (⟨previous.val + 2, htwo⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      dsimp only [previous]
      omega
    have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft, hright] at htwoEq
    exact htwoEq
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hpreviousStrict
    exact hpreviousStrict
  · exact hcurrentGap
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hgapEquality
    exact hgapEquality
  · have hleft : previous.castSucc =
        (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hleft] at hevenPair
    exact hevenPair

theorem weakUnaryDirect_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 1) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 1 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.weakUnaryDirect_source_previous_twoStep_eq_before_selected_of_current_gt
      hfin i₀ hi₀ a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  have hpreviousCurrent :
      b.order ⟨g.val - 1, by omega⟩ =
        a.order ⟨g.val - 1, by omega⟩ + 1 := by
    omega
  have hjpos : 0 < i.val - 1 := by omega
  have hjlt : i.val - 1 < n + 2 :=
    (Nat.sub_le _ _).trans_lt i.lt_large
  have hjle : i.val - 1 ≤ n + 2 := hjlt.le
  let j : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val - 1, hjpos, hjlt, hjle⟩
  have hj : D.Lemma517Range j := by
    change j.val ≤ D.lemma517Cutoff
    change i.val ≤ D.lemma517Cutoff at hi
    dsimp only [j]
    omega
  have hentryIndex :
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 2)) =
        ⟨g.val - 1, by omega⟩ := by
    apply Fin.ext
    rfl
  have hpreviousEntry :
      b.orderSequence.entryOrZero (j.val - 1) =
        a.orderSequence.entryOrZero (j.val - 1) + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := j.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := j.lt_large; omega),
      BONG.GoodBONG.orderSequence_at, BONG.GoodBONG.orderSequence_at,
      hentryIndex]
    exact hpreviousCurrent
  have hjDefect : D.DefectReducedRange j :=
    D.weakUnaryDirect_defectReducedRange_of_lemma517Range
      hfin i₀ hi₀ j hj
  have hpreviousSum :=
    D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
      a b j hjDefect hpreviousEntry
  have hprefixOddRaw :=
    a.comparisonPrefixProduct_order_odd_of_previous_prefix_eq b
      j.val j.pos j.lt_large.le j.lt_large.le hpreviousSum hpreviousEntry
  have hprefixOdd : Odd (ordUnit K
      (a.prefixProduct (i.val - 1) * b.prefixProduct (i.val - 1))) := by
    simpa only [j] using hprefixOddRaw
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentIndex : g.castSucc =
      (⟨i.val - 1, hjlt⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hevenCurrentNext : Even
      (a.order ⟨i.val - 1, hjlt⟩ +
        a.order ⟨i.val, i.lt_large⟩) := by
    have hpair := hevenPair
    rw [htwo, hnextIndex, hcurrentIndex] at hpair
    simpa only [add_comm] using hpair
  have hshiftOdd :=
    a.shiftedPrimaryProduct_odd_of_previousPrefix_odd_of_sourcePair_even
      b i hiPrevious hprefixOdd hevenCurrentNext
  have hzero := a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed b
    (-1) (i.val + 1) (i.val - 1) hshiftOdd
  have hcandidate :=
    a.representationAlphaValue_le_primaryCoefficient_of_defect_zero b i hzero
  have halphaLower :=
    a.orderGap_add_one_le_alphaValue_of_even_of_lt_twoE g hgapEven hgapLt
  have hnextGapIndex : g.succ = ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hcurrentGapIndex : g.castSucc =
      (⟨i.val - 1, hjlt⟩ : Fin (n + 2)) := hcurrentIndex
  push_cast at hcandidate
  push_cast at halphaLower
  unfold BONG.GoodBONG.orderGap at halphaLower
  rw [hnextGapIndex, hcurrentGapIndex] at halphaLower
  push_cast at halphaLower
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 1 := by
    exact_mod_cast hcurrent
  rw [hcurrentGapIndex] at hcurrentQ
  linarith

/-- Collision-safe source-alpha bound in the reverse gap-two branch. -/
theorem weakUnaryDirect_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 2 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.weakUnaryDirect_source_previous_twoStep_eq_before_selected_of_current_gt
      hfin i₀ hi₀ a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hpreviousLe : previousAlpha ≤ g := by
    change i.val - 2 ≤ i.val - 1
    omega
  have hendpoint := a.alphaLeftEndpoint_monotone hpreviousLe
  change (a.order previousAlpha.castSucc : ℚ) +
      a.alphaValue previousAlpha ≤
    (a.order g.castSucc : ℚ) + a.alphaValue g at hendpoint
  have hweightData :=
    D.weakUnaryDirect_previous_order_add_alpha_eq_of_current_eq_target_add_two
      hfin i₀ hi₀ a b g hbefore hcurrent
  rcases hweightData with ⟨_, hweightSum⟩
  have hpreviousAlphaIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 1)) = previousAlpha := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  rw [hpreviousAlphaIndex] at hweightSum
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hpreviousIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
        previousAlpha.castSucc := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  have htwoNormalized :
      a.order previousAlpha.castSucc =
        a.order ⟨i.val, i.lt_large⟩ := by
    rw [← hpreviousIndex, ← hnextIndex]
    exact htwo
  have hgapNormalized :
      b.order previousAlpha.castSucc - a.order previousAlpha.castSucc =
        a.order g.castSucc - b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hgapEquality
  have hcandidate :=
    a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
  have hcurrentMathIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
        g.castSucc := by
    apply Fin.ext
    rfl
  have hcandidate' : a.representationAlphaValue b i ≤
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
        (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
    push_cast at hcandidate
    rw [hcurrentMathIndex,
      show (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
        previousAlpha by rfl] at hcandidate
    exact hcandidate
  have htwoQ :
      (a.order previousAlpha.castSucc : ℚ) =
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast htwoNormalized
  have hgapQ :
      (b.order previousAlpha.castSucc : ℚ) -
          (a.order previousAlpha.castSucc : ℚ) =
        (a.order g.castSucc : ℚ) - (b.order g.castSucc : ℚ) := by
    exact_mod_cast hgapNormalized
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 2 := by
    exact_mod_cast hcurrent
  linarith

/-- Complete collision-safe alpha-cap estimate in the reverse strict-order
branch before the selected component. -/
theorem weakUnaryDirect_commonBound_before_selected_of_current_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  have hcases :=
    D.weakUnaryDirect_source_previous_twoStep_eq_before_selected_of_current_gt
      hfin i₀ hi₀ a b g hbefore hcurrent
  rcases hcases with
    ⟨_hpos, _hnext, _htwo, _hpreviousStrict, hcurrentCases,
      _hgapEquality, _hevenPair, _hgapEven, _hgapLt⟩
  have hsourceBound : a.representationAlphaValue b i ≤
      a.alphaValue g := by
    rcases hcurrentCases with hgapOne | hgapTwo
    · exact D.weakUnaryDirect_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
        hfin i₀ hi₀ a b i hi hbefore hgapOne
    · exact D.weakUnaryDirect_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
        hfin i₀ hi₀ a b i hbefore hgapTwo
  have htargetBound : a.representationAlphaValue b i ≤
      b.alphaValue g :=
    D.weakUnaryDirect_representationAlphaValue_le_targetAlpha_of_current_gt
      hfin i₀ hi₀ a b i hcurrent
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsourceBound
  · exact_mod_cast htargetBound

/-- Any common approximation at the right boundary, together with the
collision-safe reverse-order bound, yields the Section 5 defect
certificate. -/
theorem weakUnaryDirect_commonCertificate_before_selected_of_current_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc)
    (happrox : ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  obtain ⟨X, hsource, htarget⟩ := happrox
  exact BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
      (D.weakUnaryDirect_commonBound_before_selected_of_current_gt
        hfin i₀ hi₀ a b i hi hbefore hcurrent)

/-- At the global coordinate occupied by the enlarged unary component on
the large side, the small weak profile is at the first coordinate of the
intermediate common component. -/
theorem weakUnaryDirect_small_coordinates_at_largeSelected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0) :
    ((D.smallWeakProfileWitness b).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition ∧
      ((D.smallWeakProfileWitness b).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0 := by
  classical
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := D.largeSelectedPosition
  have hrankSmall : 0 < finrank K
      (D.smallAlmostJordan.component p).carrier :=
    D.smallAlmostJordan.component_finrank_pos p
  let zero : Fin (finrank K
      (D.smallAlmostJordan.component p).carrier) := ⟨0, hrankSmall⟩
  have hglobal := x.index_val_eq_componentStart_add_local I
  have hcomponentStart :
      x.componentStart (x.indexEquiv I).1 = x.componentStart p :=
    congrArg x.componentStart hposition
  have hiStart : I.val = x.componentStart p := by
    calc
      I.val = x.componentStart (x.indexEquiv I).1 +
          (x.indexEquiv I).2.val := hglobal
      _ = x.componentStart p := by
        rw [hcomponentStart, hlocal, Nat.add_zero]
  have hprefix := D.weakUnaryShift_prefixRank_eq hfin i₀ hi₀
  have hI : I = y.indexEquiv.symm ⟨p, zero⟩ := by
    apply Fin.ext
    have hinverse := y.inverse_index_val p zero
    dsimp only [zero, Fin.val_mk] at hinverse
    calc
      I.val = x.componentStart p := hiStart
      _ = y.componentStart p := by
        simpa only [x, y, p,
          BONG.WeakJordanOrderProfileWitness.componentStart] using hprefix
      _ = (y.indexEquiv.symm ⟨p, zero⟩).val := hinverse.symm
  have hy : y.indexEquiv I = ⟨p, zero⟩ := by
    rw [hI, y.indexEquiv.apply_symm_apply]
  constructor
  · simpa only [y, I, p] using congrArg Sigma.fst hy
  · simpa only [y, I, zero] using congrArg (fun z ↦ z.2.val) hy

/-- The collision determinant relation at the unary-shift boundary.  The
weak prefixes before the enlarged unary component agree componentwise, so
the generic collision transport applies without an aligned selected
position. -/
theorem weakUnaryDirect_largeCollision_boundaryDeterminantRelation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0) :
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    let heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    D.LargeCollisionBoundaryDeterminantRelation k heq b i := by
  classical
  dsimp only
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  have hsmall := D.weakUnaryDirect_small_coordinates_at_largeSelected
    hfin i₀ hi₀ a b i hposition hlocal
  have hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j := by
    intro j hj
    exact D.unaryShift_component_eq_before hfin i₀ hi₀ j hj
  have hdet :=
    D.exists_mergedPrefixBefore_mul_commonDet_mul_square_eq_smallPrefixAtLargeSelected
      hcomponent c hscale
  simpa only [LargeCollisionBoundaryDeterminantRelation, k, heq,
    hsmall.1] using hdet

/-- Lemma 5.13 common approximation at the selected unary coordinate when
the large almost-Jordan decomposition has its unique scale collision. -/
theorem weakUnaryDirect_largeCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  classical
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hk.1, hk.2]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  have hsmall := D.weakUnaryDirect_small_coordinates_at_largeSelected
    hfin i₀ hi₀ a b i hposition hlocal
  have hsmallBefore : D.largeSelectedPosition < D.smallSelectedPosition := by
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val < D.smallSelectedPosition.val
    omega
  have hdet : D.LargeCollisionBoundaryDeterminantRelation k heq b i := by
    simpa only [k, heq] using
      D.weakUnaryDirect_largeCollision_boundaryDeterminantRelation
        hfin i₀ hi₀ c hscale a b i hposition hlocal
  exact D.largeCollision_boundaryCommonApproximation c hscale k hk.1 hk.2
    heq a b i hposition hlocal (hsmall.1.trans_le hsmallBefore.le)
      hsmall.2 hdet

/-- Lemma 5.13 common approximation at the selected unary coordinate when
the large almost-Jordan decomposition is already strict.  The small side
is resolved independently, so a possible collision to the right of its
selected component is harmless. -/
theorem weakUnaryDirect_noLargeCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  classical
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hsmall := D.weakUnaryDirect_small_coordinates_at_largeSelected
    hfin i₀ hi₀ a b i hposition hlocal
  have hsmallBefore : D.largeSelectedPosition < D.smallSelectedPosition := by
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val < D.smallSelectedPosition.val
    omega
  have hsmallBound : (y.indexEquiv I).1 ≤ D.smallSelectedPosition :=
    hsmall.1.trans_le hsmallBefore.le
  let hlargeLe := hposition.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallBound
  let C := Rlarge.coordinates
  let E := Rsmall.coordinates
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_noCollision
      hlarge a I hlargeLe
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallBound
  have hlocalLarge : (Rlarge.profile.indexEquiv I).2.val = 0 := by
    rw [Rlarge.localCoordinate_eq, hoffLarge, Nat.zero_add]
    exact hlocal
  have hlocalSmall : (Rsmall.profile.indexEquiv I).2.val = 0 := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add]
    exact hsmall.2
  have hiStartLarge' : I.val = C.start := by
    calc
      I.val = Rlarge.coordinates.start +
          (Rlarge.profile.indexEquiv I).2.val :=
        Rlarge.index_val_eq_coordinates_start_add_local
      _ = Rlarge.coordinates.start + 0 :=
        congrArg (Rlarge.coordinates.start + ·) hlocalLarge
      _ = C.start := by simp only [Nat.add_zero, C]
  have hiStartSmall' : I.val = E.start := by
    calc
      I.val = Rsmall.coordinates.start +
          (Rsmall.profile.indexEquiv I).2.val :=
        Rsmall.index_val_eq_coordinates_start_add_local
      _ = Rsmall.coordinates.start + 0 :=
        congrArg (Rsmall.coordinates.start + ·) hlocalSmall
      _ = E.start := by simp only [Nat.add_zero, E]
  have hstart : C.start = E.start := by
    omega
  have hiStart : i.val = C.start := by
    change I.val = C.start
    exact hiStartLarge'
  have hiC : i.val < C.stop := by
    simpa only [I] using Rlarge.index_val_lt_coordinates_stop
  have hiE : i.val < E.stop := by
    simpa only [I] using Rsmall.index_val_lt_coordinates_stop
  let dLarge := Rlarge.determinantSeedData
  let dSmall := Rsmall.determinantSeedData
  have hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j := by
    intro j hj
    exact D.unaryShift_component_eq_before hfin i₀ hi₀ j hj
  have hdet : ∃ s : Kˣ,
      dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    simpa only [dLarge, dSmall, I, y] using
      D.strictResolution_determinantSeeds_square_at_boundary_of_noLargeCollision
        hlarge a b I hposition hsmall.1 hsmallBound hcomponent
  let S := Rlarge.approximationSeedsWith dLarge
    Rlarge.fundamentalNormGenerator Rlarge.fundamentalNormGenerator_spec
  let T := Rsmall.approximationSeedsWith dSmall
    Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
  have hdet' : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2 := by
    simpa only [S, T,
      BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
        hdet
  apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet'
    i.val 0
  · simpa only [Nat.mul_zero, Nat.add_zero] using hiStart
  · exact hiC
  · exact hiE

/-- Collision-complete common approximation at the selected unary
coordinate. -/
theorem weakUnaryDirect_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  by_cases hcollision : D.LargeScaleCollision
  · let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    exact D.weakUnaryDirect_largeCollision_commonApproximation_at_selected
      hfin i₀ hi₀ c hscale a b i hposition hlocal
  · exact D.weakUnaryDirect_noLargeCollision_commonApproximation_at_selected
      hcollision hfin i₀ hi₀ a b i hposition hlocal

/-- Collision-complete Lemma 5.13 approximation on the literal Lemma 5.17
range of the unary adjacent transposition. -/
theorem weakUnaryDirect_commonApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  rcases D.weakAligned_reducedRange_right_coordinate a i hi with
    hbefore | hposition
  · exact D.weakUnaryDirect_commonApproximation_before_selected
      hfin i₀ hi₀ a b i hbefore hcurrent
  · have hrankAt : finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 1 := by
      rw [hposition, D.largeAlmostJordan_finrank_selected, hfin]
    have hlocalLt : (x.indexEquiv I).2.val < 1 :=
      lt_of_lt_of_eq (x.indexEquiv I).2.isLt hrankAt
    have hlocal : (x.indexEquiv I).2.val = 0 := by omega
    exact D.weakUnaryDirect_commonApproximation_at_selected
      hfin i₀ hi₀ a b i hposition hlocal

/-- Complete collision-safe Lemma 5.13 local data on the unary-shift
Lemma 5.17 range. -/
theorem weakUnaryDirect_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range where
  commonApproximation i hi hcurrent :=
    D.weakUnaryDirect_commonApproximation
      hfin i₀ hi₀ a b i hi hcurrent
  previousPrefixSum_eq i hi hcurrent := by
    have hiDefect : D.DefectReducedRange i :=
      D.weakUnaryDirect_defectReducedRange_of_lemma517Range
        hfin i₀ hi₀ i hi
    exact D.weakUnaryShift_previousPrefixSum_eq_of_current_succ_reduced
      hfin i₀ hi₀ a b i hiDefect hcurrent

/-- The comparison coordinate `i - 1` is strictly before the large unary
selected component throughout the literal Lemma 5.17 range. -/
theorem weakUnaryDirect_alphaCoordinate_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i) :
    ((D.largeWeakProfileWitness a).indexEquiv
      (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
        D.largeSelectedPosition := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  have hiStart : i.val ≤ D.largeSelectedStart := by
    change i.val ≤ D.largeSelectedStart +
      finrank K
        (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
      at hi
    rw [D.largeAlmostJordan_finrank_selected, hfin] at hi
    exact hi
  have hgIndex : g.val < D.largeSelectedStart := by
    change i.val - 1 < D.largeSelectedStart
    have hipos := i.pos
    omega
  apply D.weakUnaryShift_component_before_of_index_lt_start a g.castSucc
  change i.val - 1 <
    ∑ p ∈ Finset.Iio D.largeSelectedPosition,
      finrank K (D.largeAlmostJordan.component p).carrier
  change i.val - 1 < D.largeSelectedStart at hgIndex
  simpa only [largeSelectedStart] using hgIndex

/-- Complete collision-safe condition-(ii) certificate on the unary-shift
Lemma 5.17 range. -/
theorem weakUnaryDirect_defectCertificate_lemma517Range
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let localData := D.weakUnaryDirect_lemma513LocalData hfin i₀ hi₀ a b
  have hbefore := D.weakUnaryDirect_alphaCoordinate_before_selected
    hfin a i hi
  by_cases hlt : a.order g.castSucc < b.order g.castSucc
  · by_cases hsucc : b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) + 1
    · exact D.weakUnaryDirect_oddCertificate_before_selected
        hfin i₀ hi₀ a b i hi hbefore hsucc
    · have hcurrentLt : a.order
            ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
          b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
        have hindex :
            (⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Fin (n + 2)) =
                g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hlt
      exact D.weakUnaryDirect_commonCertificate_before_selected_of_current_lt
        hfin i₀ hi₀ a b i hi hbefore hcurrentLt hsucc
  · by_cases heq : a.order g.castSucc = b.order g.castSucc
    · have hentryEq : a.orderSequence.entryOrZero (i.val - 1) =
          b.orderSequence.entryOrZero (i.val - 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact heq
      exact localData.equalCertificate a b D.smallLattice_le_large
        (D.lemma517Data_proved a b) i hi hentryEq
    · have hgt : b.order g.castSucc < a.order g.castSucc := by omega
      have hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
          a.orderSequence.entryOrZero (i.val - 1) + 1 := by
        rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        omega
      have happrox := localData.commonApproximation i hi hnotSucc
      exact D.weakUnaryDirect_commonCertificate_before_selected_of_current_gt
        hfin i₀ hi₀ a b i hi hbefore hgt happrox

end Lattice.Beli2019Lemma51Data

end Bong
