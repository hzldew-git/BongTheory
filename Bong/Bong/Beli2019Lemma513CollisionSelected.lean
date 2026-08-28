/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513CollisionApproximation
import Bong.Bong.Beli2009ModularSignedDeterminantWeight

/-!
# The terminal collision in Beli (2019), Lemma 5.13(i)

This module proves the exceptional binary endpoint where the enlarged
selected block collides with the preceding common Jordan block.  It is the
formal counterpart of the final paragraph of Lemma 5.13(i).
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- At a large-side collision, the determinant of the small prefix before
the selected component is, up to a square, the determinant before the
amalgamated pair times the determinant of the common left component.  This
is the right-boundary determinant identity silently used when Lemma 3.2 is
applied at `i = n_k` in Beli (2019), Lemma 5.13. -/
theorem exists_mergedPrefixBefore_mul_commonDet_mul_square_eq_smallPrefixAtLargeSelected
    (D : Beli2019Lemma51Data q M N)
    (hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator) :
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    let heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    ∃ z : Kˣ,
      (((D.largeAlmostJordan.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit) *
          (D.largeAlmostJordan.component k.castSucc).refinedDeterminantUnit) *
          z ^ 2 =
        (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.largeSelectedPosition.val
          |>.refinedDeterminantUnit) := by
  classical
  dsimp only
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have hkCommon := hk.1
  have hkSelected := hk.2
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hkCommon, hkSelected]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  let S := (D.largeAlmostJordan.mergeAdjacentAt k heq).toOrthogonalDecomposition
  let p := D.largeSelectedPosition
  let cut := p.val
  have hcut : cut = k.val + 1 := by
    exact congrArg Fin.val hkSelected |>.symm
  have hcutSucc : cut - 1 + 1 = cut := by omega
  have hP : cut - 1 + 1 ≤ D.complementComponentCount + 1 := by
    rw [hcutSucc]
    exact p.isLt.le
  have hQ : cut - 1 + 1 ≤ D.complementComponentCount + 1 := hP
  have hprefixComponent (z : Fin (cut - 1 + 1)) :
      P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
        Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
    let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
    let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
    have hjPVal : jP.val = z.val :=
      P.prefixIndexEquiv_val (cut - 1 + 1) hP z
    have hjQVal : jQ.val = z.val :=
      Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
    have hjEq : jP = jQ := by
      apply Fin.ext
      exact hjPVal.trans hjQVal.symm
    have hjBefore : jP < D.largeSelectedPosition := by
      change jP.val < p.val
      rw [hjPVal]
      have hz := z.isLt
      omega
    change D.largeAlmostJordan.component jP =
      D.smallAlmostJordan.component jQ
    rw [← hjEq]
    exact hcomponent jP hjBefore
  let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
    (fun z ↦ by
      rw [hprefixComponent z]
      exact Lattice.Isometry.refl _ _)
  have hprefixClassRaw := Lattice.determinantClass_eq_of_isometry F
  have hprefixClass :
      unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) := by
    change unitSquareClass K
          ((P.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit)
      at hprefixClassRaw
    rw [hcutSucc] at hprefixClassRaw
    exact hprefixClassRaw
  have happendRaw := P.unitSquareClass_prefix_succ_eq_mul_component k.castSucc
  have happend :
      unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) =
        unitSquareClass K
            ((P.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
          unitSquareClass K
            (P.component k.castSucc).refinedDeterminantUnit := by
    rw [unitSquareClass_mul] at happendRaw
    change unitSquareClass K
        ((P.prefixQuadraticSublattice (k.val + 1)).refinedDeterminantUnit) =
      unitSquareClass K
          ((P.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
        unitSquareClass K (P.component k.castSucc).refinedDeterminantUnit
      at happendRaw
    rw [hcut]
    exact happendRaw
  have hbefore :=
    D.largeAlmostJordan.unitSquareClass_mergeAdjacentAt_prefixBefore k heq
  have htarget :
      unitSquareClass K
          (((S.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
            (P.component k.castSucc).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) := by
    calc
      unitSquareClass K
          (((S.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
            (P.component k.castSucc).refinedDeterminantUnit) =
          unitSquareClass K
              ((S.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
            unitSquareClass K
              (P.component k.castSucc).refinedDeterminantUnit := by
        rw [unitSquareClass_mul]
      _ = unitSquareClass K
              ((P.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
            unitSquareClass K
              (P.component k.castSucc).refinedDeterminantUnit := by
        rw [show unitSquareClass K
              ((S.prefixQuadraticSublattice k.val).refinedDeterminantUnit) =
            unitSquareClass K
              ((P.prefixQuadraticSublattice k.val).refinedDeterminantUnit) by
          simpa only [S, P] using hbefore]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) :=
        happend.symm
      _ = unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) :=
        hprefixClass
  obtain ⟨z, hz⟩ :=
    BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
      (((S.prefixQuadraticSublattice k.val).refinedDeterminantUnit) *
        (P.component k.castSucc).refinedDeterminantUnit)
      ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) htarget
  refine ⟨z, ?_⟩
  simpa only [S, P, Q, cut, p, k] using hz

/-- Aligned specialization of the collision-boundary determinant
transport. -/
theorem exists_mergedPrefixBefore_mul_commonDet_mul_square_eq_smallPrefix
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator) :
    let k := Classical.choose (D.largeCollision_adjacent c hscale)
    let heq : ordUnit K
          (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
      have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
      rw [hk.1, hk.2]
      simpa only [D.largeAlmostJordan_scaleGenerator_selected,
        D.largeAlmostJordan_scaleGenerator_common] using hscale
    ∃ z : Kˣ,
      (((D.largeAlmostJordan.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit) *
          (D.largeAlmostJordan.component k.castSucc).refinedDeterminantUnit) *
          z ^ 2 =
        (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) := by
  have hcomponent : ∀ j : Fin (D.complementComponentCount + 1),
      j < D.largeSelectedPosition →
        D.largeAlmostJordan.component j = D.smallAlmostJordan.component j := by
    intro j hj
    exact D.aligned_component_eq hselected j (ne_of_lt hj)
  simpa only [hselected] using
    D.exists_mergedPrefixBefore_mul_commonDet_mul_square_eq_smallPrefixAtLargeSelected
      hcomponent c hscale

/-- The determinant relation needed at the first coordinate of a selected
component absorbed into the common component on its left.  The small-side
boundary is deliberately allowed to be any weak component at or before the
small selected component; this is the common core of the aligned and unary
shift cases of Beli (2019), Lemma 5.13(i). -/
def LargeCollisionBoundaryDeterminantRelation
    [Beli2006AlphaLaws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (k : Fin D.complementComponentCount)
    (heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ))
    {n : Nat} (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ z : Kˣ,
    (((D.largeAlmostJordan.mergeAdjacentAt k heq).toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit) *
        (D.largeAlmostJordan.component k.castSucc).refinedDeterminantUnit) *
        z ^ 2 =
      (D.smallAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice
          ((D.smallWeakProfileWitness b).indexEquiv
            ⟨i.val, i.lt_large⟩).1.val
        |>.refinedDeterminantUnit)

set_option maxHeartbeats 0 in
/-- Collision-boundary core for the first selected coordinate.  It isolates
the source-side Beli 2.14 argument from the positional determinant transport
on the small side. -/
theorem largeCollision_boundaryCommonApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    (k : Fin D.complementComponentCount)
    (hkCommon : k.castSucc = D.largeCommonPosition c)
    (hkSelected : k.succ = D.largeSelectedPosition)
    (heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ))
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0)
    (hsmallLe :
      ((D.smallWeakProfileWitness b).indexEquiv
        ⟨i.val, i.lt_large⟩).1 ≤ D.smallSelectedPosition)
    (hsmallWeakLocal :
      ((D.smallWeakProfileWitness b).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 0)
    (hdet : D.LargeCollisionBoundaryDeterminantRelation k heq b i) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  classical
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      D.largeAlmostJordan k heq
        (D.largeOnlyScaleCollisionAt c hscale k ⟨hkCommon, hkSelected⟩)
  let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
    Classical.choice
      (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
  have hright : (x.indexEquiv I).1 = k.succ :=
    hposition.trans hkSelected.symm
  have hcoordinates := x.strict_coordinates_of_right
    D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
  let Rlarge : BONG.StrictCoordinateResolution a.toBONG
      D.largeAlmostJordan x I :=
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
        have hpos := D.largeAlmostJordan.component_finrank_pos k.castSucc
        omega
      prefixComponent_eq := by
        intro j hj
        refine ⟨j.castSucc, rfl, ?_⟩
        apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
        rw [hcoordinates.1] at hj
        exact hj
      scaleOrder_eq := by
        unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hcoordinates.1,
          Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
        have hskip : k.succ.succAbove k = k.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
        rw [hskip, hright]
        exact heq
      effectiveNormOrder_eq := by
        rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hcoordinates.1]
        exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq k (x.indexEquiv I).1 _ }
  have hRcomponent : Rlarge.component = k := by
    change (P.indexEquiv I).1 = k
    exact hcoordinates.1
  let J := D.largeAlmostJordan.component k.castSucc
  let commonRank := finrank K J.carrier
  have hcommonRankPos : 0 < commonRank := by
    exact D.largeAlmostJordan.component_finrank_pos k.castSucc
  have hresolvedLocal :
      (Rlarge.profile.indexEquiv I).2.val = commonRank := by
    change (P.indexEquiv I).2.val = commonRank
    rw [hcoordinates.2, hlocal, Nat.add_zero]
  have hlocalPos : 0 < (Rlarge.profile.indexEquiv I).2.val := by
    rw [hresolvedLocal]
    exact hcommonRankPos
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hsmallLocal : (Rsmall.profile.indexEquiv I).2.val = 0 := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add]
    exact hsmallWeakLocal
  have hiLarge : i.val = Rlarge.coordinates.start + commonRank := by
    have hi := Rlarge.index_val_eq_coordinates_start_add_local
    rw [hresolvedLocal] at hi
    exact hi
  have hiSmall : i.val = Rsmall.coordinates.start := by
    have hi := Rsmall.index_val_eq_coordinates_start_add_local
    calc
      i.val = Rsmall.coordinates.start +
          (Rsmall.profile.indexEquiv I).2.val := hi
      _ = Rsmall.coordinates.start := by rw [hsmallLocal, Nat.add_zero]
  have hiLargeStop : i.val < Rlarge.coordinates.stop :=
    Rlarge.index_val_lt_coordinates_stop
  have hiSmallStop : i.val < Rsmall.coordinates.stop :=
    Rsmall.index_val_lt_coordinates_stop
  let dLarge := Rlarge.determinantSeedData
  let dSmall := Rsmall.determinantSeedData
  let seedsSmall := Rsmall.approximationSeedsWith dSmall
    Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
  have hsmallSeedRaw := seedsSmall.evenApproximation 0 (by
    simpa only [Nat.mul_zero, add_zero, ← hiSmall] using hiSmallStop)
  have hsmallSeed : b.IsPrefixApproximation i.val dSmall.leftDet := by
    rw [hiSmall]
    simpa only [Nat.mul_zero, add_zero, pow_zero, one_mul, seedsSmall,
      BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
        hsmallSeedRaw
  let mergedPrefix : Kˣ :=
    (S.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice k.val
      |>.refinedDeterminantUnit)
  have hdLargeMerged : dLarge.leftDet = mergedPrefix := by
    by_cases hkzero : k.val = 0
    · have hRzero : Rlarge.component.val = 0 := by
        rw [hRcomponent, hkzero]
      rw [Rlarge.determinantSeedData_leftDet_of_component_zero hRzero]
      have hsub : Subsingleton
          (S.toOrthogonalDecomposition.prefixQuadraticSublattice k.val).carrier := by
        rw [hkzero]
        exact Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton
          S.toOrthogonalDecomposition
      dsimp only [mergedPrefix]
      exact (Lattice.determinantUnit_eq_one_of_subsingleton _ _ hsub).symm
    · rw [Rlarge.determinantSeedData_leftDet_of_component_ne_zero (by
        rw [hRcomponent]
        exact hkzero)]
      dsimp only [mergedPrefix]
      change
        (Rlarge.jordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice Rlarge.component.val
          |>.refinedDeterminantUnit) =
        (S.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice k.val
          |>.refinedDeterminantUnit)
      rw [hRcomponent]
      rfl
  obtain ⟨zDet, hzDet⟩ := hdet
  have hzDet' :
      (dLarge.leftDet * J.refinedDeterminantUnit) * zDet ^ 2 =
        (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (y.indexEquiv I).1.val
          |>.refinedDeterminantUnit) := by
    simpa only [S, J, hdLargeMerged] using hzDet
  obtain ⟨sSmall, hsSmall⟩ :=
    Rsmall.exists_determinantSeedData_eq_weakPrefix_mul_square hoffSmall
  have hsSmall' :
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (y.indexEquiv I).1.val
          |>.refinedDeterminantUnit) =
        dSmall.leftDet * sSmall ^ 2 := by
    simpa only [dSmall] using hsSmall
  have hdetRelation :
      (dLarge.leftDet * J.refinedDeterminantUnit) * zDet ^ 2 =
        dSmall.leftDet * sSmall ^ 2 := hzDet'.trans hsSmall'
  let sDet := zDet / sSmall
  have hdSmall : dSmall.leftDet =
      (dLarge.leftDet * J.refinedDeterminantUnit) * sDet ^ 2 := by
    calc
      dSmall.leftDet =
          (dSmall.leftDet * sSmall ^ 2) / sSmall ^ 2 := by
        exact (mul_div_cancel_right dSmall.leftDet (sSmall ^ 2)).symm
      _ = ((dLarge.leftDet * J.refinedDeterminantUnit) * zDet ^ 2) /
          sSmall ^ 2 := by rw [← hdetRelation]
      _ = (dLarge.leftDet * J.refinedDeterminantUnit) * sDet ^ 2 := by
        dsimp only [sDet]
        rw [div_pow]
        exact mul_div_assoc
          (dLarge.leftDet * J.refinedDeterminantUnit) (zDet ^ 2)
            (sSmall ^ 2)
  let selectedScale :=
    ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)
  let effective := D.largeAlmostJordan.effectiveNormOrderAt
    (x.indexEquiv I).1 selectedScale
  have hcommonScale :
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc) =
        selectedScale := by
    dsimp only [selectedScale]
    rw [hright]
    exact heq
  have hscaleEffective : selectedScale ≤ effective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      (x.indexEquiv I).1 selectedScale
  have heffectiveCommon : effective =
      D.largeAlmostJordan.effectiveNormOrderAt k.castSucc
        (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc)) := by
    calc
      effective = D.largeAlmostJordan.effectiveNormOrderAt
          (x.indexEquiv I).1
          (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc)) := by
        dsimp only [effective, selectedScale]
        rw [hcommonScale]
      _ = D.largeAlmostJordan.effectiveNormOrderAt k.castSucc
          (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc)) :=
        D.largeAlmostJordan.effectiveNormOrderAt_anchor_irrel
          (x.indexEquiv I).1 k.castSucc _
  let Acommon := D.largeAlmostJordan.normGeneratorUnit k.castSucc
  have hAcommon : Lattice.IsNormGeneratorValue J.space J.lattice Acommon := by
    simpa only [J, Acommon] using
      D.largeAlmostJordan.normGeneratorUnit_spec k.castSucc
  have heffectiveLeNorm : effective ≤ ordUnit K Acommon := by
    rw [heffectiveCommon]
    simpa only [Acommon] using
      D.largeAlmostJordan.effectiveNormOrderAt_scale_le_normOrder k.castSucc
  have hRscale : ordUnit K
      (Rlarge.strictWeak.scaleGenerator Rlarge.component) = selectedScale := by
    have h := Rlarge.scaleOrder_eq
    change ordUnit K
        (Rlarge.strictWeak.scaleGenerator Rlarge.component) = selectedScale at h
    exact h
  have hReffectiveAt : Rlarge.strictWeak.effectiveNormOrderAt
      Rlarge.component selectedScale = effective := by
    have h := Rlarge.effectiveNormOrder_eq
    change Rlarge.strictWeak.effectiveNormOrderAt
        Rlarge.component selectedScale = effective at h
    exact h
  have hReffective : Rlarge.strictWeak.effectiveNormOrderAt
      Rlarge.component
        (ordUnit K (Rlarge.strictWeak.scaleGenerator Rlarge.component)) =
      effective := by
    rw [hRscale]
    exact hReffectiveAt
  let previous : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hpreviousOrderRaw :=
    Rlarge.previousOrder_eq_resolvedLocalOrder hlocalPos
  have hpreviousOrder : a.order previous =
      JordanProfileOrder.localOrder selectedScale effective
        (commonRank - 1) := by
    simpa only [previous, I, hRscale, hReffectiveAt, hresolvedLocal] using
      hpreviousOrderRaw
  have hcapEq :=
    Rlarge.prefixAlphaCap_eq_fundamentalWeight_sub_previousOrder hlocalPos
  have hcapEq' : a.prefixAlphaCap i.val =
      (((Rlarge.jordan.fundamentalWeightOrder Rlarge.component -
          a.order previous : Int) : ℚ) : WithTop ℚ) := by
    simpa only [I, previous] using hcapEq
  have hweightInclusion :
      Lattice.weightIdeal J.space J.lattice ≤
        Lattice.weightIdeal q Rlarge.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation]
    have hgenerator : Lattice.IsNormGeneratorValue q
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc)))
        Rlarge.fundamentalNormGenerator := by
      rw [hcommonScale]
      rw [← Rlarge.fundamentalLattice_eq_scaleTruncation]
      exact Rlarge.fundamentalNormGenerator_spec
    simpa only [J, hcommonScale] using
      D.largeAlmostJordan.componentWeight_le_weightIdeal_scaleTruncation
        k.castSucc Rlarge.fundamentalNormGenerator hgenerator
  have hfundWeightLe :
      Rlarge.jordan.fundamentalWeightOrder Rlarge.component ≤
        Lattice.weightIdealOrder J.space J.lattice := by
    rw [Lattice.weightIdeal_eq_powerIdeal,
      Lattice.weightIdeal_eq_powerIdeal,
      Lattice.powerIdeal_le_iff] at hweightInclusion
    simpa only [Lattice.JordanDecomposition.fundamentalWeightOrder,
      BONG.StrictCoordinateResolution.fundamentalLattice, J] using
        hweightInclusion
  have hcapLeWeight : a.prefixAlphaCap i.val ≤
      (((Lattice.weightIdealOrder J.space J.lattice -
          a.order previous : Int) : ℚ) : WithTop ℚ) := by
    rw [hcapEq']
    norm_cast
    exact_mod_cast sub_le_sub_right hfundWeightLe (a.order previous)
  rcases Nat.even_or_odd commonRank with heven | hodd
  · rcases heven with ⟨half, hhalf⟩
    have hhalfPos : 0 < half := by omega
    let pairs := half - 1
    have hrank : finrank K J.carrier = 2 * pairs + 2 := by
      dsimp only [J, commonRank] at hhalf ⊢
      dsimp only [pairs]
      omega
    have hpreviousOdd : ¬Even (commonRank - 1) := by
      rintro ⟨u, hu⟩
      omega
    have hpreviousEq : a.order previous =
        2 * selectedScale - effective := by
      rw [hpreviousOrder,
        JordanProfileOrder.localOrder_odd_of_scale_le
          hscaleEffective hpreviousOdd]
    have hthreshold :
        2 * ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc) -
            ordUnit K Acommon ≤ a.order previous := by
      rw [hcommonScale, hpreviousEq]
      omega
    have hdetBoundRaw :=
      Lattice.IsModular.weightIdealOrder_sub_le_defect_signedDeterminant_of_even_rank_of_normGenerator
        (D.largeAlmostJordan.modular k.castSucc)
        (D.largeAlmostJordan.component_finrank_pos k.castSucc)
        pairs hrank Acommon hAcommon (a.order previous) hthreshold
    have hdetBound :
        (((Lattice.weightIdealOrder J.space J.lattice -
            a.order previous : Int) : ℚ) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K)
            (((-1 : Kˣ) ^ half) * J.refinedDeterminantUnit) := by
      have hpow : pairs + 1 = half := by
        dsimp only [pairs]
        omega
      simpa only [J, Lattice.QuadraticSublattice.refinedDeterminantUnit,
        hpow] using hdetBoundRaw
    have hcapDefect := hcapLeWeight.trans hdetBound
    let seedsLarge := Rlarge.approximationSeedsWith dLarge
      Rlarge.fundamentalNormGenerator Rlarge.fundamentalNormGenerator_spec
    have hlargeSeedRaw := seedsLarge.evenApproximation half (by
      omega)
    have hlargeSeed : a.IsPrefixApproximation i.val
        (((-1 : Kˣ) ^ half) * dLarge.leftDet) := by
      have hlargeSeedAt : a.IsPrefixApproximation
          (Rlarge.coordinates.start + 2 * half)
          (((-1 : Kˣ) ^ half) * dLarge.leftDet) := by
        simpa only [seedsLarge,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
            hlargeSeedRaw
      convert hlargeSeedAt using 1 <;> omega
    have hproduct :
        (((-1 : Kˣ) ^ half) * dLarge.leftDet) * dSmall.leftDet =
          (((-1 : Kˣ) ^ half) * J.refinedDeterminantUnit) *
            (dLarge.leftDet * sDet) ^ 2 := by
      rw [hdSmall, mul_pow]
      simp only [pow_two]
      ac_rfl
    have hreplace : a.prefixAlphaCap i.val ≤
        BONG.GoodBONG.defectOrder (K := K)
          (((( -1 : Kˣ) ^ half) * dLarge.leftDet) * dSmall.leftDet) := by
      rw [hproduct, BONG.GoodBONG.defectOrder_mul_square]
      exact hcapDefect
    have hlargeApprox := a.isPrefixApproximation_of_defect_mul i.val
      (((-1 : Kˣ) ^ half) * dLarge.leftDet) dSmall.leftDet
        hlargeSeed hreplace
    exact ⟨dSmall.leftDet, hlargeApprox, hsmallSeed⟩
  · rcases hodd with ⟨half, hhalf⟩
    have hrank : finrank K J.carrier = 2 * half + 1 := by
      simpa only [J, commonRank] using hhalf
    have hproper :=
      Lattice.normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
        J.space J.lattice
        (D.largeAlmostJordan.scaleGenerator k.castSucc)
        (D.largeAlmostJordan.modular k.castSucc) ⟨half, hrank⟩
    have hAprincipal : Lattice.principalIdeal (K := K) (Acommon : K) =
        Lattice.principalIdeal (K := K)
          (D.largeAlmostJordan.scaleGenerator k.castSucc : K) := by
      calc
        Lattice.principalIdeal (K := K) (Acommon : K) =
            Lattice.normIdeal J.space J.lattice := hAcommon.2.symm
        _ = Lattice.scaleIdeal J.space J.lattice := hproper
        _ = Lattice.principalIdeal (K := K)
            (D.largeAlmostJordan.scaleGenerator k.castSucc : K) :=
          (D.largeAlmostJordan.modular k.castSucc).scaleIdeal_eq_principal
            (D.largeAlmostJordan.component_finrank_pos k.castSucc)
    have hAOrder : ordUnit K Acommon = selectedScale := by
      have hraw :=
        (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp hAprincipal
      rwa [hcommonScale] at hraw
    have heffectiveEq : effective = selectedScale := by
      apply le_antisymm
      · rw [← hAOrder]
        exact heffectiveLeNorm
      · exact hscaleEffective
    have hpreviousEven : Even (commonRank - 1) := by
      refine ⟨half, ?_⟩
      omega
    have hpreviousEq : a.order previous = effective := by
      rw [hpreviousOrder,
        JordanProfileOrder.localOrder_even_of_scale_le
          hscaleEffective hpreviousEven]
    have hscalePrevious :
        ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc) ≤
          a.order previous := by
      rw [hcommonScale, hpreviousEq, heffectiveEq]
    have hdetBoundRaw :=
      Lattice.IsModular.weightIdealOrder_sub_le_defect_norm_mul_signedDeterminant_of_odd_rank
        (D.largeAlmostJordan.modular k.castSucc)
        (D.largeAlmostJordan.component_finrank_pos k.castSucc)
        half hrank Acommon hAcommon (a.order previous) hscalePrevious
    have hdetBound :
        (((Lattice.weightIdealOrder J.space J.lattice -
            a.order previous : Int) : ℚ) : WithTop ℚ) ≤
          BONG.GoodBONG.defectOrder (K := K)
            (((-1 : Kˣ) ^ (half + 1)) * Acommon *
              J.refinedDeterminantUnit) := by
      simpa only [J, Lattice.QuadraticSublattice.refinedDeterminantUnit] using
        hdetBoundRaw
    have hcapDefect := hcapLeWeight.trans hdetBound
    have hAmem : (Acommon : K) ∈
        Lattice.normGroupSet q Rlarge.fundamentalLattice := by
      rw [Rlarge.fundamentalLattice_eq_scaleTruncation]
      let T := D.largeAlmostJordan.toOrthogonalDecomposition
        |>.modularScaleTruncationDecomposition
          D.largeAlmostJordan.scaleGenerator D.largeAlmostJordan.modular
          (ordUnit K (D.largeAlmostJordan.scaleGenerator k.castSucc))
      have hcomponent : T.component k.castSucc = J := by
        simpa only [T, J] using
          D.largeAlmostJordan.toOrthogonalDecomposition
            |>.modularScaleTruncationDecomposition_component_self
              D.largeAlmostJordan.scaleGenerator
                D.largeAlmostJordan.modular k.castSucc
      have hAinT : (Acommon : K) ∈
          Lattice.normGroupSet (T.component k.castSucc).space
            (T.component k.castSucc).lattice := by
        rw [hcomponent]
        exact hAcommon.1
      have hsubset := T.component_normGroupSet_subset k.castSucc hAinT
      rw [hright, ← heq]
      exact hsubset
    have hAfund : Lattice.IsNormGeneratorValue q
        Rlarge.fundamentalLattice Acommon := by
      refine ⟨hAmem, ?_⟩
      rw [Rlarge.normIdeal_fundamentalLattice_eq_powerIdeal]
      change Lattice.powerIdeal (K := K) effective =
        Lattice.principalIdeal (K := K) (Acommon : K)
      rw [heffectiveEq, ← hAOrder]
      exact (Lattice.principalIdeal_eq_powerIdeal Acommon).symm
    let seedsLarge := Rlarge.approximationSeedsWith dLarge (-Acommon)
      hAfund.neg
    have hlargeSeedRaw := seedsLarge.oddApproximation half (by
      omega)
    have hlargeSeed : a.IsPrefixApproximation i.val
        (((-1 : Kˣ) ^ half) * ((-Acommon) * dLarge.leftDet)) := by
      have hlargeSeedAt : a.IsPrefixApproximation
          (Rlarge.coordinates.start + 1 + 2 * half)
          (((-1 : Kˣ) ^ half) * ((-Acommon) * dLarge.leftDet)) := by
        simpa only [seedsLarge,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
            hlargeSeedRaw
      convert hlargeSeedAt using 1 <;> omega
    have hsign :
        ((-1 : Kˣ) ^ half) * (-Acommon) =
          ((-1 : Kˣ) ^ (half + 1)) * Acommon := by
      rw [show -Acommon = (-1 : Kˣ) * Acommon by simp, pow_succ]
      ac_rfl
    have hproduct :
        (((-1 : Kˣ) ^ half) * ((-Acommon) * dLarge.leftDet)) *
            dSmall.leftDet =
          (((-1 : Kˣ) ^ (half + 1)) * Acommon *
            J.refinedDeterminantUnit) *
              (dLarge.leftDet * sDet) ^ 2 := by
      rw [hdSmall, mul_pow]
      simp only [pow_two]
      calc
        (((-1 : Kˣ) ^ half) * (-Acommon * dLarge.leftDet)) *
              ((dLarge.leftDet * J.refinedDeterminantUnit) * (sDet * sDet)) =
            (((( -1 : Kˣ) ^ half) * (-Acommon)) * dLarge.leftDet) *
              ((dLarge.leftDet * J.refinedDeterminantUnit) * (sDet * sDet)) := by
                ac_rfl
        _ = (((( -1 : Kˣ) ^ (half + 1)) * Acommon) * dLarge.leftDet) *
              ((dLarge.leftDet * J.refinedDeterminantUnit) * (sDet * sDet)) := by
                rw [hsign]
        _ = (((-1 : Kˣ) ^ (half + 1)) * Acommon *
              J.refinedDeterminantUnit) *
                ((dLarge.leftDet * dLarge.leftDet) * (sDet * sDet)) := by
                  ac_rfl
    have hreplace : a.prefixAlphaCap i.val ≤
        BONG.GoodBONG.defectOrder (K := K)
          ((((-1 : Kˣ) ^ half) * ((-Acommon) * dLarge.leftDet)) *
            dSmall.leftDet) := by
      rw [hproduct, BONG.GoodBONG.defectOrder_mul_square]
      exact hcapDefect
    have hlargeApprox := a.isPrefixApproximation_of_defect_mul i.val
      (((-1 : Kˣ) ^ half) * ((-Acommon) * dLarge.leftDet))
        dSmall.leftDet hlargeSeed hreplace
    exact ⟨dSmall.leftDet, hlargeApprox, hsmallSeed⟩

set_option maxHeartbeats 0 in
/-- The aligned first-coordinate endpoint recovered from the reusable
collision-boundary core. -/
theorem largeCollision_selectedFirst_commonApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
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
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let k := Classical.choose (D.largeCollision_adjacent c hscale)
  have hk := Classical.choose_spec (D.largeCollision_adjacent c hscale)
  have hkCommon := hk.1
  have hkSelected := hk.2
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hkCommon, hkSelected]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  have hxy := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 = D.smallSelectedPosition :=
    hxy.1.symm.trans (hposition.trans hselected.symm)
  have hsmallWeakLocal : (y.indexEquiv I).2.val = 0 :=
    hxy.2.symm.trans hlocal
  have hdet : D.LargeCollisionBoundaryDeterminantRelation k heq b i := by
    simpa only [LargeCollisionBoundaryDeterminantRelation, k, I, y,
      hsmallPosition] using
        D.exists_mergedPrefixBefore_mul_commonDet_mul_square_eq_smallPrefix
          hselected c hscale
  exact D.largeCollision_boundaryCommonApproximation c hscale k hkCommon
    hkSelected heq a b i hposition hlocal hsmallPosition.le
      hsmallWeakLocal hdet

/-- At the second coordinate of the aligned selected binary block, a
one-step rise of the two selected effective norm orders is exactly the
current-order jump excluded in Lemma 5.13(i).  This calculation uses only
the weak profiles, so it remains valid when either almost-Jordan family has
an adjacent scale collision. -/
theorem selectedBinary_effectiveNormOrder_ne_add_one_of_current_ne
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hlocal :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).2.val = 1)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
        (ordUnit K D.input.block.scaleGenerator) ≠
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) + 1 := by
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := D.largeSelectedPosition
  let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let targetSmall := ordUnit K D.input.block.scaleGenerator
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt p targetLarge
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition targetSmall
  change eSmall ≠ eLarge + 1
  intro hone
  apply hcurrent
  let I : Fin (n + 2) := ⟨i.val - 1, by
    have := i.pos
    have := i.lt_large
    omega⟩
  have hrank : finrank K
      (D.largeAlmostJordan.component p).carrier = 2 := by
    simpa only [p, D.largeAlmostJordan_finrank_selected] using hfin
  let localZero : Fin
      (finrank K (D.largeAlmostJordan.component p).carrier) :=
    ⟨0, by rw [hrank]; omega⟩
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = x.componentStart p + 1 := by
    have hpositionX : (x.indexEquiv R).1 = p := hposition
    have hlocalX : (x.indexEquiv R).2.val = 1 := hlocal
    have hstartEq : x.componentStart (x.indexEquiv R).1 =
        x.componentStart p := congrArg x.componentStart hpositionX
    calc
      i.val = x.componentStart (x.indexEquiv R).1 +
          (x.indexEquiv R).2.val := by
        unfold BONG.WeakJordanOrderProfileWitness.componentStart
        simpa only [R] using hglobal
      _ = x.componentStart p + 1 := by omega
  have hI : I = x.indexEquiv.symm ⟨p, localZero⟩ := by
    apply Fin.ext
    rw [x.inverse_index_val]
    change i.val - 1 = x.componentStart p
    rw [hiStart]
    omega
  have hxI : x.indexEquiv I = ⟨p, localZero⟩ := by
    rw [hI, x.indexEquiv.apply_symm_apply]
  have hxyI := D.weakProfile_coordinates_eq hselected a b I
  have hlargeScale : targetLarge ≤ eLarge :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p targetLarge
  have hsmallScale : targetSmall ≤ eSmall :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      D.smallSelectedPosition targetSmall
  have hlargeOrder := D.largeWeak_order_eq_localOrder a I
  have hsmallOrder := D.smallWeak_order_eq_localOrder b I
  have hxIPosition : (x.indexEquiv I).1 = p := by rw [hxI]
  have hxILocal : (x.indexEquiv I).2.val = 0 := by rw [hxI]
  have hyIPosition : (y.indexEquiv I).1 = D.smallSelectedPosition := by
    calc
      (y.indexEquiv I).1 = (x.indexEquiv I).1 := hxyI.1.symm
      _ = p := hxIPosition
      _ = D.smallSelectedPosition := hselected.symm
  have hyILocal : (y.indexEquiv I).2.val = 0 :=
    hxyI.2.symm.trans hxILocal
  have hlargeOrder' : a.order I =
      JordanProfileOrder.localOrder targetLarge eLarge 0 := by
    simpa only [x, hxIPosition, hxILocal, p, targetLarge, eLarge,
      D.largeAlmostJordan_scaleGenerator_selected] using hlargeOrder
  have hsmallOrder' : b.order I =
      JordanProfileOrder.localOrder targetSmall eSmall 0 := by
    simpa only [y, hyIPosition, hyILocal, targetSmall, eSmall,
      D.smallAlmostJordan_scaleGenerator_selected] using hsmallOrder
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hlargeScale (by simp)] at hlargeOrder'
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsmallScale (by simp)] at hsmallOrder'
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (by have := i.lt_large; omega),
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence
      (by have := i.lt_large; omega)]
  change b.order I = a.order I + 1
  exact hsmallOrder'.trans <| hone.trans <|
    congrArg (fun z : Int ↦ z + 1) hlargeOrder'.symm

set_option maxHeartbeats 0 in
theorem largeCollision_selectedLast_commonApproximation_of_effective_eq_or_add_two
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
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
        ⟨i.val, i.lt_large⟩).2.val = 1)
    (heffectiveCases :
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator) =
          D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator) ∨
        D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator) =
          D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
              (ordUnit K D.input.block.enlargedScaleGenerator) + 2) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  classical
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  obtain ⟨k, hkCommon, hkSelected⟩ :=
    D.largeCollision_adjacent c hscale
  have heq : ordUnit K
        (D.largeAlmostJordan.scaleGenerator k.castSucc) =
      ordUnit K (D.largeAlmostJordan.scaleGenerator k.succ) := by
    rw [hkCommon, hkSelected]
    simpa only [D.largeAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_common] using hscale
  let S := D.largeAlmostJordan.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      D.largeAlmostJordan k heq
        (D.largeOnlyScaleCollisionAt c hscale k ⟨hkCommon, hkSelected⟩)
  let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
    Classical.choice
      (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
  have hright : (x.indexEquiv I).1 = k.succ :=
    hposition.trans hkSelected.symm
  have hcoordinates := x.strict_coordinates_of_right
    D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hright
  let Rlarge : BONG.StrictCoordinateResolution a.toBONG
      D.largeAlmostJordan x I :=
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
        have hpos := D.largeAlmostJordan.component_finrank_pos k.castSucc
        omega
      prefixComponent_eq := by
        intro j hj
        refine ⟨j.castSucc, rfl, ?_⟩
        apply D.largeAlmostJordan.mergeAdjacentAt_component_of_lt k heq
        rw [hcoordinates.1] at hj
        exact hj
      scaleOrder_eq := by
        unfold Lattice.JordanDecomposition.fundamentalScaleOrder
        rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
          hcoordinates.1,
          Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
        have hskip : k.succ.succAbove k = k.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt]
          exact Fin.castSucc_lt_succ_iff.mpr (Fin.le_refl k)
        rw [hskip, hright]
        exact heq
      effectiveNormOrder_eq := by
        rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan,
          hcoordinates.1]
        exact D.largeAlmostJordan.effectiveNormOrderAt_mergeAdjacentAt
          k heq k (x.indexEquiv I).1 _ }
  have hlargeRankEq :
      Rlarge.jordan.componentRank Rlarge.component =
        finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 2 := by
    change finrank K (S.component (P.indexEquiv I).1).carrier = _
    rw [hcoordinates.1,
      D.largeAlmostJordan.mergeAdjacentAt_componentRank_self k heq,
      hkSelected, D.largeAlmostJordan_finrank_selected, hfin]
  have hlargeRank : 2 ≤ Rlarge.jordan.componentRank Rlarge.component := by
    rw [hlargeRankEq]
    omega
  have hiEnd : i.val = Rlarge.coordinates.stop - 1 := by
    have hi := Rlarge.index_val_eq_coordinates_start_add_local
    have hlocalResolved : (Rlarge.profile.indexEquiv I).2.val =
        finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 1 := by
      change (P.indexEquiv I).2.val = _
      rw [hcoordinates.2, hlocal]
    have hstop : Rlarge.coordinates.stop =
        Rlarge.coordinates.start +
          Rlarge.jordan.componentRank Rlarge.component := rfl
    calc
      i.val = Rlarge.coordinates.start +
          (Rlarge.profile.indexEquiv I).2.val := hi
      _ = Rlarge.coordinates.start +
          (finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 1) :=
        by rw [hlocalResolved]
      _ = (Rlarge.coordinates.start +
          (finrank K (D.largeAlmostJordan.component k.castSucc).carrier + 2)) - 1 :=
        by omega
      _ = Rlarge.coordinates.stop - 1 := by
        rw [hstop, hlargeRankEq]
  have hxy := D.weakProfile_coordinates_eq hselected a b I
  have hsmallPosition : (y.indexEquiv I).1 = D.smallSelectedPosition :=
    hxy.1.symm.trans (hposition.trans hselected.symm)
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallPosition.le
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallPosition.le
  have hinclude : Rsmall.fundamentalLattice ≤ Rlarge.fundamentalLattice := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation,
      Rlarge.fundamentalLattice_eq_scaleTruncation]
    change Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) ≤
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
    rw [hsmallPosition, hposition,
      D.smallAlmostJordan_scaleGenerator_selected,
      D.largeAlmostJordan_scaleGenerator_selected]
    intro z hz
    exact D.scaleTruncation_small_le_large
      (ordUnit K D.input.block.enlargedScaleGenerator) le_rfl
        (Lattice.scaleTruncation_anti (q := q) (L := N)
          D.enlargedScaleOrder_lt_smallScaleOrder.le hz)
  have heffectiveEq (heffective :
      D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
          (ordUnit K D.input.block.enlargedScaleGenerator) =
        D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
          (ordUnit K D.input.block.scaleGenerator)) :
      D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv I).1)) =
        D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1)) := by
    rw [hposition, hsmallPosition,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected]
    exact heffective
  have hrescale : Lattice.rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator
            (x.indexEquiv I).1))) ≤
      Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          (y.indexEquiv I).1))
    rw [hposition, hsmallPosition,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected]
    exact D.rescale_largeFundamental_le_small_of_rank_two hfin
  have heffectiveTwo (heffective :
      D.smallAlmostJordan.effectiveNormOrderAt D.smallSelectedPosition
            (ordUnit K D.input.block.scaleGenerator) =
        D.largeAlmostJordan.effectiveNormOrderAt D.largeSelectedPosition
            (ordUnit K D.input.block.enlargedScaleGenerator) + 2) :
      D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1)) =
        D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1)) + 2 := by
    rw [hposition, hsmallPosition,
      D.largeAlmostJordan_scaleGenerator_selected,
      D.smallAlmostJordan_scaleGenerator_selected]
    exact heffective
  have hpos : 0 < finrank K V := by
    rw [← a.toBONG.length_eq_finrank]
    omega
  obtain ⟨A, B, sNorm, hALarge, hBSmall, hB⟩ :
      ∃ A B sNorm : Kˣ,
        Lattice.IsNormGeneratorValue q Rlarge.fundamentalLattice A ∧
          Lattice.IsNormGeneratorValue q Rsmall.fundamentalLattice B ∧
            B = A * sNorm ^ 2 := by
    rcases heffectiveCases with heffective | heffective
    · obtain ⟨A, hALarge, hASmall⟩ :=
        Rlarge.exists_commonNormGenerator_of_effective_eq Rsmall hinclude
          (heffectiveEq heffective)
      exact ⟨A, A, 1, hALarge, hASmall, by simp⟩
    · let A := Rlarge.fundamentalNormGenerator
      let B := (uniformizerUnit K) ^ 2 * A
      have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
        hpos hrescale (heffectiveTwo heffective)
      refine ⟨A, B, uniformizerUnit K, hpair.1, hpair.2, ?_⟩
      dsimp only [B]
      ac_rfl
  let determinantSmall := Rsmall.determinantSeedData
  let seedsSmall := Rsmall.approximationSeedsWith determinantSmall B hBSmall
  have hsmallLocal : (Rsmall.profile.indexEquiv I).2.val = 1 := by
    rw [Rsmall.localCoordinate_eq, hoffSmall, Nat.zero_add]
    exact hxy.2.symm.trans hlocal
  have hiSmall : i.val = Rsmall.coordinates.start + 1 := by
    have hi := Rsmall.index_val_eq_coordinates_start_add_local
    rw [hsmallLocal] at hi
    exact hi
  have hsmallInside : Rsmall.coordinates.start + 1 <
      Rsmall.coordinates.stop := by
    rw [← hiSmall]
    exact Rsmall.index_val_lt_coordinates_stop
  have hsmallSeed := seedsSmall.oddApproximation 0 (by
    simpa only [Nat.mul_zero, add_zero] using hsmallInside)
  have hsmallSeed' : b.IsPrefixApproximation i.val
      (B * determinantSmall.leftDet) := by
    rw [hiSmall]
    simpa only [Nat.mul_zero, add_zero, pow_zero, one_mul, seedsSmall,
      BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
      BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using
        hsmallSeed
  obtain ⟨sSmall, hsSmall⟩ :=
    Rsmall.exists_determinantSeedData_eq_weakPrefix_mul_square hoffSmall
  let dSmall : Kˣ :=
    (D.smallAlmostJordan.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice D.smallSelectedPosition.val
      |>.refinedDeterminantUnit)
  have hsSmall' : dSmall = determinantSmall.leftDet * sSmall ^ 2 := by
    change ((D.smallWeakProfileWitness b).indexEquiv I).1 =
      D.smallSelectedPosition at hsmallPosition
    rw [hsmallPosition] at hsSmall
    simpa only [dSmall, determinantSmall] using hsSmall
  have hsmallApprox : b.IsPrefixApproximation i.val (B * dSmall) := by
    rw [hsSmall']
    have hmul : B * (determinantSmall.leftDet * sSmall ^ 2) =
        (B * determinantSmall.leftDet) * sSmall ^ 2 := by
      ac_rfl
    rw [hmul]
    exact (b.isPrefixApproximation_mul_square_iff i.val
      (B * determinantSmall.leftDet) sSmall).2 hsmallSeed'
  have hlargeSeed :=
    BONG.WeakJordanOrderProfileWitness.corollary33_prescribedPrefixApproximation
      a Rlarge.strictWeak Rlarge.hasImproperEvenRank
        Rlarge.scaleOrder_strict Rlarge.profile Rlarge.component (-A)
          hALarge.neg hlargeRank
  change a.IsPrefixApproximation (Rlarge.coordinates.stop - 1)
      ((-A) *
        (Rlarge.jordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (Rlarge.component.val + 1)
          |>.refinedDeterminantUnit)) at hlargeSeed
  rw [← hiEnd] at hlargeSeed
  let dMerged : Kˣ :=
    (Rlarge.jordan.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (Rlarge.component.val + 1)
      |>.refinedDeterminantUnit)
  change a.IsPrefixApproximation i.val ((-A) * dMerged) at hlargeSeed
  let dOldLarge : Kˣ :=
    (D.largeAlmostJordan.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (D.largeSelectedPosition.val + 1)
      |>.refinedDeterminantUnit)
  let dEnlarged : Kˣ := D.input.enlargedComponent.refinedDeterminantUnit
  obtain ⟨sMerge, hsMerge⟩ :=
    D.largeAlmostJordan.exists_mergeAdjacentAt_prefixThrough_mul_square k heq
  have hkVal : k.val + 1 = D.largeSelectedPosition.val := by
    exact congrArg Fin.val hkSelected
  have hRcomponent : Rlarge.component = k := by
    change (P.indexEquiv I).1 = k
    exact hcoordinates.1
  have hsMerge' : dOldLarge * sMerge ^ 2 = dMerged := by
    dsimp only [dOldLarge, dMerged]
    rw [show D.largeSelectedPosition.val + 1 = k.val + 2 by omega,
      hRcomponent]
    change
      (D.largeAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (k.val + 2)
        |>.refinedDeterminantUnit) * sMerge ^ 2 =
      (Rlarge.jordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (k.val + 1)
        |>.refinedDeterminantUnit)
    change
      (D.largeAlmostJordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (k.val + 2)
        |>.refinedDeterminantUnit) * sMerge ^ 2 =
      ((D.largeAlmostJordan.mergeAdjacentAt k heq).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (k.val + 1)
        |>.refinedDeterminantUnit)
    exact hsMerge
  obtain ⟨sDet, hsDet⟩ :=
    D.exists_largeSelectedPrefixDeterminant_eq_smallPrefix_mul_enlarged_square
      hselected c hscale
  have hsDet' : dSmall * dEnlarged * sDet ^ 2 = dOldLarge := by
    simpa only [dSmall, dEnlarged, dOldLarge] using hsDet
  have hdMerged : dMerged =
      dSmall * dEnlarged * (sDet * sMerge) ^ 2 := by
    rw [← hsMerge', ← hsDet']
    rw [mul_pow]
    ac_rfl
  have hweakRank :
      finrank K
        (D.largeAlmostJordan.component (x.indexEquiv I).1).carrier = 2 := by
    rw [hposition, D.largeAlmostJordan_finrank_selected, hfin]
  have hdefect :=
    Rlarge.prefixAlphaCap_stop_sub_one_le_defect_neg_weakComponentDeterminant
      hweakRank hlargeRank
  have hdefect' : a.prefixAlphaCap i.val ≤
      BONG.GoodBONG.defectOrder (K := K) (-dEnlarged) := by
    rw [hiEnd]
    have hpositionX : (x.indexEquiv I).1 = D.largeSelectedPosition :=
      hposition
    rw [hpositionX, D.largeAlmostJordan_component_selected] at hdefect
    simpa only [dEnlarged] using hdefect
  have hproduct : ((-A) * dMerged) * (B * dSmall) =
      (-dEnlarged) *
        (A * dSmall * (sNorm * (sDet * sMerge))) ^ 2 := by
    rw [hB, hdMerged]
    rw [show -A = (-1 : Kˣ) * A by simp,
      show -dEnlarged = (-1 : Kˣ) * dEnlarged by simp, mul_pow]
    simp only [pow_two]
    ac_rfl
  have hreplace : a.prefixAlphaCap i.val ≤
      BONG.GoodBONG.defectOrder (K := K)
        (((-A) * dMerged) * (B * dSmall)) := by
    rw [hproduct, BONG.GoodBONG.defectOrder_mul_square]
    exact hdefect'
  have hlargeApprox : a.IsPrefixApproximation i.val (B * dSmall) :=
    a.isPrefixApproximation_of_defect_mul i.val ((-A) * dMerged)
      (B * dSmall) hlargeSeed hreplace
  exact ⟨B * dSmall, hlargeApprox, hsmallApprox⟩

set_option maxHeartbeats 0 in
/-- The terminal collision theorem in the form used by Lemma 5.13(i).
The universal two-step bound leaves three possible effective norm-order
differences; the current-order hypothesis rules out the middle one. -/
theorem largeCollision_selectedLast_commonApproximation_of_current_ne
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (hfin : finrank K D.input.block.component.carrier = 2)
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
        ⟨i.val, i.lt_large⟩).2.val = 1)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let targetLarge := ordUnit K D.input.block.enlargedScaleGenerator
  let targetSmall := ordUnit K D.input.block.scaleGenerator
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt
    D.largeSelectedPosition targetLarge
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt
    D.smallSelectedPosition targetSmall
  have hlargeLe := D.largeSelected_effectiveNormOrder_le_smallSelected
  have hsmallLe :=
    D.smallSelected_effectiveNormOrder_le_largeSelected_add_two_of_rank_two
      hfin
  change eLarge ≤ eSmall at hlargeLe
  change eSmall ≤ eLarge + 2 at hsmallLe
  have hnotOne : eSmall ≠ eLarge + 1 := by
    simpa only [eLarge, eSmall, targetLarge, targetSmall] using
      D.selectedBinary_effectiveNormOrder_ne_add_one_of_current_ne
        hselected hfin a b i hposition hlocal hcurrent
  have hcases : eLarge = eSmall ∨ eSmall = eLarge + 2 := by
    omega
  exact
    D.largeCollision_selectedLast_commonApproximation_of_effective_eq_or_add_two
      hselected hfin c hscale a b i hposition hlocal (by
        simpa only [eLarge, eSmall, targetLarge, targetSmall] using hcases)

/-- At an aligned selected block with a large-side collision, the first
coordinate is covered by the collision-boundary determinant argument above;
in rank two the remaining coordinate is the terminal binary argument. -/
theorem largeCollision_commonApproximation_at_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hposition :
      ((D.largeWeakProfileWitness a).indexEquiv
        ⟨i.val, i.lt_large⟩).1 = D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let localCoord := ((D.largeWeakProfileWitness a).indexEquiv I).2.val
  have hlocalLt : localCoord <
      finrank K
        (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv I).1).carrier :=
    ((D.largeWeakProfileWitness a).indexEquiv I).2.isLt
  rw [hposition, D.largeAlmostJordan_finrank_selected] at hlocalLt
  rcases D.rank_one_or_two with hOne | hTwo
  · have hlocalZero : localCoord = 0 := by omega
    exact D.largeCollision_selectedFirst_commonApproximation
      hselected c hscale a b i hposition (by
        simpa only [localCoord] using hlocalZero)
  · have hlocalCases : localCoord = 0 ∨ localCoord = 1 := by omega
    rcases hlocalCases with hlocalZero | hlocalOne
    · exact D.largeCollision_selectedFirst_commonApproximation
        hselected c hscale a b i hposition (by
          simpa only [localCoord] using hlocalZero)
    · exact D.largeCollision_selectedLast_commonApproximation_of_current_ne
        hselected hTwo c hscale a b i hposition (by
          simpa only [localCoord] using hlocalOne) hcurrent

/-- Complete direct-range Lemma 5.13 data in the aligned large-collision
case.  Coordinates before the selected block use collision-resolved strict
coordinates; the selected coordinate is dispatched by its rank and parity.
The prefix-sum implication is independent of strictification. -/
theorem largeCollision_aligned_lemma513LocalData
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2)) :
    BONG.GoodBONG.Beli2019Lemma513LocalData a b D.Lemma517Range where
  commonApproximation i hi hcurrent := by
    rcases D.weakAligned_reducedRange_right_coordinate a i hi with
      hbefore | hposition
    · exact D.weakAligned_commonApproximation_before_selected
        hselected a b i hbefore hcurrent
    · exact D.largeCollision_commonApproximation_at_selected
        hselected c hscale a b i hposition hcurrent
  previousPrefixSum_eq i hi hcurrent := by
    have hstart :=
      D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
    change D.largeSelectedStart = D.smallSelectedStart at hstart
    have hiDefect : D.DefectReducedRange i := by
      change i.val ≤ D.largeSelectedStart +
        finrank K
          (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1
        at hi
      change i.val ≤ D.smallSelectedStart +
        finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      rw [D.largeAlmostJordan_finrank_selected] at hi
      rw [D.smallAlmostJordan_finrank_selected, ← hstart]
      exact hi
    exact D.weakAllRanks_previousPrefixSum_eq_of_current_succ_reduced
      a b i hiDefect hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
