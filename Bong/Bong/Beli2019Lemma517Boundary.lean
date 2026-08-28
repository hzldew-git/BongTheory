/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma514

/-!
# Boundary branch of Beli (2019), Lemma 5.17(i)

This file applies Lemmas 5.14 and 5.16 at an ordinary Jordan boundary before
the distinguished component.  The proof constructs the boundary from the
last local coordinate, embeds both adjacent intrinsic lattices, and invokes
the parity-free boundary comparison.
-/

namespace Bong

open Dyadic Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Up to and including the distinguished component, the large-side
fundamental scale is no greater than the small-side scale and stays in the
range of Lemma 5.16. -/
theorem noCollision_componentScale_interval_of_le_selected
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1))
    (hp : p ≤ D.largeSelectedPosition) :
    (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder p ≤
        (D.smallNoCollisionJordan hsmall).fundamentalScaleOrder p ∧
      (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder p ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
  rcases hp.lt_or_eq with hbefore | hpEq
  · have hscaleEq := D.weakAligned_scaleOrder_eq_before_selected
      hselected p hbefore
    have hboundRaw := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    have hbound :
        ordUnit K (D.largeAlmostJordan.scaleGenerator p) ≤
          ordUnit K D.input.block.enlargedScaleGenerator := by
      simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hboundRaw
    constructor
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        D.smallNoCollisionJordan_fundamentalScaleOrder]
      exact hscaleEq.le
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder]
      exact hbound
  · have hsmallGenerator :
        ordUnit K (D.smallAlmostJordan.scaleGenerator
          D.largeSelectedPosition) =
          ordUnit K D.input.block.scaleGenerator := by
      rw [← hselected, D.smallAlmostJordan_scaleGenerator_selected]
    constructor
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        D.smallNoCollisionJordan_fundamentalScaleOrder,
        hpEq,
        D.largeAlmostJordan_scaleGenerator_selected,
        hsmallGenerator]
      exact D.enlargedScaleOrder_lt_smallScaleOrder.le
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        hpEq, D.largeAlmostJordan_scaleGenerator_selected]

/-- Lemma 5.17(i) at the last coordinate of a common component strictly
before the distinguished component, in the aligned collision-free case. -/
theorem noCollision_prefixAlphaCap_le_of_boundary_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hbefore :
      let g : Fin n := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
          g.castSucc).1 < D.largeSelectedPosition)
    (hlargeLast :
      let g : Fin n := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
          g.castSucc).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
            g.castSucc).1) :
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
  let Plarge := D.largeNoCollisionProfileWitness hlarge a
  let Psmall := D.smallNoCollisionProfileWitness hsmall b
  let H := D.largeNoCollisionJordan hlarge
  let J := D.smallNoCollisionJordan hsmall
  let p : Fin (D.complementComponentCount + 1) :=
    (Plarge.indexEquiv g.castSucc).1
  change p < D.largeSelectedPosition at hbefore
  change (Plarge.indexEquiv g.castSucc).2.val + 1 =
    H.componentRank p at hlargeLast
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b g.castSucc
  change p = (Psmall.indexEquiv g.castSucc).1 ∧
    (Plarge.indexEquiv g.castSucc).2.val =
      (Psmall.indexEquiv g.castSucc).2.val at hcoordinates
  have hrank := congrFun
    (D.noCollision_componentRank_eq hsmall hlarge hselected) p
  change H.componentRank p = J.componentRank p at hrank
  let z : Fin D.complementComponentCount := ⟨p.val, by
    have hpSelected := hbefore
    have hselectedLt := D.largeSelectedPosition.isLt
    omega⟩
  let pNext : Fin (D.complementComponentCount + 1) := ⟨p.val + 1, by
    have hpSelected := hbefore
    have hselectedLt := D.largeSelectedPosition.isLt
    omega⟩
  have hzLeft : Lattice.JordanDecomposition.boundaryLeftIndex z = p := by
    apply Fin.ext
    rfl
  have hzRight : Lattice.JordanDecomposition.boundaryRightIndex z = pNext := by
    apply Fin.ext
    rfl
  have hlargeBoundary : Plarge.boundaryIndex z = g := by
    apply Plarge.boundaryIndex_eq_of_indexEquiv_last g z
    · exact hzLeft.symm
    · exact hlargeLast
  have hsmallLast : (Psmall.indexEquiv g.castSucc).2.val + 1 =
      J.componentRank (Psmall.indexEquiv g.castSucc).1 := by
    calc
      (Psmall.indexEquiv g.castSucc).2.val + 1 =
          (Plarge.indexEquiv g.castSucc).2.val + 1 := by omega
      _ = H.componentRank p := hlargeLast
      _ = J.componentRank p := hrank
      _ = J.componentRank (Psmall.indexEquiv g.castSucc).1 := by
        rw [← hcoordinates.1]
  have hsmallComponent : (Psmall.indexEquiv g.castSucc).1 =
      Lattice.JordanDecomposition.boundaryLeftIndex z := by
    calc
      (Psmall.indexEquiv g.castSucc).1 = p := hcoordinates.1.symm
      _ = Lattice.JordanDecomposition.boundaryLeftIndex z := hzLeft.symm
  have hsmallBoundary : Psmall.boundaryIndex z = g := by
    exact Psmall.boundaryIndex_eq_of_indexEquiv_last g z
      hsmallComponent hsmallLast
  have hleftInterval := D.noCollision_componentScale_interval_of_le_selected
    hsmall hlarge hselected p hbefore.le
  have hrightLe : pNext ≤ D.largeSelectedPosition := by
    apply Fin.le_iff_val_le_val.mpr
    dsimp only [pNext]
    exact hbefore
  have hrightInterval := D.noCollision_componentScale_interval_of_le_selected
    hsmall hlarge hselected pNext hrightLe
  have hleftLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
    rw [hzLeft]
    exact D.smallFundamentalLattice_le_large_of_scale_le p p
      hleftInterval.1 hleftInterval.2
  have hrightLattice : J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z) ≤
      H.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryRightIndex z) := by
    rw [hzRight]
    exact D.smallFundamentalLattice_le_large_of_scale_le pNext pNext
      hrightInterval.1 hrightInterval.2
  have hleftScale : J.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex z) =
      H.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex z) := by
    have hscaleEq := D.weakAligned_scaleOrder_eq_before_selected
      hselected p hbefore
    rw [hzLeft,
      D.smallNoCollisionJordan_fundamentalScaleOrder,
      D.largeNoCollisionJordan_fundamentalScaleOrder]
    exact hscaleEq.symm
  have halpha := BONG.alphaValue_le_of_boundary_fundamentalLattices_le
    a b Psmall Plarge z hleftScale hleftLattice hrightLattice
  rw [hlargeBoundary, hsmallBoundary] at halpha
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large]
  have halphaTop : (a.alphaValue g : WithTop ℚ) ≤
      (b.alphaValue g : WithTop ℚ) := by
    exact_mod_cast halpha
  simpa only [g] using halphaTop

/-- Complete Lemma 5.17(i) in the aligned collision-free case.  The direct
range is partitioned into an internal coordinate and an ordinary boundary.
The only remaining formal possibility is a unary distinguished component;
there equality of the current orders contradicts `r' < r`. -/
theorem noCollision_prefixAlphaCap_le
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  let g : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    have := i.pos
    omega⟩
  let Plarge := D.largeNoCollisionProfileWitness hlarge a
  let Psmall := D.smallNoCollisionProfileWitness hsmall b
  have hrange := D.lemma517Range_largeNoCollision_coordinate hlarge a i hi
  change (Plarge.indexEquiv g.castSucc).1 < D.largeSelectedPosition ∨
      ((Plarge.indexEquiv g.castSucc).1 = D.largeSelectedPosition ∧
        (Plarge.indexEquiv g.castSucc).2.val = 0) at hrange
  by_cases hinternal : (Plarge.indexEquiv g.castSucc).2.val + 1 <
      (D.largeNoCollisionJordan hlarge).componentRank
        (Plarge.indexEquiv g.castSucc).1
  · exact D.noCollision_prefixAlphaCap_le_of_internal
      hsmall hlarge hselected a b i hi hcurrent hinternal
  · have hlast : (Plarge.indexEquiv g.castSucc).2.val + 1 =
        (D.largeNoCollisionJordan hlarge).componentRank
          (Plarge.indexEquiv g.castSucc).1 := by
      have hlocalLt := (Plarge.indexEquiv g.castSucc).2.isLt
      change (Plarge.indexEquiv g.castSucc).2.val <
        (D.largeNoCollisionJordan hlarge).componentRank
          (Plarge.indexEquiv g.castSucc).1 at hlocalLt
      omega
    rcases hrange with hbefore | ⟨hposition, hlocal⟩
    · exact D.noCollision_prefixAlphaCap_le_of_boundary_before_selected
        hsmall hlarge hselected a b i hbefore hlast
    · have hRankOne :
          (D.largeNoCollisionJordan hlarge).componentRank
            (Plarge.indexEquiv g.castSucc).1 = 1 := by
        omega
      have hBlockRankOne :
          finrank K D.input.block.component.carrier = 1 := by
        change finrank K (D.largeAlmostJordan.component
          (Plarge.indexEquiv g.castSucc).1).carrier = 1 at hRankOne
        rw [hposition, D.largeAlmostJordan_finrank_selected] at hRankOne
        exact hRankOne
      have hcoordinates := D.noCollision_profile_coordinates_eq
        hsmall hlarge hselected a b g.castSucc
      have hsmallPosition :
          (Psmall.indexEquiv g.castSucc).1 = D.smallSelectedPosition := by
        calc
          (Psmall.indexEquiv g.castSucc).1 =
              (Plarge.indexEquiv g.castSucc).1 := hcoordinates.1.symm
          _ = D.largeSelectedPosition := hposition
          _ = D.smallSelectedPosition := hselected.symm
      have hcurrent' : a.order g.castSucc = b.order g.castSucc := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega)] at hcurrent
        have hraw :
            a.order ⟨i.val - 1, by have := i.lt_large; omega⟩ =
              b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
          simpa only [BONG.GoodBONG.orderSequence_at] using hcurrent
        let current : Fin (n + 1) :=
          ⟨i.val - 1, by have := i.lt_large; omega⟩
        have hindex : g.castSucc = current := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hraw
      have hlargeEffective :=
        D.largeSelected_effectiveNormOrder_eq_scale_of_rank_one hBlockRankOne
      have hsmallEffective :=
        D.smallSelected_effectiveNormOrder_eq_scale_of_rank_one hBlockRankOne
      change ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        g.castSucc).1 = D.largeSelectedPosition at hposition
      change ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv
        g.castSucc).1 = D.smallSelectedPosition at hsmallPosition
      rw [D.largeNoCollision_order_eq_localOrder hlarge a g.castSucc,
        D.smallNoCollision_order_eq_localOrder hsmall b g.castSucc] at hcurrent'
      simp only [hposition, hsmallPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected] at hcurrent'
      rw [hlargeEffective, hsmallEffective] at hcurrent'
      simp only [JordanProfileOrder.localOrder_of_proper] at hcurrent'
      exact False.elim
        ((ne_of_lt D.enlargedScaleOrder_lt_smallScaleOrder) hcurrent')

end Lattice.Beli2019Lemma51Data

end Bong
