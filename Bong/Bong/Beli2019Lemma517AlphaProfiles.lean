/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma516Weights
import Bong.Bong.Beli2019Lemma513Profiles

/-!
# Jordan-profile proof of Beli (2019), Lemma 5.17(i)

This file compares the alpha invariants at the equal-order coordinates in
the direct Lemma 5.17 range.  It first treats strict, collision-free Jordan
families.  The possible equal-scale amalgamation is handled after the strict
calculation, using the canonical split coordinates of weak profiles.
-/

namespace Bong

open Dyadic Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

@[simp]
theorem largeNoCollisionJordan_fundamentalScaleOrder
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    (p : Fin (D.complementComponentCount + 1)) :
    (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder p =
      ordUnit K (D.largeAlmostJordan.scaleGenerator p) := by
  unfold Lattice.JordanDecomposition.fundamentalScaleOrder
  unfold largeNoCollisionJordan
  rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]

@[simp]
theorem smallNoCollisionJordan_fundamentalScaleOrder
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (p : Fin (D.complementComponentCount + 1)) :
    (D.smallNoCollisionJordan hsmall).fundamentalScaleOrder p =
      ordUnit K (D.smallAlmostJordan.scaleGenerator p) := by
  unfold Lattice.JordanDecomposition.fundamentalScaleOrder
  unfold smallNoCollisionJordan
  rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]

/-- In the no-collision case the uniform weak profile and the strict
large-side profile have the same coordinates.  This follows from uniqueness
of the increasing enumeration, independently of the classical choices used
to construct the two witnesses. -/
theorem largeWeak_noCollision_coordinates_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision) {n : Nat}
    (a : BONG.GoodBONG q M n) (i : Fin n) :
    ((D.largeWeakProfileWitness a).indexEquiv i).1 =
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 ∧
      ((D.largeWeakProfileWitness a).indexEquiv i).2.val =
        ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val := by
  let z := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.largeAlmostJordan
    (D.largeAlmostJordan_scaleOrder_strict_of_noCollision hlarge)
    (D.largeNoCollisionProfileWitness hlarge a)
  have h := (D.largeWeakProfileWitness a).indexEquiv_coordinates_eq_of_componentRank_eq
    z rfl i
  change ((D.largeWeakProfileWitness a).indexEquiv i).1 =
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).1 ∧
    ((D.largeWeakProfileWitness a).indexEquiv i).2.val =
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv i).2.val at h
  exact h

/-- Small-side analogue of `largeWeak_noCollision_coordinates_eq`. -/
theorem smallWeak_noCollision_coordinates_eq
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision) {n : Nat}
    (b : BONG.GoodBONG q N n) (i : Fin n) :
    ((D.smallWeakProfileWitness b).indexEquiv i).1 =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1 ∧
      ((D.smallWeakProfileWitness b).indexEquiv i).2.val =
        ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val := by
  let z := BONG.WeakJordanOrderProfileWitness.ofStrict
    D.smallAlmostJordan
    (D.smallAlmostJordan_scaleOrder_strict_of_noCollision hsmall)
    (D.smallNoCollisionProfileWitness hsmall b)
  have h := (D.smallWeakProfileWitness b).indexEquiv_coordinates_eq_of_componentRank_eq
    z rfl i
  change ((D.smallWeakProfileWitness b).indexEquiv i).1 =
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).1 ∧
    ((D.smallWeakProfileWitness b).indexEquiv i).2.val =
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv i).2.val at h
  exact h

/-- The Lemma 5.17 range dichotomy transported from the uniform weak
profile to the strict no-collision profile. -/
theorem lemma517Range_largeNoCollision_coordinate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hlarge : ¬D.LargeScaleCollision)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i) :
    let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
    let x := D.largeNoCollisionProfileWitness hlarge a
    (x.indexEquiv I).1 < D.largeSelectedPosition ∨
      ((x.indexEquiv I).1 = D.largeSelectedPosition ∧
        (x.indexEquiv I).2.val = 0) := by
  let I : Fin n := ⟨i.val - 1, by have := i.lt_large; omega⟩
  have hweak := D.lemma517Range_large_coordinate a i hi
  have hcoordinates := D.largeWeak_noCollision_coordinates_eq hlarge a I
  rcases hweak with hbefore | ⟨hposition, hlocal⟩
  · rw [hcoordinates.1] at hbefore
    exact Or.inl hbefore
  · rw [hcoordinates.1] at hposition
    rw [hcoordinates.2] at hlocal
    exact Or.inr ⟨hposition, hlocal⟩

/-- On the Lemma 5.17 range, the strict large-side fundamental scale is no
larger than the corresponding small-side scale and is at most the enlarged
selected scale.  Before the selected component the two scales are equal;
at the selected component this is exactly `r' < r`. -/
theorem noCollision_fundamentalScale_interval
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (b : BONG.GoodBONG q N n) (I : Fin n)
    (hrange :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 <
          D.largeSelectedPosition ∨
        (((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1 =
            D.largeSelectedPosition ∧
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).2.val = 0)) :
    let pLarge :=
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1
    let pSmall :=
      ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).1
    (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder pLarge ≤
        (D.smallNoCollisionJordan hsmall).fundamentalScaleOrder pSmall ∧
      (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder pLarge ≤
        ordUnit K D.input.block.enlargedScaleGenerator := by
  let pLarge :=
    ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv I).1
  let pSmall :=
    ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).1
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have hpositions : pLarge = pSmall := hcoordinates.1
  rcases hrange with hbefore | ⟨hposition, _hlocal⟩
  · have hscaleEq := D.weakAligned_scaleOrder_eq_before_selected
      hselected pLarge hbefore
    have hboundRaw := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    have hbound :
        ordUnit K (D.largeAlmostJordan.scaleGenerator pLarge) ≤
          ordUnit K D.input.block.enlargedScaleGenerator := by
      simpa only [D.largeAlmostJordan_scaleGenerator_selected] using hboundRaw
    constructor
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        D.smallNoCollisionJordan_fundamentalScaleOrder]
      rw [← hcoordinates.1]
      exact hscaleEq.le
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder]
      exact hbound
  · have hsmallPosition : pSmall = D.smallSelectedPosition := by
      calc
        pSmall = pLarge := hpositions.symm
        _ = D.largeSelectedPosition := hposition
        _ = D.smallSelectedPosition := hselected.symm
    constructor
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        D.smallNoCollisionJordan_fundamentalScaleOrder,
        hposition]
      change ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv I).1 =
        D.smallSelectedPosition at hsmallPosition
      rw [hsmallPosition,
        D.largeAlmostJordan_scaleGenerator_selected,
        D.smallAlmostJordan_scaleGenerator_selected]
      exact D.enlargedScaleOrder_lt_smallScaleOrder.le
    · rw [D.largeNoCollisionJordan_fundamentalScaleOrder,
        hposition, D.largeAlmostJordan_scaleGenerator_selected]

/-- Lemma 5.17(i) at an internal coordinate of two aligned,
collision-free Jordan profiles. -/
theorem noCollision_prefixAlphaCap_le_of_internal
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
      b.orderSequence.entryOrZero (i.val - 1))
    (hlargeInternal :
      let g : Fin n := ⟨i.val - 1, by
        have := i.lt_large
        have := i.pos
        omega⟩
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv g.castSucc).2.val + 1 <
        (D.largeNoCollisionJordan hlarge).componentRank
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv g.castSucc).1) :
    a.prefixAlphaCap i.val ≤ b.prefixAlphaCap i.val := by
  let g : Fin n := ⟨i.val - 1, by
    have := i.lt_large
    have := i.pos
    omega⟩
  let Plarge := D.largeNoCollisionProfileWitness hlarge a
  let Psmall := D.smallNoCollisionProfileWitness hsmall b
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b g.castSucc
  have hsmallInternal :
      (Psmall.indexEquiv g.castSucc).2.val + 1 <
        (D.smallNoCollisionJordan hsmall).componentRank
          (Psmall.indexEquiv g.castSucc).1 := by
    have hrank := congrFun
      (D.noCollision_componentRank_eq hsmall hlarge hselected)
      (Plarge.indexEquiv g.castSucc).1
    change (D.largeNoCollisionJordan hlarge).componentRank
        (Plarge.indexEquiv g.castSucc).1 =
      (D.smallNoCollisionJordan hsmall).componentRank
        (Plarge.indexEquiv g.castSucc).1 at hrank
    change (Plarge.indexEquiv g.castSucc).1 =
        (Psmall.indexEquiv g.castSucc).1 ∧
      (Plarge.indexEquiv g.castSucc).2.val =
        (Psmall.indexEquiv g.castSucc).2.val at hcoordinates
    have hrank' :
        (D.largeNoCollisionJordan hlarge).componentRank
            (Plarge.indexEquiv g.castSucc).1 =
          (D.smallNoCollisionJordan hsmall).componentRank
            (Psmall.indexEquiv g.castSucc).1 := by
      calc
        (D.largeNoCollisionJordan hlarge).componentRank
            (Plarge.indexEquiv g.castSucc).1 =
          (D.smallNoCollisionJordan hsmall).componentRank
            (Plarge.indexEquiv g.castSucc).1 := hrank
        _ = (D.smallNoCollisionJordan hsmall).componentRank
            (Psmall.indexEquiv g.castSucc).1 :=
          congrArg (D.smallNoCollisionJordan hsmall).componentRank
            hcoordinates.1
    calc
      (Psmall.indexEquiv g.castSucc).2.val + 1 =
          (Plarge.indexEquiv g.castSucc).2.val + 1 := by
        omega
      _ < (D.largeNoCollisionJordan hlarge).componentRank
          (Plarge.indexEquiv g.castSucc).1 := hlargeInternal
      _ = (D.smallNoCollisionJordan hsmall).componentRank
          (Psmall.indexEquiv g.castSucc).1 := hrank'
  have hrange := D.lemma517Range_largeNoCollision_coordinate hlarge a i hi
  change (Plarge.indexEquiv g.castSucc).1 < D.largeSelectedPosition ∨
      ((Plarge.indexEquiv g.castSucc).1 = D.largeSelectedPosition ∧
        (Plarge.indexEquiv g.castSucc).2.val = 0) at hrange
  have hscales := D.noCollision_fundamentalScale_interval
    hsmall hlarge hselected a b g.castSucc hrange
  change
    (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder
          (Plarge.indexEquiv g.castSucc).1 ≤
        (D.smallNoCollisionJordan hsmall).fundamentalScaleOrder
          (Psmall.indexEquiv g.castSucc).1 ∧
      (D.largeNoCollisionJordan hlarge).fundamentalScaleOrder
          (Plarge.indexEquiv g.castSucc).1 ≤
        ordUnit K D.input.block.enlargedScaleGenerator at hscales
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
  have halpha := D.alphaValue_le_of_internal_coordinates
    a b Psmall Plarge g hsmallInternal hlargeInternal
      hscales.1 hscales.2 hcurrent'
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large]
  have halphaTop : (a.alphaValue g : WithTop ℚ) ≤
      (b.alphaValue g : WithTop ℚ) := by
    exact_mod_cast halpha
  simpa only [g] using halphaTop

end Lattice.Beli2019Lemma51Data

end Bong
