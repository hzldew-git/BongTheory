/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37ResolvedEndpointModels
import Bong.Bong.Beli2019SectionFiveCarrierGeometry

/-!
# Carrier identities for Beli (2019), Section 5 condition (iii)

The central representation proof compares adjacent approximation models.
This file records the carrier equalities through a collision-safe resolved
component.  They are consequences of the explicit merge construction, not
additional local laws.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace BONG.StrictCoordinateResolution

/-- If a strict coordinate resolution has zero offset and keeps the selected
weak component, then its block start and stop are exactly the weak-profile
component start and stop. -/
theorem coordinates_eq_weak_of_offset_zero_of_component_eq
    {m t : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (m + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (hoffset : R.localCoordinateOffset = 0)
    (hcomponent : R.strictWeak.component R.component =
      W.component (x.indexEquiv I).1) :
    R.coordinates.start = x.componentStart (x.indexEquiv I).1 ∧
      R.coordinates.stop = x.componentStop (x.indexEquiv I).1 := by
  have hstart := R.coordinates_start_add_offset_eq_weak_componentStart
  rw [hoffset, Nat.add_zero] at hstart
  refine ⟨hstart, ?_⟩
  have hrank := congrArg (fun C ↦ finrank K C.carrier) hcomponent
  change R.coordinates.start +
      finrank K (R.strictWeak.component R.component).carrier =
    x.componentStart (x.indexEquiv I).1 +
      finrank K (W.component (x.indexEquiv I).1).carrier
  rw [hstart, hrank]

/-- A penultimate resolved coordinate with another global coordinate after
its block cannot lie in the last strict Jordan component. -/
theorem component_succ_lt_of_penultimate
    {m t : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (m + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hafter : I.val + 2 < m + 2) :
    R.component.val + 1 < R.componentCount := by
  let z := BONG.WeakJordanOrderProfileWitness.ofStrict
    R.strictWeak R.scaleOrder_strict R.profile
  have hindex := R.index_val_eq_coordinates_start_add_local
  have hstrictPenultimate : (z.indexEquiv I).2.val + 2 =
      finrank K (R.strictWeak.component (z.indexEquiv I).1).carrier := by
    change (R.profile.indexEquiv I).2.val + 2 =
      finrank K (R.strictWeak.component R.component).carrier
    change I.val = R.coordinates.start +
      (R.profile.indexEquiv I).2.val at hindex
    change I.val + 2 = R.coordinates.start +
      finrank K (R.strictWeak.component R.component).carrier at hpenultimate
    omega
  have hlocalSucc : (z.indexEquiv I).2.val + 1 <
      finrank K (R.strictWeak.component (z.indexEquiv I).1).carrier := by
    omega
  let J : Fin (m + 2) := ⟨I.val + 1, by omega⟩
  have hnext := z.indexEquiv_global_succ_eq_local_succ
    I J (by rfl) hlocalSucc
  have hnextComponent : (z.indexEquiv J).1 = (z.indexEquiv I).1 := by
    simpa only using congrArg Sigma.fst hnext
  have hnextLocal : (z.indexEquiv J).2.val =
      (z.indexEquiv I).2.val + 1 := by
    simpa only [Fin.val_mk] using congrArg (fun p ↦ p.2.val) hnext
  have hlast : (z.indexEquiv J).2.val + 1 =
      finrank K (R.strictWeak.component (z.indexEquiv J).1).carrier := by
    have hrankEq := congrArg
      (fun p ↦ finrank K (R.strictWeak.component p).carrier)
      hnextComponent
    omega
  have hbound := z.component_succ_lt_of_terminal_with_global_succ
    J hlast (by
      dsimp only [J, Fin.val_mk]
      omega)
  change (z.indexEquiv I).1.val + 1 < R.componentCount
  have hcomponentVal := congrArg Fin.val hnextComponent
  omega

/-- If the resolved strict component has a successor, its half-open endpoint
is a genuine global coordinate and is therefore strictly below the BONG
length. -/
theorem coordinates_stop_lt_of_component_succ
    {m t : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (m + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (hnext : R.component.val + 1 < R.componentCount) :
    R.coordinates.stop < m + 2 := by
  classical
  let next : Fin R.componentCount :=
    ⟨R.component.val + 1, hnext⟩
  have hset : Finset.Iio next =
      insert R.component (Finset.Iio R.component) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change j.val < R.component.val + 1 ↔
      j = R.component ∨ j.val < R.component.val
    constructor
    · intro hj
      by_cases hlt : j.val < R.component.val
      · exact Or.inr hlt
      · left
        apply Fin.ext
        omega
    · rintro (rfl | hj) <;> omega
  have hfirstLt := (R.profile.profileComponentFirstIndex next).isLt
  rw [BONG.JordanOrderProfileWitness.profileComponentFirstIndex_val,
    hset, Finset.sum_insert (by simp)] at hfirstLt
  change (∑ j ∈ Finset.Iio R.component,
      R.jordan.componentRank j) + R.jordan.componentRank R.component <
    m + 2
  change R.jordan.componentRank R.component +
      (∑ j ∈ Finset.Iio R.component,
        R.jordan.componentRank j) < m + 2 at hfirstLt
  omega

/-- A positive global coordinate which is first in its resolved strict block
cannot belong to the first strict Jordan component. -/
theorem component_pos_of_first_of_positive
    {m t : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (m + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (hpositive : 0 < I.val)
    (hfirst : I.val = R.coordinates.start) :
    0 < R.component.val := by
  by_contra hnot
  have hcountPos : 0 < R.componentCount := by
    have := R.component.isLt
    omega
  let z : Fin R.componentCount := ⟨0, hcountPos⟩
  have hcomponentZero : R.component = z := by
    apply Fin.ext
    dsimp only [z, Fin.val_mk]
    exact Nat.eq_zero_of_not_pos hnot
  have hstartZero : R.coordinates.start = 0 := by
    unfold coordinates
    unfold BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    rw [hcomponentZero]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Iio] at hj
    change j.val < 0 at hj
    omega
  omega

/-- The vector-space rank of the strict prefix through the resolved
component is its global half-open endpoint. -/
theorem finrank_prefixCarrier_succ_eq_coordinates_stop
    {m t : Nat} {L : Lattice K V}
    {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    {I : Fin (m + 2)}
    (R : BONG.StrictCoordinateResolution a.toBONG W x I)
    (hnext : R.component.val + 1 < R.componentCount) :
    finrank K
        (R.jordan.toOrthogonalDecomposition.prefixCarrier
          (R.component.val + 1)) =
      R.coordinates.stop := by
  classical
  let next : Fin R.componentCount :=
    ⟨R.component.val + 1, hnext⟩
  have hset : Finset.Iio next = insert R.component (Finset.Iio R.component) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change (j.val < R.component.val + 1) ↔
      j = R.component ∨ j.val < R.component.val
    constructor
    · intro hj
      by_cases hlt : j.val < R.component.val
      · exact Or.inr hlt
      · left
        apply Fin.ext
        omega
    · rintro (rfl | hj) <;> omega
  have hfinrank :=
    R.jordan.toOrthogonalDecomposition.finrank_prefixCarrier_index next
  rw [show next.val = R.component.val + 1 by rfl] at hfinrank
  rw [hset, Finset.sum_insert (by simp)] at hfinrank
  change finrank K
      (R.jordan.toOrthogonalDecomposition.prefixCarrier
        (R.component.val + 1)) =
    (R.jordan.componentRank R.component +
      ∑ j ∈ Finset.Iio R.component, R.jordan.componentRank j) at hfinrank
  rw [hfinrank]
  change finrank K (R.strictWeak.component R.component).carrier +
      (∑ j ∈ Finset.Iio R.component,
        finrank K (R.strictWeak.component j).carrier) =
    (∑ j ∈ Finset.Iio R.component,
      finrank K (R.strictWeak.component j).carrier) +
      finrank K (R.strictWeak.component R.component).carrier
  exact Nat.add_comm _ _

end BONG.StrictCoordinateResolution

namespace Lattice.Beli2019Lemma51Data

/-- Strictly before the selected component, the small-side collision
resolution leaves the current weak component unchanged.  Its only possible
merge starts at the selected component. -/
theorem smallStrictCoordinateResolution_component_eq_of_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (b : BONG.GoodBONG q N n) (I : Fin n)
    (hle : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition)
    (hlt : ((D.smallWeakProfileWitness b).indexEquiv I).1 <
      D.smallSelectedPosition) :
    let R := D.smallStrictCoordinateResolution b I hle
    R.strictWeak.component R.component =
      D.smallAlmostJordan.component
        ((D.smallWeakProfileWitness b).indexEquiv I).1 := by
  classical
  let x := D.smallWeakProfileWitness b
  by_cases hcollision : D.SmallScaleCollision
  · unfold smallStrictCoordinateResolution
    rw [dif_pos hcollision]
    have hcollision' := hcollision
    change (∃ i : Fin D.complementComponentCount,
      ordUnit K D.input.block.scaleGenerator =
        ordUnit K (D.complementStrictWeak.scaleGenerator i)) at hcollision'
    let c := Classical.choose hcollision'
    have hscale := Classical.choose_spec hcollision'
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
    have hbefore : (x.indexEquiv I).1 < k.castSucc := by
      rw [hk.1]
      exact hlt
    rw [dif_pos hbefore]
    have hcoordinates := x.strict_coordinates_of_before
      D.smallAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
    let p := Classical.choose hcoordinates
    have hp := (Classical.choose_spec hcoordinates).1
    have hpOld := (Classical.choose_spec hcoordinates).2.1
    have hpCoordinate := (Classical.choose_spec hcoordinates).2.2.1
    change S.component (P.indexEquiv I).1 =
      D.smallAlmostJordan.component (x.indexEquiv I).1
    rw [hpCoordinate,
      D.smallAlmostJordan.mergeAdjacentAt_component_of_ne
        k heq p (Fin.ne_of_lt hp)]
    have hskip : k.succ.succAbove p = p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hp.le
    rw [hskip, hpOld]
  · unfold smallStrictCoordinateResolution
    rw [dif_neg hcollision]
    let hstrict := D.smallAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.smallNoCollisionProfileWitness hcollision b
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    change D.smallAlmostJordan.component (P.indexEquiv I).1 =
      D.smallAlmostJordan.component (x.indexEquiv I).1
    rw [congrArg Sigma.fst hcoordinates]
    rfl

/-- Strictly before the selected component, and away from the left member
of the unique large-side collision, the large resolution likewise leaves
the current weak component unchanged. -/
theorem largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition)
    (hlt : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv I).1 =
          D.largeCommonPosition c) :
    let R := D.largeStrictCoordinateResolution a I hle
    R.strictWeak.component R.component =
      D.largeAlmostJordan.component
        ((D.largeWeakProfileWitness a).indexEquiv I).1 := by
  classical
  let x := D.largeWeakProfileWitness a
  by_cases hcollision : D.LargeScaleCollision
  · unfold largeStrictCoordinateResolution
    rw [dif_pos hcollision]
    let c := Classical.choose hcollision
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
    have hbefore : (x.indexEquiv I).1 < k.castSucc := by
      have hlt' := hlt
      change (x.indexEquiv I).1 < D.largeSelectedPosition at hlt'
      rw [← hk.2] at hlt'
      have hleLeft : (x.indexEquiv I).1 ≤ k.castSucc := by
        change (x.indexEquiv I).1.val ≤ k.val
        change (x.indexEquiv I).1.val < k.val + 1 at hlt'
        omega
      exact lt_of_le_of_ne hleLeft (by
        intro heqPosition
        apply hnotCollisionLeft
        exact ⟨c, hscale, heqPosition.trans hk.1⟩)
    rw [dif_pos hbefore]
    have hcoordinates := x.strict_coordinates_of_before
      D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
    let p := Classical.choose hcoordinates
    have hp := (Classical.choose_spec hcoordinates).1
    have hpOld := (Classical.choose_spec hcoordinates).2.1
    have hpCoordinate := (Classical.choose_spec hcoordinates).2.2.1
    change S.component (P.indexEquiv I).1 =
      D.largeAlmostJordan.component (x.indexEquiv I).1
    rw [hpCoordinate,
      D.largeAlmostJordan.mergeAdjacentAt_component_of_ne
        k heq p (Fin.ne_of_lt hp)]
    have hskip : k.succ.succAbove p = p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hp.le
    rw [hskip, hpOld]
  · unfold largeStrictCoordinateResolution
    rw [dif_neg hcollision]
    let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    change D.largeAlmostJordan.component (P.indexEquiv I).1 =
      D.largeAlmostJordan.component (x.indexEquiv I).1
    rw [congrArg Sigma.fst hcoordinates]
    rfl

/-- Before the selected component, and away from the left member of the
large-side collision, the resolved strict component has a successor. -/
theorem largeStrictCoordinateResolution_component_succ_lt_of_lt_of_notCollisionLeft
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition)
    (hlt : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv I).1 =
          D.largeCommonPosition c) :
    let R := D.largeStrictCoordinateResolution a I hle
    R.component.val + 1 < R.componentCount := by
  classical
  let x := D.largeWeakProfileWitness a
  by_cases hcollision : D.LargeScaleCollision
  · unfold largeStrictCoordinateResolution
    rw [dif_pos hcollision]
    let c := Classical.choose hcollision
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
    have hbefore : (x.indexEquiv I).1 < k.castSucc := by
      have hlt' := hlt
      change (x.indexEquiv I).1 < D.largeSelectedPosition at hlt'
      rw [← hk.2] at hlt'
      have hleLeft : (x.indexEquiv I).1 ≤ k.castSucc := by
        change (x.indexEquiv I).1.val ≤ k.val
        change (x.indexEquiv I).1.val < k.val + 1 at hlt'
        omega
      exact lt_of_le_of_ne hleLeft (by
        intro heqPosition
        apply hnotCollisionLeft
        exact ⟨c, hscale, heqPosition.trans hk.1⟩)
    rw [dif_pos hbefore]
    have hcoordinates := x.strict_coordinates_of_before
      D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
    let p := Classical.choose hcoordinates
    have hp := (Classical.choose_spec hcoordinates).1
    have hpCoordinate := (Classical.choose_spec hcoordinates).2.2.1
    change (P.indexEquiv I).1.val + 1 < D.complementComponentCount
    rw [congrArg Fin.val hpCoordinate]
    have hpVal : p.val < k.val := hp
    have hkLt := k.isLt
    omega
  · unfold largeStrictCoordinateResolution
    rw [dif_neg hcollision]
    let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    change (P.indexEquiv I).1.val + 1 < D.complementComponentCount + 1
    have hcomponentVal := congrArg Fin.val (congrArg Sigma.fst hcoordinates)
    have hlt' := hlt
    change (x.indexEquiv I).1.val < D.largeSelectedPosition.val at hlt'
    have hselectedLt := D.largeSelectedPosition.isLt
    omega

/-- Consequently the strict small-side prefix through a component before
the selected one has exactly the original weak prefix carrier. -/
theorem smallStrictCoordinateResolution_prefixCarrier_succ_eq_of_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (b : BONG.GoodBONG q N n) (I : Fin n)
    (hle : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition)
    (hlt : ((D.smallWeakProfileWitness b).indexEquiv I).1 <
      D.smallSelectedPosition) :
    let R := D.smallStrictCoordinateResolution b I hle
    R.jordan.toOrthogonalDecomposition.prefixCarrier
        (R.component.val + 1) =
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
        (((D.smallWeakProfileWitness b).indexEquiv I).1.val + 1) := by
  dsimp only
  let R := D.smallStrictCoordinateResolution b I hle
  exact R.prefixCarrier_succ_eq_weakPrefix_succ_of_offset_zero_of_component_eq
    (D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero b I hle)
    (D.smallStrictCoordinateResolution_component_eq_of_lt b I hle hlt)

/-- A penultimate coordinate in the strict small-side resolution remains
penultimate in the original weak component.  Hence its next global
coordinate is the terminal coordinate of that same weak component. -/
theorem smallWeak_globalSucc_terminal_of_strictPenultimate
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {m : Nat} (b : BONG.GoodBONG q N (m + 2))
    (I J : Fin (m + 2))
    (hle : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition)
    (hlt : ((D.smallWeakProfileWitness b).indexEquiv I).1 <
      D.smallSelectedPosition)
    (hsucc : J.val = I.val + 1)
    (hpenultimate :
      let R := D.smallStrictCoordinateResolution b I hle
      I.val + 2 = R.coordinates.stop) :
    ((D.smallWeakProfileWitness b).indexEquiv J).1 =
        ((D.smallWeakProfileWitness b).indexEquiv I).1 ∧
      ((D.smallWeakProfileWitness b).indexEquiv J).2.val + 1 =
        finrank K (D.smallAlmostJordan.component
          ((D.smallWeakProfileWitness b).indexEquiv J).1).carrier := by
  classical
  let y := D.smallWeakProfileWitness b
  let R := D.smallStrictCoordinateResolution b I hle
  change I.val + 2 = R.coordinates.stop at hpenultimate
  have hindex := R.index_val_eq_coordinates_start_add_local
  have hstrictPenultimate : (R.profile.indexEquiv I).2.val + 2 =
      finrank K (R.strictWeak.component R.component).carrier := by
    change I.val = R.coordinates.start +
      (R.profile.indexEquiv I).2.val at hindex
    change I.val + 2 = R.coordinates.start +
      finrank K (R.strictWeak.component R.component).carrier at hpenultimate
    omega
  have hoffset : R.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero b I hle
  have hcomponent :=
    D.smallStrictCoordinateResolution_component_eq_of_lt b I hle hlt
  have hlocal := R.localCoordinate_eq
  rw [hoffset, Nat.zero_add] at hlocal
  have hlocal' : (R.profile.indexEquiv I).2.val =
      (y.indexEquiv I).2.val := by
    simpa only [y] using hlocal
  have hrankComponent :
      finrank K (R.strictWeak.component R.component).carrier =
        finrank K (D.smallAlmostJordan.component
          (y.indexEquiv I).1).carrier :=
    congrArg (fun C ↦ finrank K C.carrier) hcomponent
  have hweakPenultimate : (y.indexEquiv I).2.val + 2 =
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv I).1).carrier := by
    omega
  have hlocalSucc : (y.indexEquiv I).2.val + 1 <
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv I).1).carrier := by
    omega
  have hnext := y.indexEquiv_global_succ_eq_local_succ
    I J hsucc hlocalSucc
  have hnextComponent : (y.indexEquiv J).1 =
      (y.indexEquiv I).1 := by
    simpa only using congrArg Sigma.fst hnext
  have hnextLocal : (y.indexEquiv J).2.val =
      (y.indexEquiv I).2.val + 1 := by
    simpa only [Fin.val_mk] using congrArg (fun z ↦ z.2.val) hnext
  constructor
  · exact hnextComponent
  · change (y.indexEquiv J).2.val + 1 =
      finrank K (D.smallAlmostJordan.component
        (y.indexEquiv J).1).carrier
    have hrankEq := congrArg
      (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
      hnextComponent
    omega

end Lattice.Beli2019Lemma51Data

end Bong
