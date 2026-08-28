/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveUnaryImproper

/-!
# Beli (2019), Section 5: alpha caps in the improper unary interval

This file converts the literal equality of the intermediate fundamental
lattices into the identities `R_i + alpha_i = A` and
`S_i + beta_i = A` used in case 4 following Lemma 5.13.  The proofs resolve
the possible equal-scale collision at an endpoint; the intermediate-scale
component itself is never merged.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Every internal boundary of the intermediate component on the large
side has weight equal to the weight of the common scale truncation.  This
is collision-safe even though that component lies after the selected unary
block. -/
theorem weakUnaryShift_largeCommon_weight_eq_order_add_alpha
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (j : Nat)
    (hj : j + 1 < finrank K
      (D.complementStrictWeak.component i₀).carrier) :
    let g : Fin (n + 1) := ⟨D.largeSelectedStart + (j + 1), by
      have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
      change D.largeSelectedStart +
          (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
        n + 2 at hbound
      omega⟩
    ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q M
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : Int) : ℚ) =
      (a.order g.castSucc : ℚ) + a.alphaValue g := by
  classical
  let g : Fin (n + 1) := ⟨D.largeSelectedStart + (j + 1), by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
      n + 2 at hbound
    omega⟩
  let I : Fin (n + 2) := g.castSucc
  let x := D.largeWeakProfileWitness a
  have hweak := D.weakUnaryShift_largeCommon_indexEquiv
    hfin i₀ hi₀ a j (by omega)
  have hweakI : x.indexEquiv I =
      ⟨D.smallSelectedPosition,
        ⟨j, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          omega⟩⟩ := by
    change (D.largeWeakProfileWitness a).indexEquiv
      ⟨D.largeSelectedStart + (j + 1), _⟩ = _
    exact hweak
  have hposition :=
    D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀
  have hweakComponent : (x.indexEquiv I).1 = D.smallSelectedPosition :=
    congrArg Sigma.fst hweakI
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
    have hstrict : StrictMono (fun z ↦ ordUnit K (S.scaleGenerator z)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.largeAlmostJordan k heq
          (D.largeOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness a.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (a.toBONG.beliLemma47_profile a.good (S.toJordan hstrict))
    have hafter : k.succ < (x.indexEquiv I).1 := by
      rw [hweakI, hk.2]
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      change D.largeSelectedPosition.val < D.smallSelectedPosition.val
      omega
    obtain ⟨p, hkp, hpOld, hpCoordinate, hpLocal⟩ :=
      x.strict_coordinates_of_after
        D.largeAlmostJordan_hasImproperEvenRank k heq hstrict P I hafter
    have hcomponent : S.component p =
        D.largeAlmostJordan.component D.smallSelectedPosition := by
      dsimp only [S]
      rw [D.largeAlmostJordan.mergeAdjacentAt_component_of_ne
        k heq p (Fin.ne_of_gt hkp), Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hlocal : (P.indexEquiv I).2.val = j := by
      rw [hpLocal]
      exact congrArg (fun z ↦ z.2.val) hweakI
    have hinternal : (P.indexEquiv I).2.val + 1 <
        (S.toJordan hstrict).componentRank (P.indexEquiv I).1 := by
      have hrank :
          (S.toJordan hstrict).componentRank (P.indexEquiv I).1 =
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        change finrank K (S.component (P.indexEquiv I).1).carrier = _
        rw [hpCoordinate, hcomponent,
          D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
      omega
    have hfundScale :
        (S.toJordan hstrict).fundamentalScaleOrder p =
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        show S.scaleGenerator p =
            (D.largeAlmostJordan.mergeAdjacentAt k heq).scaleGenerator p by rfl,
        Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator,
          Fin.succAbove_of_le_castSucc]
      · rw [hpOld, hweakComponent, ← hposition,
          D.largeAlmostJordan_scaleGenerator_common]
      · exact Fin.succ_le_castSucc_iff.mpr hkp
    have hweight := P.internal_weightOrder_eq_order_add_alpha g hinternal
    rw [hpCoordinate] at hweight
    change
      ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q M
          ((S.toJordan hstrict).fundamentalScaleOrder p)) : Int) : ℚ) =
        (a.order g.castSucc : ℚ) + a.alphaValue g at hweight
    simpa only [hfundScale] using hweight
  · let hstrict := D.largeAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.largeNoCollisionProfileWitness hcollision a
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    have hcomponent : (P.indexEquiv I).1 = D.smallSelectedPosition := by
      calc
        (P.indexEquiv I).1 = (x.indexEquiv I).1 :=
          congrArg Sigma.fst hcoordinates.symm
        _ = D.smallSelectedPosition := congrArg Sigma.fst hweakI
    have hlocal : (P.indexEquiv I).2.val = j := by
      calc
        (P.indexEquiv I).2.val = (x.indexEquiv I).2.val :=
          congrArg (fun z ↦ z.2.val) hcoordinates.symm
        _ = j := congrArg (fun z ↦ z.2.val) hweakI
    have hinternal : (P.indexEquiv I).2.val + 1 <
        (D.largeAlmostJordan.toJordan hstrict).componentRank
          (P.indexEquiv I).1 := by
      have hrank :
          (D.largeAlmostJordan.toJordan hstrict).componentRank
              (P.indexEquiv I).1 =
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        change finrank K (D.largeAlmostJordan.component
          (P.indexEquiv I).1).carrier = _
        rw [hcomponent,
          D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
      omega
    have hfundScale :
        (D.largeAlmostJordan.toJordan hstrict).fundamentalScaleOrder
            (P.indexEquiv I).1 =
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        hcomponent, ← hposition,
        D.largeAlmostJordan_scaleGenerator_common]
    have hweight := P.internal_weightOrder_eq_order_add_alpha g hinternal
    change
      ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q M
          ((D.largeAlmostJordan.toJordan hstrict).fundamentalScaleOrder
            (P.indexEquiv I).1)) : Int) : ℚ) =
        (a.order g.castSucc : ℚ) + a.alphaValue g at hweight
    simpa only [hfundScale] using hweight

/-- Every internal boundary of the intermediate component on the small
side has the same common fundamental weight. -/
theorem weakUnaryShift_smallCommon_weight_eq_order_add_alpha
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (j : Nat)
    (hj : j + 1 < finrank K
      (D.complementStrictWeak.component i₀).carrier) :
    let g : Fin (n + 1) := ⟨D.largeSelectedStart + j, by
      have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
      change D.largeSelectedStart +
          (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
        n + 2 at hbound
      omega⟩
    ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q N
          (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : Int) : ℚ) =
      (b.order g.castSucc : ℚ) + b.alphaValue g := by
  classical
  let g : Fin (n + 1) := ⟨D.largeSelectedStart + j, by
    have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
    change D.largeSelectedStart +
        (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤
      n + 2 at hbound
    omega⟩
  let I : Fin (n + 2) := g.castSucc
  let x := D.smallWeakProfileWitness b
  have hweak := D.weakUnaryShift_smallCommon_indexEquiv
    hfin i₀ hi₀ a b j (by omega)
  have hweakI : x.indexEquiv I =
      ⟨D.largeSelectedPosition,
        ⟨j, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          omega⟩⟩ := by
    change (D.smallWeakProfileWitness b).indexEquiv
      ⟨D.largeSelectedStart + j, _⟩ = _
    exact hweak
  have hweakComponent : (x.indexEquiv I).1 = D.largeSelectedPosition :=
    congrArg Sigma.fst hweakI
  have hposition :=
    D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
      hfin i₀ hi₀
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
    have hstrict : StrictMono (fun z ↦ ordUnit K (S.scaleGenerator z)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        D.smallAlmostJordan k heq
          (D.smallOnlyScaleCollisionAt c hscale k hk)
    let P : BONG.JordanOrderProfileWitness b.toBONG (S.toJordan hstrict) :=
      Classical.choice
        (b.toBONG.beliLemma47_profile b.good (S.toJordan hstrict))
    have hbefore : (x.indexEquiv I).1 < k.castSucc := by
      rw [hweakComponent, hk.1]
      have hadjacent :=
        D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
          hfin i₀ hi₀
      change D.largeSelectedPosition.val < D.smallSelectedPosition.val
      omega
    obtain ⟨p, hp, hpOld, hpCoordinate, hpLocal⟩ :=
      x.strict_coordinates_of_before
        D.smallAlmostJordan_hasImproperEvenRank k heq hstrict P I hbefore
    have hcomponent : S.component p =
        D.smallAlmostJordan.component D.largeSelectedPosition := by
      dsimp only [S]
      rw [D.smallAlmostJordan.mergeAdjacentAt_component_of_lt k heq p hp,
        hpOld, hweakComponent]
    have hlocal : (P.indexEquiv I).2.val = j := by
      rw [hpLocal]
      exact congrArg (fun z ↦ z.2.val) hweakI
    have hinternal : (P.indexEquiv I).2.val + 1 <
        (S.toJordan hstrict).componentRank (P.indexEquiv I).1 := by
      have hrank :
          (S.toJordan hstrict).componentRank (P.indexEquiv I).1 =
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        change finrank K (S.component (P.indexEquiv I).1).carrier = _
        rw [hpCoordinate, hcomponent,
          D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
      omega
    have hfundScale :
        (S.toJordan hstrict).fundamentalScaleOrder p =
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        show S.scaleGenerator p =
            (D.smallAlmostJordan.mergeAdjacentAt k heq).scaleGenerator p by rfl,
        Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleGenerator]
      have hskip : k.succ.succAbove p = p.castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        exact Fin.castSucc_lt_succ_iff.mpr hp.le
      rw [hskip, hpOld, hweakComponent, ← hposition,
        D.smallAlmostJordan_scaleGenerator_common]
    have hweight := P.internal_weightOrder_eq_order_add_alpha g hinternal
    rw [hpCoordinate] at hweight
    change
      ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q N
          ((S.toJordan hstrict).fundamentalScaleOrder p)) : Int) : ℚ) =
        (b.order g.castSucc : ℚ) + b.alphaValue g at hweight
    simpa only [hfundScale] using hweight
  · let hstrict := D.smallAlmostJordan_scaleOrder_strict_of_noCollision
      hcollision
    let P := D.smallNoCollisionProfileWitness hcollision b
    have hcoordinates := x.indexEquiv_eq_ofStrict hstrict P I
    have hcomponent : (P.indexEquiv I).1 = D.largeSelectedPosition := by
      calc
        (P.indexEquiv I).1 = (x.indexEquiv I).1 :=
          congrArg Sigma.fst hcoordinates.symm
        _ = D.largeSelectedPosition := hweakComponent
    have hlocal : (P.indexEquiv I).2.val = j := by
      calc
        (P.indexEquiv I).2.val = (x.indexEquiv I).2.val :=
          congrArg (fun z ↦ z.2.val) hcoordinates.symm
        _ = j := congrArg (fun z ↦ z.2.val) hweakI
    have hinternal : (P.indexEquiv I).2.val + 1 <
        (D.smallAlmostJordan.toJordan hstrict).componentRank
          (P.indexEquiv I).1 := by
      have hrank :
          (D.smallAlmostJordan.toJordan hstrict).componentRank
              (P.indexEquiv I).1 =
            finrank K (D.complementStrictWeak.component i₀).carrier := by
        change finrank K (D.smallAlmostJordan.component
          (P.indexEquiv I).1).carrier = _
        rw [hcomponent,
          D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
      omega
    have hfundScale :
        (D.smallAlmostJordan.toJordan hstrict).fundamentalScaleOrder
            (P.indexEquiv I).1 =
          ordUnit K (D.complementStrictWeak.scaleGenerator i₀) := by
      unfold Lattice.JordanDecomposition.fundamentalScaleOrder
      rw [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
        hcomponent, ← hposition,
        D.smallAlmostJordan_scaleGenerator_common]
    have hweight := P.internal_weightOrder_eq_order_add_alpha g hinternal
    change
      ((Lattice.weightIdealOrder q
        (Lattice.scaleTruncation q N
          ((D.smallAlmostJordan.toJordan hstrict).fundamentalScaleOrder
            (P.indexEquiv I).1)) : Int) : ℚ) =
        (b.order g.castSucc : ℚ) + b.alphaValue g at hweight
    simpa only [hfundScale] using hweight

/-! ## Alternating orders at the common component -/

/-- Even local coordinates of the improper intermediate component have the
high order, namely the original selected order. -/
theorem weakUnaryShift_largeCommon_order_of_even
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (j : Nat) (hj : j < finrank K
      (D.complementStrictWeak.component i₀).carrier)
    (heven : Even j) :
    a.orderSequence.entry (D.largeSelectedStart + (j + 1))
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart +
                (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
              at hbound
            omega) =
      ordUnit K D.input.block.scaleGenerator := by
  have hentry := D.weakUnaryShift_largeCommon_entry
    hfin i₀ hi₀ a j hj
  have hscaleLe : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
      D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by omega
  rw [JordanProfileOrder.localOrder_even_of_scale_le hscaleLe heven,
    heffective] at hentry
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  simpa only [largeSelectedStart] using hentry.trans (by omega)

/-- Odd local coordinates of the same component have the low order. -/
theorem weakUnaryShift_largeCommon_order_of_odd
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M n)
    (j : Nat) (hj : j < finrank K
      (D.complementStrictWeak.component i₀).carrier)
    (hodd : ¬Even j) :
    a.orderSequence.entry (D.largeSelectedStart + (j + 1))
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart +
                (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
              at hbound
            omega) =
      ordUnit K D.input.block.scaleGenerator - 2 := by
  have hentry := D.weakUnaryShift_largeCommon_entry
    hfin i₀ hi₀ a j hj
  have hscaleLe : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
      D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by omega
  rw [JordanProfileOrder.localOrder_odd_of_scale_le hscaleLe hodd,
    heffective] at hentry
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  simpa only [largeSelectedStart] using hentry.trans (by omega)

/-- The target common component has the same high order at even local
coordinates. -/
theorem weakUnaryShift_smallCommon_order_of_even
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (j : Nat) (hj : j < finrank K
      (D.complementStrictWeak.component i₀).carrier)
    (heven : Even j) :
    b.orderSequence.entry (D.largeSelectedStart + j)
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart +
                (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
              at hbound
            omega) =
      ordUnit K D.input.block.scaleGenerator := by
  have hentry := D.weakUnaryShift_smallCommon_entry
    hfin i₀ hi₀ a b j hj
  have hscaleLe : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
      D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by omega
  rw [JordanProfileOrder.localOrder_even_of_scale_le hscaleLe heven,
    heffective] at hentry
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  simpa only [largeSelectedStart] using hentry.trans (by omega)

/-- The target common component has the low order at odd local
coordinates. -/
theorem weakUnaryShift_smallCommon_order_of_odd
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (j : Nat) (hj : j < finrank K
      (D.complementStrictWeak.component i₀).carrier)
    (hodd : ¬Even j) :
    b.orderSequence.entry (D.largeSelectedStart + j)
        (by have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart +
                (finrank K (D.complementStrictWeak.component i₀).carrier + 1) ≤ n
              at hbound
            omega) =
      ordUnit K D.input.block.scaleGenerator - 2 := by
  have hentry := D.weakUnaryShift_smallCommon_entry
    hfin i₀ hi₀ a b j hj
  have hscaleLe : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) ≤
      D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) := by omega
  rw [JordanProfileOrder.localOrder_odd_of_scale_le hscaleLe hodd,
    heffective] at hentry
  have hselectedScale : ordUnit K D.input.block.enlargedScaleGenerator =
      ordUnit K D.input.block.scaleGenerator - 2 := by
    rcases D.input.block.componentRank_and_enlargedScaleOrder with
      hOne | hTwo
    · exact hOne.2
    · omega
  simpa only [largeSelectedStart] using hentry.trans (by omega)

/-! ## The common cap bound -/

/-- Case 4 following Lemma 5.13: throughout the improper unary exceptional
interval, the primary representation candidate is bounded by both current
alpha caps.  Odd boundaries use the next source alpha; even boundaries use
the previous target alpha.  Property P1 supplies the remaining current cap,
including both endpoints of the interval. -/
theorem weakUnaryShift_improper_commonBound
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (heffective : D.largeAlmostJordan.effectiveNormOrderAt
        (D.largeCommonPosition i₀)
        (ordUnit K (D.complementStrictWeak.scaleGenerator i₀)) =
      ordUnit K (D.complementStrictWeak.scaleGenerator i₀) + 1)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : D.largeSelectedStart < i.val)
    (hright : i.val ≤ D.largeSelectedStart +
      finrank K (D.complementStrictWeak.component i₀).carrier) :
    a.representationAlpha b i ≤
      min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val) := by
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let j := i.val - D.largeSelectedStart
  let current : Fin (n + 1) := BONG.GoodBONG.representationAlphaIndex i
  have hcurrentVal : current.val = i.val - 1 := rfl
  have hjpos : 0 < j := by dsimp only [j]; omega
  have hjle : j ≤ c := by dsimp only [j, c]; omega
  have hstartAddJ : D.largeSelectedStart + j = i.val := by
    dsimp only [j]
    exact Nat.add_sub_of_le hleft.le
  have hcEven :=
    D.unaryShift_intermediateRank_even_of_effective_eq_add_one i₀ heffective
  change Even c at hcEven
  have hweightEqInt :=
    D.unaryShift_intermediate_weightIdealOrder_eq hfin i₀ hi₀
  have hweightEq :
      (Lattice.weightIdealOrder q
          (Lattice.scaleTruncation q M
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) =
        (Lattice.weightIdealOrder q
          (Lattice.scaleTruncation q N
            (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) := by
    exact_mod_cast hweightEqInt
  by_cases hjEven : Even j
  · have hjTwo : 2 ≤ j := by
      rcases hjEven with ⟨z, hz⟩
      omega
    have hlocalEven : Even (j - 2) := by
      rcases hjEven with ⟨z, hz⟩
      refine ⟨z - 1, ?_⟩
      omega
    have hlocalOdd : ¬Even (j - 1) := by
      intro h
      rcases h with ⟨z, hz⟩
      rcases hjEven with ⟨w, hw⟩
      omega
    let previous : Fin (n + 1) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    have hpreviousVal : previous.val = i.val - 2 := rfl
    have hpreviousLe : previous ≤ current := by
      change i.val - 2 ≤ i.val - 1
      omega
    have hsourceWeightRaw :=
      D.weakUnaryShift_largeCommon_weight_eq_order_add_alpha
        hfin i₀ hi₀ a (j - 2) (by
          dsimp only [c] at hjle ⊢
          omega)
    have hsourceIndex :
        (⟨D.largeSelectedStart + ((j - 2) + 1), by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
          dsimp only [c] at hjle hbound ⊢
          omega⟩ : Fin (n + 1)) = current := by
      apply Fin.ext
      dsimp only [j, current, BONG.GoodBONG.representationAlphaIndex]
      omega
    have hsourceWeight :
        (Lattice.weightIdealOrder q
            (Lattice.scaleTruncation q M
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) =
          (a.order current.castSucc : ℚ) + a.alphaValue current := by
      dsimp only at hsourceWeightRaw
      rw [hsourceIndex] at hsourceWeightRaw
      exact hsourceWeightRaw
    have htargetWeightRaw :=
      D.weakUnaryShift_smallCommon_weight_eq_order_add_alpha
        hfin i₀ hi₀ a b (j - 2) (by
          dsimp only [c] at hjle ⊢
          omega)
    have htargetIndex :
        (⟨D.largeSelectedStart + (j - 2), by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
          dsimp only [c] at hjle hbound ⊢
          omega⟩ : Fin (n + 1)) = previous := by
      apply Fin.ext
      dsimp only [j, previous]
      omega
    have htargetWeight :
        (Lattice.weightIdealOrder q
            (Lattice.scaleTruncation q N
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) =
          (b.order previous.castSucc : ℚ) + b.alphaValue previous := by
      dsimp only at htargetWeightRaw
      rw [htargetIndex] at htargetWeightRaw
      exact htargetWeightRaw
    have hsourceHighRaw := D.weakUnaryShift_largeCommon_order_of_even
      hfin i₀ hi₀ heffective a (j - 2) (by
        dsimp only [c] at hjle ⊢
        omega) hlocalEven
    have hsourceHigh : a.order current.castSucc =
        ordUnit K D.input.block.scaleGenerator := by
      change a.order ⟨D.largeSelectedStart + ((j - 2) + 1), _⟩ = _
        at hsourceHighRaw
      exact (congrArg (fun z : Fin (n + 1) ↦ a.order z.castSucc)
        hsourceIndex.symm).trans hsourceHighRaw
    have htargetHighRaw := D.weakUnaryShift_smallCommon_order_of_even
      hfin i₀ hi₀ heffective a b (j - 2) (by
        dsimp only [c] at hjle ⊢
        omega) hlocalEven
    have htargetHigh : b.order previous.castSucc =
        ordUnit K D.input.block.scaleGenerator := by
      change b.order ⟨D.largeSelectedStart + (j - 2), _⟩ = _
        at htargetHighRaw
      exact (congrArg (fun z : Fin (n + 1) ↦ b.order z.castSucc)
        htargetIndex.symm).trans htargetHighRaw
    have hsourceLowRaw := D.weakUnaryShift_largeCommon_order_of_odd
      hfin i₀ hi₀ heffective a (j - 1) (by
        dsimp only [c] at hjle ⊢
        omega) hlocalOdd
    have hsourceAtI : a.order ⟨i.val, i.lt_large⟩ =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      have hidx :
          (⟨D.largeSelectedStart + ((j - 1) + 1), by
            have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
            dsimp only [c] at hjle hbound ⊢
            omega⟩ : Fin (n + 2)) = ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        dsimp only [j]
        omega
      change a.order ⟨D.largeSelectedStart + ((j - 1) + 1), _⟩ = _
        at hsourceLowRaw
      rw [hidx] at hsourceLowRaw
      exact hsourceLowRaw
    have htargetLowRaw := D.weakUnaryShift_smallCommon_order_of_odd
      hfin i₀ hi₀ heffective a b (j - 1) (by
        dsimp only [c] at hjle ⊢
        omega) hlocalOdd
    have htargetCurrent : b.order current.castSucc =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      have hidx :
          (⟨D.largeSelectedStart + (j - 1), by
            have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
            dsimp only [c] at hjle hbound ⊢
            omega⟩ : Fin (n + 2)) = current.castSucc := by
        apply Fin.ext
        change D.largeSelectedStart + (j - 1) = i.val - 1
        omega
      change b.order ⟨D.largeSelectedStart + (j - 1), _⟩ = _
        at htargetLowRaw
      rw [hidx] at htargetLowRaw
      exact htargetLowRaw
    have hcandidate :=
      a.representationAlphaValue_le_primary_previousAlpha b i (by omega)
    have hpreviousCandidate :
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
          previous := by apply Fin.ext; rfl
    have hcurrentOrderIndex :
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
          current.castSucc := by apply Fin.ext; rfl
    push_cast at hcandidate
    rw [hpreviousCandidate, hcurrentOrderIndex,
      hsourceAtI, htargetCurrent] at hcandidate
    have hrepPrevious : a.representationAlphaValue b i ≤
        b.alphaValue previous := by linarith
    have halphaEq : a.alphaValue current = b.alphaValue previous := by
      have hordersQ : (a.order current.castSucc : ℚ) =
          (b.order previous.castSucc : ℚ) := by
        exact_mod_cast hsourceHigh.trans htargetHigh.symm
      linarith [hweightEq, hsourceWeight, htargetWeight, hordersQ]
    have hendpoint := b.alphaLeftEndpoint_monotone hpreviousLe
    change (b.order previous.castSucc : ℚ) + b.alphaValue previous ≤
      (b.order current.castSucc : ℚ) + b.alphaValue current at hendpoint
    have hrepSource : a.representationAlphaValue b i ≤
        a.alphaValue current := by linarith
    have hrepTarget : a.representationAlphaValue b i ≤
        b.alphaValue current := by
      rw [htargetHigh, htargetCurrent] at hendpoint
      push_cast at hendpoint
      linarith
    rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
      b.prefixAlphaCap_of_internal i.pos i.lt_large,
      ← a.coe_representationAlphaValue b i]
    apply le_min
    · exact_mod_cast hrepSource
    · exact_mod_cast hrepTarget
  · have hjlt : j < c := by
      rcases hcEven with ⟨z, hz⟩
      by_contra hnot
      have hEq : j = c := by omega
      apply hjEven
      rw [hEq]
      exact ⟨z, hz⟩
    have hlocalEven : Even (j - 1) := by
      rcases Nat.not_even_iff_odd.mp hjEven with ⟨z, hz⟩
      exact ⟨z, by omega⟩
    have hnextLocalOdd : ¬Even j := hjEven
    have hnextBound : i.val < n + 1 := by
      have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
      change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
      omega
    let next : Fin (n + 1) := ⟨i.val, hnextBound⟩
    have hcurrentLe : current ≤ next := by
      change i.val - 1 ≤ i.val
      omega
    have hsourceWeightRaw :=
      D.weakUnaryShift_largeCommon_weight_eq_order_add_alpha
        hfin i₀ hi₀ a (j - 1) (by
          dsimp only [c] at hjlt ⊢
          omega)
    have hsourceIndex :
        (⟨D.largeSelectedStart + ((j - 1) + 1), by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
          dsimp only [c] at hjlt hbound ⊢
          omega⟩ : Fin (n + 1)) = next := by
      apply Fin.ext
      dsimp only [j, next]
      omega
    have hsourceWeight :
        (Lattice.weightIdealOrder q
            (Lattice.scaleTruncation q M
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) =
          (a.order next.castSucc : ℚ) + a.alphaValue next := by
      dsimp only at hsourceWeightRaw
      rw [hsourceIndex] at hsourceWeightRaw
      exact hsourceWeightRaw
    have htargetWeightRaw :=
      D.weakUnaryShift_smallCommon_weight_eq_order_add_alpha
        hfin i₀ hi₀ a b (j - 1) (by
          dsimp only [c] at hjlt ⊢
          omega)
    have htargetIndex :
        (⟨D.largeSelectedStart + (j - 1), by
          have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
          change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
          dsimp only [c] at hjlt hbound ⊢
          omega⟩ : Fin (n + 1)) = current := by
      apply Fin.ext
      dsimp only [j, current, BONG.GoodBONG.representationAlphaIndex]
      omega
    have htargetWeight :
        (Lattice.weightIdealOrder q
            (Lattice.scaleTruncation q N
              (ordUnit K (D.complementStrictWeak.scaleGenerator i₀))) : ℚ) =
          (b.order current.castSucc : ℚ) + b.alphaValue current := by
      dsimp only at htargetWeightRaw
      rw [htargetIndex] at htargetWeightRaw
      exact htargetWeightRaw
    have hsourceHighRaw := D.weakUnaryShift_largeCommon_order_of_even
      hfin i₀ hi₀ heffective a (j - 1) (by
        dsimp only [c] at hjlt ⊢
        omega) hlocalEven
    have hsourceHigh : a.order next.castSucc =
        ordUnit K D.input.block.scaleGenerator := by
      change a.order ⟨D.largeSelectedStart + ((j - 1) + 1), _⟩ = _
        at hsourceHighRaw
      exact (congrArg (fun z : Fin (n + 1) ↦ a.order z.castSucc)
        hsourceIndex.symm).trans hsourceHighRaw
    have htargetHighRaw := D.weakUnaryShift_smallCommon_order_of_even
      hfin i₀ hi₀ heffective a b (j - 1) (by
        dsimp only [c] at hjlt ⊢
        omega) hlocalEven
    have htargetHigh : b.order current.castSucc =
        ordUnit K D.input.block.scaleGenerator := by
      change b.order ⟨D.largeSelectedStart + (j - 1), _⟩ = _
        at htargetHighRaw
      exact (congrArg (fun z : Fin (n + 1) ↦ b.order z.castSucc)
        htargetIndex.symm).trans htargetHighRaw
    have hsourceLowRaw := D.weakUnaryShift_largeCommon_order_of_odd
      hfin i₀ hi₀ heffective a j (by
        dsimp only [c] at hjlt ⊢
        exact hjlt) hnextLocalOdd
    have hsourceAfter : a.order next.succ =
        ordUnit K D.input.block.scaleGenerator - 2 := by
      have hidx :
          (⟨D.largeSelectedStart + (j + 1), by
            have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
            change D.largeSelectedStart + (c + 1) ≤ n + 2 at hbound
            dsimp only [c] at hjlt hbound ⊢
            omega⟩ : Fin (n + 2)) = next.succ := by
        apply Fin.ext
        change D.largeSelectedStart + (j + 1) = i.val + 1
        omega
      change a.order ⟨D.largeSelectedStart + (j + 1), _⟩ = _
        at hsourceLowRaw
      rw [hidx] at hsourceLowRaw
      exact hsourceLowRaw
    have hsourceAtIIndex :
        (⟨i.val, i.lt_large⟩ : Fin (n + 2)) = next.castSucc := by
      apply Fin.ext
      rfl
    have htargetCurrentIndex :
        (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
          current.castSucc := by apply Fin.ext; rfl
    have hcandidate :=
      a.representationAlphaValue_le_primary_nextAlpha b i (by
        dsimp only [next] at hsourceAfter ⊢
        have := next.succ.isLt
        omega)
    have hnextCandidate :
        (⟨i.val, by omega⟩ : Fin (n + 1)) = next := by
      apply Fin.ext
      rfl
    push_cast at hcandidate
    rw [hsourceAtIIndex, htargetCurrentIndex, hnextCandidate,
      hsourceHigh, htargetHigh] at hcandidate
    have hrepNext : a.representationAlphaValue b i ≤
        a.alphaValue next := by linarith
    have halphaEq : a.alphaValue next = b.alphaValue current := by
      have hordersQ : (a.order next.castSucc : ℚ) =
          (b.order current.castSucc : ℚ) := by
        exact_mod_cast hsourceHigh.trans htargetHigh.symm
      linarith [hweightEq, hsourceWeight, htargetWeight, hordersQ]
    have hendpoint := a.alphaRightEndpoint_antitone hcurrentLe
    change -(a.order next.succ : ℚ) + a.alphaValue next ≤
      -(a.order current.succ : ℚ) + a.alphaValue current at hendpoint
    have hcurrentSucc : current.succ = next.castSucc := by
      apply Fin.ext
      change (i.val - 1) + 1 = i.val
      omega
    rw [hcurrentSucc, hsourceHigh, hsourceAfter] at hendpoint
    push_cast at hendpoint
    have hrepSource : a.representationAlphaValue b i ≤
        a.alphaValue current := by linarith
    have hrepTarget : a.representationAlphaValue b i ≤
        b.alphaValue current := by linarith
    rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
      b.prefixAlphaCap_of_internal i.pos i.lt_large,
      ← a.coe_representationAlphaValue b i]
    apply le_min
    · exact_mod_cast hrepSource
    · exact_mod_cast hrepTarget

end Lattice.Beli2019Lemma51Data

end Bong
