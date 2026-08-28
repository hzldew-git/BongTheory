/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517Complete

/-!
# Corollary 5.10 triggers after Beli (2019), Lemma 5.17

This file derives the `nextOrder` alternative of Corollary 5.10 directly
from the weak almost-Jordan profiles.  If the current coordinate has a local
successor in an aligned common component, equality of the current orders
forces equality of the two effective norm orders, and hence equality of the
next orders.  The only cases left after this lemma are genuine component
boundaries and the first coordinate of the selected binary component.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Inside a common component before aligned selected components, equality
of one pair of corresponding local orders forces equality at the next local
coordinate. -/
theorem weakAligned_nextOrder_eq_of_current_eq_of_local_succ
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv I).1).carrier)
    (hcurrent : a.order I = b.order I) :
    a.orderSequence.entryOrZero (I.val + 1) =
      b.orderSequence.entryOrZero (I.val + 1) := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let sourcePosition := (x.indexEquiv I).1
  let targetPosition := (y.indexEquiv I).1
  let sourceLocal := (x.indexEquiv I).2.val
  let targetLocal := (y.indexEquiv I).2.val
  let sourceScale :=
    ordUnit K (D.largeAlmostJordan.scaleGenerator sourcePosition)
  let targetScale :=
    ordUnit K (D.smallAlmostJordan.scaleGenerator targetPosition)
  let sourceEffective :=
    D.largeAlmostJordan.effectiveNormOrderAt sourcePosition sourceScale
  let targetEffective :=
    D.smallAlmostJordan.effectiveNormOrderAt targetPosition targetScale
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hposition : sourcePosition = targetPosition := hcoordinates.1
  have hlocal : sourceLocal = targetLocal := hcoordinates.2
  have hscale : sourceScale = targetScale := by
    dsimp only [sourceScale, targetScale, sourcePosition, targetPosition]
    rw [← hcoordinates.1]
    exact D.weakAligned_scaleOrder_eq_before_selected hselected
      ((D.largeWeakProfileWitness a).indexEquiv I).1 hbefore
  have hsourceScaleLe : sourceScale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt
      sourcePosition sourceScale
  have htargetScaleLe : targetScale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt
      targetPosition targetScale
  have htargetScaleLe' : sourceScale ≤ targetEffective := by
    rw [hscale]
    exact htargetScaleLe
  have hsourceCurrent : a.order I =
      JordanProfileOrder.localOrder sourceScale sourceEffective
        sourceLocal := by
    simpa only [sourceScale, sourceEffective, sourcePosition, sourceLocal]
      using D.largeWeak_order_eq_localOrder a I
  have htargetCurrent : b.order I =
      JordanProfileOrder.localOrder targetScale targetEffective
        targetLocal := by
    simpa only [targetScale, targetEffective, targetPosition, targetLocal]
      using D.smallWeak_order_eq_localOrder b I
  have hlocalOrder :
      JordanProfileOrder.localOrder sourceScale sourceEffective sourceLocal =
        JordanProfileOrder.localOrder sourceScale targetEffective
          sourceLocal := by
    calc
      _ = a.order I := hsourceCurrent.symm
      _ = b.order I := hcurrent
      _ = JordanProfileOrder.localOrder targetScale targetEffective
          targetLocal := htargetCurrent
      _ = JordanProfileOrder.localOrder sourceScale targetEffective
          sourceLocal := by rw [hscale, hlocal]
  have heffective : sourceEffective = targetEffective :=
    JordanProfileOrder.effective_eq_of_localOrder_eq
      hsourceScaleLe htargetScaleLe' hlocalOrder
  have hranks := congrFun (D.almostJordan_componentRank_eq hselected)
    sourcePosition
  have htargetRank :
      finrank K (D.smallAlmostJordan.component targetPosition).carrier =
        finrank K (D.largeAlmostJordan.component sourcePosition).carrier := by
    rw [← hposition, ← hranks]
  have hlocalNextSmall : targetLocal + 1 <
      finrank K
        (D.smallAlmostJordan.component targetPosition).carrier := by
    have hlarge : sourceLocal + 1 <
        finrank K
          (D.largeAlmostJordan.component sourcePosition).carrier := by
      simpa only [sourceLocal, sourcePosition] using hlocalNext
    omega
  have hiNext : I.val + 1 < n := x.global_succ_lt_of_local_succ I hlocalNext
  have hsourceNext :=
    x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hiNext hlocalNext
  have htargetNext :=
    y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
      I hiNext (by
        simpa only [targetLocal, targetPosition] using hlocalNextSmall)
  simp only [BONG.weakJordanExpectedOrder] at hsourceNext htargetNext
  change a.order ⟨I.val + 1, hiNext⟩ =
      JordanProfileOrder.localOrder sourceScale sourceEffective
        (sourceLocal + 1) at hsourceNext
  change b.order ⟨I.val + 1, hiNext⟩ =
      JordanProfileOrder.localOrder targetScale targetEffective
        (targetLocal + 1) at htargetNext
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hiNext,
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence hiNext]
  change a.order ⟨I.val + 1, hiNext⟩ =
    b.order ⟨I.val + 1, hiNext⟩
  calc
    _ = JordanProfileOrder.localOrder sourceScale sourceEffective
        (sourceLocal + 1) := hsourceNext
    _ = JordanProfileOrder.localOrder targetScale targetEffective
        (targetLocal + 1) := by rw [hscale, heffective, hlocal]
    _ = _ := htargetNext.symm

/-- The preceding theorem supplies the `nextOrder` alternative of Corollary
5.10 at the next prefix length. -/
theorem weakAligned_prefixExtensionTrigger_of_current_eq_of_local_succ
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition)
    (hlocalNext :
      ((D.largeWeakProfileWitness a).indexEquiv I).2.val + 1 <
        finrank K (D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv I).1).carrier)
    (hcurrent : a.order I = b.order I) :
    BeliPrefixExtensionTrigger (ramificationIndex K : Int)
      a.orderSequence b.orderSequence (I.val + 1) := by
  let x := D.largeWeakProfileWitness a
  have hiNext : I.val + 1 < n := x.global_succ_lt_of_local_succ I hlocalNext
  exact BeliPrefixExtensionTrigger.nextOrder hiNext hiNext
    (D.weakAligned_nextOrder_eq_of_current_eq_of_local_succ
      hselected a b I hbefore hlocalNext hcurrent)

end Lattice.Beli2019Lemma51Data

end Bong
