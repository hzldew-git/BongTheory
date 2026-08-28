/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37BoundaryModels
import Bong.Bong.Beli2019SectionFiveCarrierGeometry
import Bong.Bong.Beli2019SectionFiveRepresentationRange
import Bong.Bong.Beli2019SectionFiveUnaryImproper

/-!
# Beli (2019), Section 5: the direct part of condition 2.1(iv)

This file carries out the direct-range calculation in Section 5.15.  The
first lemma isolates the two strict coordinate inequalities forced by the
long trigger.  The remaining lemmas classify those inequalities on the
aligned and adjacent-unary almost-Jordan profiles and realize the surviving
endpoint by nested Lemma 3.7(i) models.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The numerical antecedent in condition 2.1(iv) forces the two strict
comparisons `R_i < S_i` and `R_(i+1) < S_(i+1)` used in Beli's proof.
The Lean indices are zero-based, so these are the coordinates `i-1` and
`i` below. -/
theorem sectionFiveLongTrigger_pair_strict
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : sectionFiveLongTrigger a b i) :
    a.order ⟨i.val - 1, by
        have := i.one_lt
        have := i.succ_lt_large
        omega⟩ <
        b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ ∧
      a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ <
        b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
  have hi : i.val ≤ n + 1 := by
    have := i.succ_lt_large
    omega
  unfold sectionFiveLongTrigger at htrigger
  simp only [dif_pos hi] at htrigger
  rcases htrigger with ⟨houter, hjump, hinner⟩
  let g : Fin n := ⟨i.val - 1, by
    have := i.one_lt
    have := i.succ_lt_large
    omega⟩
  have hsourceGap := a.orderGap_ge_neg_two_mul_e_for_properties g
  have htargetGap := b.orderGap_ge_neg_two_mul_e_for_properties g
  have hsucc : g.succ =
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (n + 1)) := by
    have hiOne := i.one_lt
    apply Fin.ext
    dsimp only [g, Fin.succ, Fin.val_mk]
    omega
  have hcast : g.castSucc =
      (⟨i.val - 1, by
        have := i.one_lt
        have := i.succ_lt_large
        omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  change -(2 * (ramificationIndex K : Int)) ≤
    a.order g.succ - a.order g.castSucc at hsourceGap
  change -(2 * (ramificationIndex K : Int)) ≤
    b.order g.succ - b.order g.castSucc at htargetGap
  rw [hsucc, hcast] at hsourceGap htargetGap
  have hsourceStep :
      a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ ≤
        a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
          2 * (ramificationIndex K : Int) := by
    omega
  have htargetStep :
      b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ ≤
        b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
          2 * (ramificationIndex K : Int) := by
    omega
  constructor <;> omega

end BONG.GoodBONG

namespace BONG.WeakJordanOrderProfileWitness

variable {L H : Lattice K V} {t : Nat}
  {W : Lattice.WeakJordanDecomposition q L t}
  {T : Lattice.WeakJordanDecomposition q H t}

/-- If two consecutive global coordinates cross to a component whose local
coordinate is zero, then the first coordinate is terminal in a strictly
earlier component. -/
theorem terminal_and_component_lt_of_global_succ_local_zero
    {r : Nat} {c : BONG V q L r}
    {S : Lattice.WeakJordanDecomposition q L t}
    (x : BONG.WeakJordanOrderProfileWitness c S)
    (I J : Fin r) (hsucc : J.val = I.val + 1)
    (hzero : (x.indexEquiv J).2.val = 0) :
    (x.indexEquiv I).1 < (x.indexEquiv J).1 ∧
      (x.indexEquiv I).2.val + 1 =
        finrank K (S.component (x.indexEquiv I).1).carrier := by
  have hIJ : I < J := by
    change I.val < J.val
    omega
  have hlex := (x.order_iff I J).mp hIJ
  change Sigma.Lex (fun i j : Fin t ↦ i < j)
    (fun _ i j ↦ i < j) (x.indexEquiv I) (x.indexEquiv J) at hlex
  rw [Sigma.lex_iff] at hlex
  have hcomponent : (x.indexEquiv I).1 < (x.indexEquiv J).1 := by
    rcases hlex with hcomponent | ⟨hcomponents, hlocal⟩
    · exact hcomponent
    · have htransport := eqRec_heq
        (φ := fun p ↦ Fin (finrank K (S.component p).carrier))
        hcomponents (x.indexEquiv I).2
      have htransportVal := Fin.val_eq_val_of_heq htransport
      have hlocalCastVal :
          (Eq.recOn (motive := fun p _ ↦
              Fin (finrank K (S.component p).carrier))
            hcomponents (x.indexEquiv I).2).val <
            (x.indexEquiv J).2.val := by
        exact hlocal
      omega
  refine ⟨hcomponent, ?_⟩
  by_contra hnot
  have hlocalSucc : (x.indexEquiv I).2.val + 1 <
      finrank K (S.component (x.indexEquiv I).1).carrier := by
    have hbound := (x.indexEquiv I).2.isLt
    omega
  let localSucc : Fin
      (finrank K (S.component (x.indexEquiv I).1).carrier) :=
    ⟨(x.indexEquiv I).2.val + 1, hlocalSucc⟩
  let nextGlobal := x.indexEquiv.symm
    ⟨(x.indexEquiv I).1, localSucc⟩
  have hnextVal := x.inverse_index_val_local_succ
    (x.indexEquiv I).1 (x.indexEquiv I).2 hlocalSucc
  have hcurrent : x.indexEquiv.symm (x.indexEquiv I) = I :=
    x.indexEquiv.symm_apply_apply I
  have hnextEq : nextGlobal = J := by
    apply Fin.ext
    dsimp only [nextGlobal, localSucc, Fin.val_mk]
    rw [hnextVal, hcurrent, hsucc]
  have hcomponentsEq := congrArg (fun z ↦ (x.indexEquiv z).1) hnextEq
  have hnextComponent : (x.indexEquiv nextGlobal).1 =
      (x.indexEquiv I).1 := by
    dsimp only [nextGlobal]
    rw [x.indexEquiv.apply_symm_apply]
  exact hcomponent.ne (hnextComponent.symm.trans hcomponentsEq)

/-- A terminal coordinate which still has a global successor cannot lie in
the last weak Jordan component. -/
theorem component_succ_lt_of_terminal_of_global_succ
    {r : Nat} {c : BONG V q L r}
    {S : Lattice.WeakJordanDecomposition q L t}
    (x : BONG.WeakJordanOrderProfileWitness c S)
    (I : Fin r)
    (hlast : (x.indexEquiv I).2.val + 1 =
      finrank K (S.component (x.indexEquiv I).1).carrier)
    (hsucc : I.val + 1 < r) :
    (x.indexEquiv I).1.val + 1 < t := by
  let J : Fin r := ⟨I.val + 1, hsucc⟩
  have hIJ : I < J := by
    change I.val < I.val + 1
    omega
  have hlex := (x.order_iff I J).mp hIJ
  change Sigma.Lex (fun i j : Fin t ↦ i < j)
    (fun _ i j ↦ i < j) (x.indexEquiv I) (x.indexEquiv J) at hlex
  rw [Sigma.lex_iff] at hlex
  have hcomponent : (x.indexEquiv I).1 < (x.indexEquiv J).1 := by
    rcases hlex with hcomponent | ⟨hcomponents, hlocal⟩
    · exact hcomponent
    · have htransport := eqRec_heq
        (φ := fun p ↦ Fin (finrank K (S.component p).carrier))
        hcomponents (x.indexEquiv I).2
      have htransportVal := Fin.val_eq_val_of_heq htransport
      have hlocalCastVal :
          (Eq.recOn (motive := fun p _ ↦
              Fin (finrank K (S.component p).carrier))
            hcomponents (x.indexEquiv I).2).val <
            (x.indexEquiv J).2.val := by
        exact hlocal
      have htargetBound := (x.indexEquiv J).2.isLt
      have hrankEq := congrArg
        (fun p ↦ finrank K (S.component p).carrier) hcomponents
      omega
  have htargetBound := (x.indexEquiv J).1.isLt
  change (x.indexEquiv I).1.val < (x.indexEquiv J).1.val at hcomponent
  omega

/-- Exact weak-profile coordinates at the numerical start of a component. -/
theorem indexEquiv_eq_component_zero_of_val_eq_start
    {r : Nat} {c : BONG V q L r}
    {S : Lattice.WeakJordanDecomposition q L t}
    (x : BONG.WeakJordanOrderProfileWitness c S)
    (I : Fin r) (p : Fin t)
    (hval : I.val =
      ∑ k ∈ Finset.Iio p, finrank K (S.component k).carrier) :
    x.indexEquiv I =
      ⟨p, ⟨0, S.component_finrank_pos p⟩⟩ := by
  let zero : Fin (finrank K (S.component p).carrier) :=
    ⟨0, S.component_finrank_pos p⟩
  have hinverse := x.inverse_index_val p zero
  have hglobal : x.indexEquiv.symm ⟨p, zero⟩ = I := by
    apply Fin.ext
    dsimp only [zero, Fin.val_mk] at hinverse ⊢
    omega
  calc
    x.indexEquiv I = x.indexEquiv (x.indexEquiv.symm ⟨p, zero⟩) := by
      rw [hglobal]
    _ = ⟨p, zero⟩ := x.indexEquiv.apply_symm_apply ⟨p, zero⟩

/-- Exact weak-profile coordinates at an arbitrary local offset from the
numerical start of a component. -/
theorem indexEquiv_eq_component_local_of_val_eq_start_add
    {r : Nat} {c : BONG V q L r}
    {S : Lattice.WeakJordanDecomposition q L t}
    (x : BONG.WeakJordanOrderProfileWitness c S)
    (I : Fin r) (p : Fin t)
    (j : Fin (finrank K (S.component p).carrier))
    (hval : I.val =
      (∑ k ∈ Finset.Iio p, finrank K (S.component k).carrier) + j.val) :
    x.indexEquiv I = ⟨p, j⟩ := by
  have hinverse := x.inverse_index_val p j
  have hglobal : x.indexEquiv.symm ⟨p, j⟩ = I := by
    apply Fin.ext
    omega
  calc
    x.indexEquiv I = x.indexEquiv (x.indexEquiv.symm ⟨p, j⟩) := by
      rw [hglobal]
    _ = ⟨p, j⟩ := x.indexEquiv.apply_symm_apply ⟨p, j⟩

/-- A profile-level form of the parity obstruction used in Section 5.15.
It applies whenever two weak Jordan profiles have the same current
component/local coordinate, equal component ranks and scales, and the
source effective norm order is no larger than the target one. -/
theorem reverse_order_at_current_or_next
    (a : BONG.GoodBONG q L n) (b : BONG.GoodBONG q H n)
    (x : BONG.WeakJordanOrderProfileWitness a.toBONG W)
    (y : BONG.WeakJordanOrderProfileWitness b.toBONG T)
    (hW : W.HasImproperEvenRank) (hT : T.HasImproperEvenRank)
    (I : Fin n) (hiNext : I.val + 1 < n)
    (hcoordinates : (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
      (x.indexEquiv I).2.val = (y.indexEquiv I).2.val)
    (hrank : finrank K (W.component (x.indexEquiv I).1).carrier =
      finrank K (T.component (x.indexEquiv I).1).carrier)
    (hscale : ordUnit K (W.scaleGenerator (x.indexEquiv I).1) =
      ordUnit K (T.scaleGenerator (x.indexEquiv I).1))
    (heffective : W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) ≤
      T.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (T.scaleGenerator (x.indexEquiv I).1))) :
    b.order I ≤ a.order I ∨
      b.order ⟨I.val + 1, hiNext⟩ ≤
        a.order ⟨I.val + 1, hiNext⟩ := by
  let p := (x.indexEquiv I).1
  let j := (x.indexEquiv I).2.val
  let sourceScale := ordUnit K (W.scaleGenerator p)
  let targetScale := ordUnit K (T.scaleGenerator p)
  let sourceEffective := W.effectiveNormOrderAt p sourceScale
  let targetEffective := T.effectiveNormOrderAt p targetScale
  have hsourceScale : sourceScale ≤ sourceEffective :=
    W.targetScale_le_effectiveNormOrderAt p sourceScale
  have htargetScale : targetScale ≤ targetEffective :=
    T.targetScale_le_effectiveNormOrderAt p targetScale
  have hsourceCurrent : a.order I =
      JordanProfileOrder.localOrder sourceScale sourceEffective j := by
    simpa only [p, j, sourceScale, sourceEffective,
      BONG.weakJordanExpectedOrder, BONG.GoodBONG.order] using x.order_eq I
  have htargetCurrent : b.order I =
      JordanProfileOrder.localOrder targetScale targetEffective j := by
    have h := y.order_eq I
    simp only [BONG.weakJordanExpectedOrder] at h
    rw [← hcoordinates.2, ← hcoordinates.1] at h
    simpa only [p, j, targetScale, targetEffective,
      BONG.GoodBONG.order] using h
  by_cases heven : Even j
  · by_cases hlocalNext : j + 1 < finrank K (W.component p).carrier
    · right
      have htargetRank :
          finrank K (T.component (y.indexEquiv I).1).carrier =
            finrank K (W.component p).carrier := by
        calc
          _ = finrank K (T.component p).carrier := by
            rw [← hcoordinates.1]
          _ = _ := hrank.symm
      have htargetLocalNext : (y.indexEquiv I).2.val + 1 <
          finrank K (T.component (y.indexEquiv I).1).carrier := by
        change (x.indexEquiv I).2.val + 1 <
          finrank K (W.component p).carrier at hlocalNext
        omega
      have hsourceNext :=
        x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
          I hiNext hlocalNext
      have htargetNext :=
        y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
          I hiNext htargetLocalNext
      simp only [BONG.weakJordanExpectedOrder] at hsourceNext htargetNext
      have hsourceNext' : a.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder sourceScale sourceEffective
            (j + 1) := by
        change a.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder
            (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))
            (W.effectiveNormOrderAt (x.indexEquiv I).1
              (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)))
            ((x.indexEquiv I).2.val + 1) at hsourceNext
        simpa only [p, j, sourceScale, sourceEffective] using hsourceNext
      have htargetNext' : b.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder targetScale targetEffective
            (j + 1) := by
        change b.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder
            (ordUnit K (T.scaleGenerator (y.indexEquiv I).1))
            (T.effectiveNormOrderAt (y.indexEquiv I).1
              (ordUnit K (T.scaleGenerator (y.indexEquiv I).1)))
            ((y.indexEquiv I).2.val + 1) at htargetNext
        rw [← hcoordinates.2, ← hcoordinates.1] at htargetNext
        simpa only [p, j, targetScale, targetEffective] using htargetNext
      have hoddNext : ¬Even (j + 1) := by
        intro h
        exact (Nat.even_add_one.mp h) heven
      rw [hsourceNext', htargetNext',
        JordanProfileOrder.localOrder_odd_of_scale_le
          hsourceScale hoddNext,
        JordanProfileOrder.localOrder_odd_of_scale_le
          htargetScale hoddNext]
      change sourceScale = targetScale at hscale
      change sourceEffective ≤ targetEffective at heffective
      omega
    · left
      have hbound := (x.indexEquiv I).2.isLt
      have hlast : j + 1 = finrank K (W.component p).carrier := by
        change j < finrank K (W.component p).carrier at hbound
        omega
      have hrankPos := W.component_finrank_pos p
      have hjLast : j = finrank K (W.component p).carrier - 1 := by
        omega
      have hsourceLast := hW.localOrder_last W p
      have htargetLast := hT.localOrder_last T p
      change JordanProfileOrder.localOrder sourceScale sourceEffective
          (finrank K (W.component p).carrier - 1) =
        2 * sourceScale - sourceEffective at hsourceLast
      change JordanProfileOrder.localOrder targetScale targetEffective
          (finrank K (T.component p).carrier - 1) =
        2 * targetScale - targetEffective at htargetLast
      rw [hsourceCurrent, htargetCurrent, hjLast, hsourceLast,
        hrank, htargetLast]
      change sourceScale = targetScale at hscale
      change sourceEffective ≤ targetEffective at heffective
      omega
  · left
    rw [hsourceCurrent, htargetCurrent,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale heven,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale heven]
    change sourceScale = targetScale at hscale
    change sourceEffective ≤ targetEffective at heffective
    omega

end BONG.WeakJordanOrderProfileWitness

namespace Lattice.Beli2019Lemma51Data

/-- Before aligned selected components, one of two consecutive coordinates
compares in the direction opposite to the two strict inequalities forced by
condition (iv).  At an internal coordinate this is the odd member of the
alternating modular block; at a component endpoint it follows from the
improper-even-rank invariant and `localOrder_last`. -/
theorem weakAligned_reverse_order_at_current_or_next_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n) (hiNext : I.val + 1 < n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    b.order I ≤ a.order I ∨
      b.order ⟨I.val + 1, hiNext⟩ ≤
        a.order ⟨I.val + 1, hiNext⟩ := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let j := (x.indexEquiv I).2.val
  let sourceScale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let targetScale := ordUnit K (D.smallAlmostJordan.scaleGenerator p)
  let sourceEffective :=
    D.largeAlmostJordan.effectiveNormOrderAt p sourceScale
  let targetEffective :=
    D.smallAlmostJordan.effectiveNormOrderAt p targetScale
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hscale : sourceScale = targetScale := by
    exact D.weakAligned_scaleOrder_eq_before_selected hselected p hbefore
  have heffective : sourceEffective ≤ targetEffective := by
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : sourceScale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p sourceScale
  have htargetScale : targetScale ≤ targetEffective :=
    D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt p targetScale
  have hsourceCurrent : a.order I =
      JordanProfileOrder.localOrder sourceScale sourceEffective j := by
    simpa only [x, p, j, sourceScale, sourceEffective] using
      D.largeWeak_order_eq_localOrder a I
  have htargetCurrent : b.order I =
      JordanProfileOrder.localOrder targetScale targetEffective j := by
    have h := D.smallWeak_order_eq_localOrder b I
    change b.order I = JordanProfileOrder.localOrder
      (ordUnit K (D.smallAlmostJordan.scaleGenerator
        ((D.smallWeakProfileWitness b).indexEquiv I).1))
      (D.smallAlmostJordan.effectiveNormOrderAt
        ((D.smallWeakProfileWitness b).indexEquiv I).1
        (ordUnit K (D.smallAlmostJordan.scaleGenerator
          ((D.smallWeakProfileWitness b).indexEquiv I).1)))
      ((D.smallWeakProfileWitness b).indexEquiv I).2.val at h
    rw [← hcoordinates.2, ← hcoordinates.1] at h
    simpa only [x, p, j, targetScale, targetEffective] using h
  by_cases heven : Even j
  · by_cases hlocalNext : j + 1 <
        finrank K (D.largeAlmostJordan.component p).carrier
    · right
      have htargetLocalNext :
          ((y.indexEquiv I).2.val + 1 <
            finrank K (D.smallAlmostJordan.component
              (y.indexEquiv I).1).carrier) := by
        have hrank := congrFun (D.almostJordan_componentRank_eq hselected) p
        change finrank K (D.largeAlmostJordan.component p).carrier =
          finrank K (D.smallAlmostJordan.component p).carrier at hrank
        change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
          (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
        change j + 1 <
          finrank K (D.largeAlmostJordan.component p).carrier at hlocalNext
        have htargetRank :
            finrank K (D.smallAlmostJordan.component
              (y.indexEquiv I).1).carrier =
              finrank K (D.largeAlmostJordan.component p).carrier := by
          calc
            _ = finrank K (D.smallAlmostJordan.component p).carrier := by
              rw [← hcoordinates.1]
            _ = _ := hrank.symm
        have hlocalEq : (x.indexEquiv I).2.val =
            (y.indexEquiv I).2.val := hcoordinates.2
        change (x.indexEquiv I).2.val + 1 <
          finrank K (D.largeAlmostJordan.component p).carrier at hlocalNext
        omega
      have hsourceNext :=
        x.order_succ_eq_weakJordanExpectedOrder_of_local_succ
          I hiNext hlocalNext
      have htargetNext :=
        y.order_succ_eq_weakJordanExpectedOrder_of_local_succ
          I hiNext htargetLocalNext
      simp only [BONG.weakJordanExpectedOrder] at hsourceNext htargetNext
      have hsourceNext' : a.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder sourceScale sourceEffective
            (j + 1) := by
        change a.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder
            (ordUnit K (D.largeAlmostJordan.scaleGenerator
              (x.indexEquiv I).1))
            (D.largeAlmostJordan.effectiveNormOrderAt
              (x.indexEquiv I).1
              (ordUnit K (D.largeAlmostJordan.scaleGenerator
                (x.indexEquiv I).1)))
            ((x.indexEquiv I).2.val + 1) at hsourceNext
        simpa only [p, j, sourceScale, sourceEffective] using hsourceNext
      have htargetNext' : b.order ⟨I.val + 1, hiNext⟩ =
          JordanProfileOrder.localOrder targetScale targetEffective
            (j + 1) := by
        change b.order ⟨I.val + 1, hiNext⟩ = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator
            (y.indexEquiv I).1))
          (D.smallAlmostJordan.effectiveNormOrderAt
            (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator
              (y.indexEquiv I).1)))
          ((y.indexEquiv I).2.val + 1) at htargetNext
        change (x.indexEquiv I).1 = (y.indexEquiv I).1 ∧
          (x.indexEquiv I).2.val = (y.indexEquiv I).2.val at hcoordinates
        rw [← hcoordinates.2, ← hcoordinates.1] at htargetNext
        simpa only [x, p, j, targetScale, targetEffective] using htargetNext
      have hoddNext : ¬Even (j + 1) := by
        intro h
        exact (Nat.even_add_one.mp h) heven
      rw [hsourceNext', htargetNext',
        JordanProfileOrder.localOrder_odd_of_scale_le
          hsourceScale hoddNext,
        JordanProfileOrder.localOrder_odd_of_scale_le
          htargetScale hoddNext]
      omega
    · left
      have hbound := (x.indexEquiv I).2.isLt
      have hlast : j + 1 =
          finrank K (D.largeAlmostJordan.component p).carrier := by
        change j <
          finrank K (D.largeAlmostJordan.component p).carrier at hbound
        omega
      have hrankPos := D.largeAlmostJordan.component_finrank_pos p
      have hjLast : j =
          finrank K (D.largeAlmostJordan.component p).carrier - 1 := by
        omega
      have hsourceLast :=
        WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
          D.largeAlmostJordan D.largeAlmostJordan_hasImproperEvenRank p
      have htargetLast :=
        WeakJordanDecomposition.HasImproperEvenRank.localOrder_last
          D.smallAlmostJordan D.smallAlmostJordan_hasImproperEvenRank p
      have hrank := congrFun (D.almostJordan_componentRank_eq hselected) p
      change JordanProfileOrder.localOrder sourceScale sourceEffective
          (finrank K (D.largeAlmostJordan.component p).carrier - 1) =
        2 * sourceScale - sourceEffective at hsourceLast
      change JordanProfileOrder.localOrder targetScale targetEffective
          (finrank K (D.smallAlmostJordan.component p).carrier - 1) =
        2 * targetScale - targetEffective at htargetLast
      rw [hsourceCurrent, htargetCurrent, hjLast, hsourceLast,
        hrank, htargetLast]
      omega
  · left
    rw [hsourceCurrent, htargetCurrent,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale heven,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale heven]
    omega

/-- The same parity obstruction before the exceptional interval in the
adjacent-unary profile. -/
theorem weakUnaryShift_reverse_order_at_current_or_next_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (I : Fin n) (hiNext : I.val + 1 < n)
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    b.order I ≤ a.order I ∨
      b.order ⟨I.val + 1, hiNext⟩ ≤
        a.order ⟨I.val + 1, hiNext⟩ := by
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  apply x.reverse_order_at_current_or_next a b y
    D.largeAlmostJordan_hasImproperEvenRank
    D.smallAlmostJordan_hasImproperEvenRank I hiNext
  · exact D.weakUnaryShift_profile_coordinates_eq_before
      hfin i₀ hi₀ a b I hbefore
  · exact D.weakUnaryShift_componentRank_eq_before
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  · exact D.weakUnaryShift_scaleOrder_eq_before_selected
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore
  · exact D.weakUnaryShift_effectiveNormOrderAt_le_before_selected
      hfin i₀ hi₀ (x.indexEquiv I).1 hbefore

/-- Inside the adjacent-unary exceptional interval, two consecutive strict
coordinate inequalities occur only when the intermediate common component
is unary and the first coordinate of the interval is used.  This is the
explicit sequence calculation in the last paragraph of Section 5.15. -/
theorem weakUnaryShift_pair_strict_interval_endpoint
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hleft : D.largeSelectedStart < i.val)
    (hright : i.val ≤ D.largeSelectedStart +
      finrank K (D.complementStrictWeak.component i₀).carrier)
    (hstrict :
      a.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ <
        b.order ⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ ∧
      a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ <
        b.order ⟨i.val, by have := i.succ_lt_large; omega⟩) :
    finrank K (D.complementStrictWeak.component i₀).carrier = 1 ∧
      i.val = D.largeSelectedStart + 1 := by
  let start := D.largeSelectedStart
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  let j := i.val - start
  let scale := ordUnit K (D.complementStrictWeak.scaleGenerator i₀)
  let effective := D.largeAlmostJordan.effectiveNormOrderAt
    (D.largeCommonPosition i₀) scale
  have hc : 0 < c := D.complementStrictWeak.component_finrank_pos i₀
  have hjPos : 0 < j := by
    dsimp only [j, start]
    omega
  have hjLe : j ≤ c := by
    dsimp only [j, start, c] at hright ⊢
    omega
  have hstartAddJ : start + j = i.val := by
    dsimp only [j, start]
    omega
  have hbound := D.weakUnaryShift_interval_bound hfin i₀ hi₀ a
  change start + (c + 1) ≤ n + 1 at hbound
  have hlargeCommon (k : Nat) (hk : k < c) :
      a.order ⟨start + (k + 1), by omega⟩ =
        JordanProfileOrder.localOrder scale effective k := by
    have h := D.weakUnaryShift_largeCommon_entry hfin i₀ hi₀ a k
      (by simpa only [c] using hk)
    simpa only [BONG.GoodBONG.orderSequence_at, start, c, scale,
      effective, largeSelectedStart] using h
  have hsmallCommon (k : Nat) (hk : k < c) :
      b.order ⟨start + k, by omega⟩ =
        JordanProfileOrder.localOrder scale effective k := by
    have h := D.weakUnaryShift_smallCommon_entry hfin i₀ hi₀ a b k
      (by simpa only [c] using hk)
    simpa only [BONG.GoodBONG.orderSequence_at, start, c, scale,
      effective, largeSelectedStart] using h
  rcases D.unaryShift_commonEffectiveNormOrder_cases hfin i₀ hi₀ with
    hproper | himproper
  · change effective = scale at hproper
    by_cases hjOne : j = 1
    · by_cases hcOne : c = 1
      · exact ⟨hcOne, by dsimp only [j, start] at hjOne; omega⟩
      · have hcTwo : 1 < c := by omega
        have hs := hlargeCommon 0 (by omega)
        have ht := hsmallCommon 1 hcTwo
        have hsourceIndex :
            (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (n + 1)) =
              ⟨start + (0 + 1), by omega⟩ := by
          apply Fin.ext
          change i.val = start + (0 + 1)
          omega
        have htargetIndex :
            (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (n + 1)) =
              ⟨start + 1, by omega⟩ := by
          apply Fin.ext
          change i.val = start + 1
          omega
        have hsAt :
            a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
              JordanProfileOrder.localOrder scale effective 0 := by
          rw [hsourceIndex]
          exact hs
        have htAt :
            b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
              JordanProfileOrder.localOrder scale effective 1 := by
          rw [htargetIndex]
          exact ht
        have hsecond := hstrict.2
        rw [hsAt, htAt, hproper,
          JordanProfileOrder.localOrder_of_proper,
          JordanProfileOrder.localOrder_of_proper] at hsecond
        exact (lt_irrefl _ hsecond).elim
    · have hjTwo : 2 ≤ j := by omega
      have hs := hlargeCommon (j - 2) (by omega)
      have ht := hsmallCommon (j - 1) (by omega)
      have hsourceIndex :
          (⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ : Fin (n + 1)) =
            ⟨start + ((j - 2) + 1), by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = start + ((j - 2) + 1)
        omega
      have htargetIndex :
          (⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ : Fin (n + 1)) =
            ⟨start + (j - 1), by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = start + (j - 1)
        omega
      have hsAt :
          a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ =
            JordanProfileOrder.localOrder scale effective (j - 2) := by
        rw [hsourceIndex]
        exact hs
      have htAt :
          b.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ =
            JordanProfileOrder.localOrder scale effective (j - 1) := by
        rw [htargetIndex]
        exact ht
      have hfirst := hstrict.1
      rw [hsAt, htAt, hproper,
        JordanProfileOrder.localOrder_of_proper,
        JordanProfileOrder.localOrder_of_proper] at hfirst
      exact (lt_irrefl _ hfirst).elim
  · change effective = scale + 1 at himproper
    have hcEven :=
      D.unaryShift_intermediateRank_even_of_effective_eq_add_one i₀
        himproper
    change Even c at hcEven
    by_cases hjEven : Even j
    · rcases hjEven with ⟨m, hm⟩
      have hjTwo : 2 ≤ j := by
        have hmPos : 0 < m := by omega
        omega
      have hsourceEven : Even (j - 2) := ⟨m - 1, by omega⟩
      have htargetOdd : ¬Even (j - 1) := by
        intro h
        rcases h with ⟨l, hl⟩
        omega
      have hs := hlargeCommon (j - 2) (by omega)
      have ht := hsmallCommon (j - 1) (by omega)
      have hsourceIndex :
          (⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ : Fin (n + 1)) =
            ⟨start + ((j - 2) + 1), by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = start + ((j - 2) + 1)
        omega
      have htargetIndex :
          (⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ : Fin (n + 1)) =
            ⟨start + (j - 1), by omega⟩ := by
        apply Fin.ext
        change i.val - 1 = start + (j - 1)
        omega
      have hsAt :
          a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ =
            JordanProfileOrder.localOrder scale effective (j - 2) := by
        rw [hsourceIndex]
        exact hs
      have htAt :
          b.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.succ_lt_large
            omega⟩ =
            JordanProfileOrder.localOrder scale effective (j - 1) := by
        rw [htargetIndex]
        exact ht
      have hfirst := hstrict.1
      have hscaleLe : scale ≤ effective := by omega
      rw [hsAt, htAt,
        JordanProfileOrder.localOrder_even_of_scale_le
          hscaleLe hsourceEven,
        JordanProfileOrder.localOrder_odd_of_scale_le
          hscaleLe htargetOdd, himproper] at hfirst
      omega
    · have hjOdd := Nat.not_even_iff_odd.mp hjEven
      rcases hjOdd with ⟨m, hm⟩
      have hjLt : j < c := by
        rcases hcEven with ⟨l, hl⟩
        omega
      have hsourceEven : Even (j - 1) := ⟨m, by omega⟩
      have htargetOdd : ¬Even j := hjEven
      have hs := hlargeCommon (j - 1) (by omega)
      have ht := hsmallCommon j hjLt
      have hsourceIndex :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (n + 1)) =
            ⟨start + ((j - 1) + 1), by omega⟩ := by
        apply Fin.ext
        change i.val = start + ((j - 1) + 1)
        omega
      have htargetIndex :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (n + 1)) =
            ⟨start + j, by omega⟩ := by
        apply Fin.ext
        change i.val = start + j
        omega
      have hsAt :
          a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
            JordanProfileOrder.localOrder scale effective (j - 1) := by
        rw [hsourceIndex]
        exact hs
      have htAt :
          b.order ⟨i.val, by have := i.succ_lt_large; omega⟩ =
            JordanProfileOrder.localOrder scale effective j := by
        rw [htargetIndex]
        exact ht
      have hsecond := hstrict.2
      have hscaleLe : scale ≤ effective := by omega
      rw [hsAt, htAt,
        JordanProfileOrder.localOrder_even_of_scale_le
          hscaleLe hsourceEven,
        JordanProfileOrder.localOrder_odd_of_scale_le
          hscaleLe htargetOdd, himproper] at hsecond
      omega

/-- Complete direct-range classification in the adjacent-unary case. -/
theorem weakUnaryShift_longTrigger_direct_endpoint
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hrange : D.LongReducedRange i)
    (htrigger : BONG.GoodBONG.sectionFiveLongTrigger a b i) :
    finrank K (D.complementStrictWeak.component i₀).carrier = 1 ∧
      i.val = D.largeSelectedStart + 1 := by
  let start := D.largeSelectedStart
  let c := finrank K (D.complementStrictWeak.component i₀).carrier
  have hstartEnd :=
    D.weakUnaryShift_smallSelectedStart_eq_intervalEnd hfin i₀ hi₀
  change D.smallSelectedStart = start + c at hstartEnd
  have hright : i.val ≤ start + c := by
    change i.val ≤ D.smallSelectedStart +
      finrank K
        (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
      at hrange
    rw [D.smallAlmostJordan_finrank_selected, hfin, hstartEnd] at hrange
    omega
  have hstrict :=
    BONG.GoodBONG.sectionFiveLongTrigger_pair_strict a b i htrigger
  by_cases hleftRange : i.val ≤ start
  · let I : Fin (n + 1) := ⟨i.val - 1, by
      have := i.one_lt
      have := i.succ_lt_large
      omega⟩
    have hindexBefore : I.val < start := by
      dsimp only [I, Fin.val_mk]
      have := i.one_lt
      omega
    have hbefore := D.weakUnaryShift_component_before_of_index_lt_start
      a I (by simpa only [start, largeSelectedStart] using hindexBefore)
    have hiNext : I.val + 1 < n + 1 := by
      dsimp only [I, Fin.val_mk]
      have := i.one_lt
      have := i.succ_lt_large
      omega
    have hreverse :=
      D.weakUnaryShift_reverse_order_at_current_or_next_before_selected
        hfin i₀ hi₀ a b I hiNext hbefore
    have hcurrentIndex : I =
        (⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hnextIndex :
        (⟨I.val + 1, hiNext⟩ : Fin (n + 1)) =
          ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
      apply Fin.ext
      change I.val + 1 = i.val
      dsimp only [I, Fin.val_mk]
      have := i.one_lt
      omega
    rcases hreverse with hreverse | hreverse
    · have hstrictCurrent : a.order I < b.order I := by
        simpa only [hcurrentIndex] using hstrict.1
      exact (not_lt_of_ge hreverse hstrictCurrent).elim
    · rw [hnextIndex] at hreverse
      exact (not_lt_of_ge hreverse hstrict.2).elim
  · exact D.weakUnaryShift_pair_strict_interval_endpoint
      hfin i₀ hi₀ a b i (lt_of_not_ge hleftRange) hright hstrict

/-- In the aligned direct range, an active long trigger can occur only at
the endpoint of a binary selected block: `a = 2` and
`i = n_{k₁} + 1` in the notation of the paper. -/
theorem weakAligned_longTrigger_direct_endpoint
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hrange : D.LongReducedRange i)
    (htrigger : BONG.GoodBONG.sectionFiveLongTrigger a b i) :
    finrank K D.input.block.component.carrier = 2 ∧
      i.val = D.largeSelectedStart + 1 := by
  let r : RepresentationIndex (n + 1) (n + 1) :=
    { val := i.val
      pos := by have := i.one_lt; omega
      lt_large := by have := i.succ_lt_large; omega
      le_small := by have := i.succ_lt_large; omega }
  have hrange' : D.DefectReducedRange r := by
    exact hrange
  let I : Fin (n + 1) := ⟨i.val - 1, by
    have := i.one_lt
    have := i.succ_lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  rcases D.weakAligned_reducedRange_coordinate hselected a r hrange' with
    hbefore | ⟨hposition, hlocal⟩
  · have hiNext : I.val + 1 < n + 1 := by
      dsimp only [I, Fin.val_mk]
      have := i.one_lt
      have := i.succ_lt_large
      omega
    have hreverse :=
      D.weakAligned_reverse_order_at_current_or_next_before_selected
        hselected a b I hiNext hbefore
    have hstrict :=
      BONG.GoodBONG.sectionFiveLongTrigger_pair_strict a b i htrigger
    have hcurrentIndex : I =
        (⟨i.val - 1, by
          have := i.one_lt
          have := i.succ_lt_large
          omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hnextIndex :
        (⟨I.val + 1, hiNext⟩ : Fin (n + 1)) =
          ⟨i.val, by have := i.succ_lt_large; omega⟩ := by
      apply Fin.ext
      dsimp only [I, Fin.val_mk]
      have := i.one_lt
      omega
    rcases hreverse with hreverse | hreverse
    · have hstrictCurrent : a.order I < b.order I := by
        simpa only [hcurrentIndex] using hstrict.1
      exact (not_lt_of_ge hreverse hstrictCurrent).elim
    · rw [hnextIndex] at hreverse
      exact (not_lt_of_ge hreverse hstrict.2).elim
  · have hglobal := x.index_val_eq_componentStart_add_local I
    have hposition' : (x.indexEquiv I).1 =
        D.largeSelectedPosition := by
      simpa only [r, I, x] using hposition
    have hlocal' : (x.indexEquiv I).2.val = 0 := by
      simpa only [r, I, x] using hlocal
    change i.val - 1 =
      (∑ k ∈ Finset.Iio (x.indexEquiv I).1,
        finrank K (D.largeAlmostJordan.component k).carrier) +
          (x.indexEquiv I).2.val at hglobal
    rw [hlocal', hposition'] at hglobal
    change i.val - 1 = D.largeSelectedStart + 0 at hglobal
    have hindex : i.val = D.largeSelectedStart + 1 := by
      have := i.one_lt
      omega
    refine ⟨?_, hindex⟩
    rcases D.rank_one_or_two with hOne | hTwo
    · have hstart :=
        D.weakAligned_largeSelectedStart_eq_smallSelectedStart hselected
      change D.largeSelectedStart = D.smallSelectedStart at hstart
      change i.val ≤ D.smallSelectedStart +
        finrank K
          (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1
        at hrange
      rw [D.smallAlmostJordan_finrank_selected, hOne, ← hstart] at hrange
      omega
    · exact hTwo

set_option maxHeartbeats 0 in
/-- Complete condition (iv) certificate in the aligned direct range.  The
long trigger forces a binary selected block; the source endpoint is the
terminal coordinate immediately before that block, while the target
endpoint is its second coordinate. -/
theorem weakAligned_longCertificate_direct
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hrange : D.LongReducedRange i)
    (htrigger : BONG.GoodBONG.sectionFiveLongTrigger a b i) :
    BONG.GoodBONG.Beli2019SectionFiveLongCertificate a b i := by
  classical
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 from by
    intro hn
    subst n
    have := i.one_lt
    have := i.succ_lt_large
    omega)
  obtain ⟨hrank, hindex⟩ :=
    D.weakAligned_longTrigger_direct_endpoint hselected a b i hrange htrigger
  let gLarge : Fin (n' + 1) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let gSmall : Fin (n' + 1) := ⟨i.val - 2, by
    have := i.succ_lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let one : Fin (finrank K
      (D.largeAlmostJordan.component D.largeSelectedPosition).carrier) :=
    ⟨1, by rw [D.largeAlmostJordan_finrank_selected, hrank]; omega⟩
  have hlargeCoordinates : x.indexEquiv gLarge.castSucc =
      ⟨D.largeSelectedPosition, one⟩ := by
    apply x.indexEquiv_eq_component_local_of_val_eq_start_add
    change i.val = D.largeSelectedStart + 1
    exact hindex
  have hlargeSelectedLe : D.largeSelectedPosition ≤
      (x.indexEquiv gLarge.castSucc).1 := by
    rw [hlargeCoordinates]
  have hlargeLast : (x.indexEquiv gLarge.castSucc).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv gLarge.castSucc).1).carrier := by
    rw [hlargeCoordinates]
    dsimp only [one, Fin.val_mk]
    rw [D.largeAlmostJordan_finrank_selected, hrank]
  have hlargeNext : (x.indexEquiv gLarge.castSucc).1.val <
      D.complementComponentCount := by
    have hcomponentNext :=
      x.component_succ_lt_of_terminal_of_global_succ gLarge.castSucc
        hlargeLast (by
          dsimp only [gLarge, Fin.castSucc_mk, Fin.val_mk]
          exact i.succ_lt_large)
    omega
  obtain ⟨Rlarge⟩ := D.nonempty_largeStrictBoundaryResolution_afterSelected
    a gLarge (by simpa only [x] using hlargeSelectedLe)
      (by simpa only [x] using hlargeLast)
      (by simpa only [x] using hlargeNext)
  have hstarts := D.weakAligned_largeSelectedStart_eq_smallSelectedStart
    hselected
  let J : Fin (n' + 2) := ⟨i.val - 1, by
    have := i.succ_lt_large
    omega⟩
  have hJCoordinates : y.indexEquiv J =
      ⟨D.smallSelectedPosition,
        ⟨0, D.smallAlmostJordan.component_finrank_pos
          D.smallSelectedPosition⟩⟩ := by
    apply y.indexEquiv_eq_component_zero_of_val_eq_start
    change i.val - 1 = D.smallSelectedStart
    change D.largeSelectedStart = D.smallSelectedStart at hstarts
    omega
  have hsmallTerminal :=
    y.terminal_and_component_lt_of_global_succ_local_zero
      gSmall.castSucc J (by
        dsimp only [gSmall, J, Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) (by
          rw [hJCoordinates])
  have hsmallBefore : (y.indexEquiv gSmall.castSucc).1 <
      D.smallSelectedPosition := by
    calc
      (y.indexEquiv gSmall.castSucc).1 < (y.indexEquiv J).1 :=
        hsmallTerminal.1
      _ = D.smallSelectedPosition := congrArg (fun z ↦ z.1) hJCoordinates
  obtain ⟨Rsmall⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSmall (by simpa only [y] using hsmallBefore)
      (by simpa only [y] using hsmallTerminal.2)
  let largeModel : BONG.GoodBONG.SpaceApproximationModel a gLarge :=
    Rlarge.lemma37Model_i
  let smallModel : BONG.GoodBONG.SpaceApproximationModel b gSmall :=
    Rsmall.lemma37Model_i
  have hcut : Rsmall.weakNext.val ≤ Rlarge.weakNext.val := by
    rw [Rsmall.weakNext_val, Rlarge.weakNext_val]
    have hselectedVal := congrArg Fin.val hselected
    have hlargePosition := congrArg (fun z ↦ z.1) hlargeCoordinates
    have hsmallBefore' := hsmallBefore
    dsimp only [y] at hsmallBefore'
    change ((D.smallWeakProfileWitness b).indexEquiv
        gSmall.castSucc).1.val < D.smallSelectedPosition.val at hsmallBefore'
    have hlargePosition' :
        ((D.largeWeakProfileWitness a).indexEquiv gLarge.castSucc).1 =
          D.largeSelectedPosition := by
      simpa only [x] using hlargePosition
    rw [hlargePosition']
    omega
  have hcarrier : smallModel.carrier ≤ largeModel.carrier := by
    dsimp only [smallModel, largeModel]
    rw [Rsmall.lemma37Model_i_carrier_eq,
      Rlarge.lemma37Model_i_carrier_eq,
      ← D.aligned_prefixCarrier_eq hselected Rsmall.weakNext.val]
    exact D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono hcut
  exact BONG.GoodBONG.Beli2019SectionFiveLongCertificate.represented
    (a.longRepresentation_of_approximationModels b i htrigger
      largeModel smallModel hcarrier)

set_option maxHeartbeats 0 in
/-- Complete condition (iv) certificate in the adjacent-unary direct range.
The target endpoint is the terminal coordinate of the unique rank-one
intermediate component, and the source endpoint is the terminal coordinate
immediately before the exchanged pair. -/
theorem weakUnaryShift_longCertificate_direct
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hrange : D.LongReducedRange i)
    (htrigger : BONG.GoodBONG.sectionFiveLongTrigger a b i) :
    BONG.GoodBONG.Beli2019SectionFiveLongCertificate a b i := by
  classical
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 from by
    intro hn
    subst n
    have := i.one_lt
    have := i.succ_lt_large
    omega)
  obtain ⟨hcommonRank, hindex⟩ :=
    D.weakUnaryShift_longTrigger_direct_endpoint hfin i₀ hi₀
      a b i hrange htrigger
  let gLarge : Fin (n' + 1) := ⟨i.val, by
    have := i.succ_lt_large
    omega⟩
  let gSmall : Fin (n' + 1) := ⟨i.val - 2, by
    have := i.succ_lt_large
    omega⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcommonPos : 0 <
      finrank K (D.complementStrictWeak.component i₀).carrier := by
    rw [hcommonRank]
    omega
  have hlargeCoordinates : x.indexEquiv gLarge.castSucc =
      ⟨D.smallSelectedPosition,
        ⟨0, by
          rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
            hfin i₀ hi₀]
          exact hcommonPos⟩⟩ := by
    have hraw := D.weakUnaryShift_largeCommon_indexEquiv
      hfin i₀ hi₀ a 0 hcommonPos
    simpa only [x, gLarge, hindex, Fin.castSucc_mk, Nat.zero_add] using hraw
  have hlargeSelectedLe : D.largeSelectedPosition ≤
      (x.indexEquiv gLarge.castSucc).1 := by
    rw [hlargeCoordinates]
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change D.largeSelectedPosition.val ≤ D.smallSelectedPosition.val
    omega
  have hlargeLast : (x.indexEquiv gLarge.castSucc).2.val + 1 =
      finrank K (D.largeAlmostJordan.component
        (x.indexEquiv gLarge.castSucc).1).carrier := by
    rw [hlargeCoordinates]
    dsimp only [Fin.val_mk]
    rw [D.weakUnaryShift_largeComponentRank_at_smallSelected
      hfin i₀ hi₀, hcommonRank]
  have hlargeNext : (x.indexEquiv gLarge.castSucc).1.val <
      D.complementComponentCount := by
    have hcomponentNext :=
      x.component_succ_lt_of_terminal_of_global_succ gLarge.castSucc
        hlargeLast (by
          dsimp only [gLarge, Fin.castSucc_mk, Fin.val_mk]
          exact i.succ_lt_large)
    omega
  obtain ⟨Rlarge⟩ := D.nonempty_largeStrictBoundaryResolution_afterSelected
    a gLarge (by simpa only [x] using hlargeSelectedLe)
      (by simpa only [x] using hlargeLast)
      (by simpa only [x] using hlargeNext)
  let J : Fin (n' + 2) := ⟨D.largeSelectedStart, by
    have := i.succ_lt_large
    omega⟩
  have hJCoordinates : y.indexEquiv J =
      ⟨D.largeSelectedPosition,
        ⟨0, by
          rw [D.weakUnaryShift_smallComponentRank_at_largeSelected
            hfin i₀ hi₀]
          exact hcommonPos⟩⟩ := by
    have hraw := D.weakUnaryShift_smallCommon_indexEquiv
      hfin i₀ hi₀ a b 0 hcommonPos
    simpa only [y, J, Nat.add_zero] using hraw
  have hsmallTerminal :=
    y.terminal_and_component_lt_of_global_succ_local_zero
      gSmall.castSucc J (by
        dsimp only [gSmall, J, Fin.castSucc_mk, Fin.val_mk]
        have := i.one_lt
        omega) (by rw [hJCoordinates])
  have hsmallBeforeLarge : (y.indexEquiv gSmall.castSucc).1 <
      D.largeSelectedPosition := by
    calc
      (y.indexEquiv gSmall.castSucc).1 < (y.indexEquiv J).1 :=
        hsmallTerminal.1
      _ = D.largeSelectedPosition := congrArg (fun z ↦ z.1) hJCoordinates
  have hsmallBefore : (y.indexEquiv gSmall.castSucc).1 <
      D.smallSelectedPosition := by
    have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
      hfin i₀ hi₀
    change (y.indexEquiv gSmall.castSucc).1.val <
      D.smallSelectedPosition.val
    change (y.indexEquiv gSmall.castSucc).1.val <
      D.largeSelectedPosition.val at hsmallBeforeLarge
    omega
  obtain ⟨Rsmall⟩ := D.nonempty_smallStrictBoundaryResolution
    b gSmall (by simpa only [y] using hsmallBefore)
      (by simpa only [y] using hsmallTerminal.2)
  let largeModel : BONG.GoodBONG.SpaceApproximationModel a gLarge :=
    Rlarge.lemma37Model_i
  let smallModel : BONG.GoodBONG.SpaceApproximationModel b gSmall :=
    Rsmall.lemma37Model_i
  have hsourceCut : Rsmall.weakNext.val ≤
      D.largeSelectedPosition.val := by
    rw [Rsmall.weakNext_val]
    have hsmallBeforeLarge' := hsmallBeforeLarge
    dsimp only [y] at hsmallBeforeLarge'
    change ((D.smallWeakProfileWitness b).indexEquiv
        gSmall.castSucc).1.val < D.largeSelectedPosition.val at hsmallBeforeLarge'
    omega
  have hcut : Rsmall.weakNext.val ≤ Rlarge.weakNext.val := by
    rw [Rsmall.weakNext_val, Rlarge.weakNext_val]
    have hsmallBefore' := hsmallBefore
    dsimp only [y] at hsmallBefore'
    change ((D.smallWeakProfileWitness b).indexEquiv
        gSmall.castSucc).1.val < D.smallSelectedPosition.val at hsmallBefore'
    have hlargePosition := congrArg (fun z ↦ z.1) hlargeCoordinates
    have hlargePosition' :
        ((D.largeWeakProfileWitness a).indexEquiv gLarge.castSucc).1 =
          D.smallSelectedPosition := by
      simpa only [x] using hlargePosition
    rw [hlargePosition']
    omega
  have hcarrier : smallModel.carrier ≤ largeModel.carrier := by
    dsimp only [smallModel, largeModel]
    rw [Rsmall.lemma37Model_i_carrier_eq,
      Rlarge.lemma37Model_i_carrier_eq,
      ← D.unaryShift_prefixCarrier_eq_before hfin i₀ hi₀
        Rsmall.weakNext.val hsourceCut]
    exact D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier_mono hcut
  exact BONG.GoodBONG.Beli2019SectionFiveLongCertificate.represented
    (a.longRepresentation_of_approximationModels b i htrigger
      largeModel smallModel hcarrier)

set_option maxHeartbeats 0 in
/-- Complete condition (iv) certificate on the direct reduced range.  This
packages the aligned rank-two case and the two alternatives for a rank-one
selected component. -/
theorem longCertificate_direct
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (D : Beli2019Lemma51Data q M N)
    (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (hrange : D.LongReducedRange i) :
    BONG.GoodBONG.Beli2019SectionFiveLongCertificate a b i := by
  classical
  by_cases htrigger : BONG.GoodBONG.sectionFiveLongTrigger a b i
  · rcases D.rank_one_or_two with hOne | hTwo
    · rcases D.selectedPositions_unary_alternative hOne with
        hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
      · exact D.weakAligned_longCertificate_direct hselected
          a b i hrange htrigger
      · exact D.weakUnaryShift_longCertificate_direct hOne i₀ hi₀
          a b i hrange htrigger
    · exact D.weakAligned_longCertificate_direct
        (D.selectedPositions_eq_of_rank_two hTwo) a b i hrange htrigger
  · exact BONG.GoodBONG.Beli2019SectionFiveLongCertificate.vacuous htrigger

set_option maxHeartbeats 0 in
/-- The complete pointwise Section 5 certificate for condition 2.1(iv).
Every boundary lies either in the direct reduced range or in the direct
range of the swapped reverse-dual inclusion. -/
theorem longCertificate_complete
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (D : Beli2019Lemma51Data q M N)
    {a : BONG.GoodBONG q M (n + 1)}
    {b : BONG.GoodBONG q N (n + 1)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    BONG.GoodBONG.Beli2019SectionFiveLongCertificate a b i := by
  rcases D.longReducedRange_or_reverseDualReducedRange R.lemma51 i
      a.toBONG.length_eq_finrank with hrange | hreverse
  · exact D.longCertificate_direct a b i hrange
  · have Cdual := R.lemma51.longCertificate_direct
      R.sourceDual R.targetDual i.reverseComplement hreverse
    exact R.originalLongCertificate_of_reverse i Cdual

end Lattice.Beli2019Lemma51Data

end Bong
