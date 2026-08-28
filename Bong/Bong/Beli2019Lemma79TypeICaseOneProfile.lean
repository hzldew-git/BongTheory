/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeICaseOneReduction
import Bong.Bong.Beli2019Lemma79NormOrder
import Bong.Bong.Beli2019Lemma75

/-!
# Beli (2019), Lemma 7.9(ii), case 1: endpoint orders

The exceptional first-switch configuration forces the two even prefixes in
case 1 to have the same first order.  Their last orders are both lower by
exactly `2e`.  This is the numerical input needed to apply Lemma 7.5 to both
prefixes.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The endpoint orders displayed at the start of Lemma 7.9(ii), case 1. -/
theorem beli2019Lemma79_typeI_caseOne_endpointOrders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    b.order 0 = c.order 0 ∧
      b.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) ∧
      c.order ⟨i.val - 1, by
          have hiBound := i.lt_large
          omega⟩ = c.order 0 - 2 * (ramificationIndex K : Int) := by
  have hleftPos : 0 < C.leftSwitch := by
    have hiPos := i.pos
    omega
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have htargetCurrent := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  have hbZeroRaw : b.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero D.anchor + 1 := htargetZero
  have hbCurrentRaw : b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    simpa only [hleft] using htargetCurrent
  have haZeroRaw : a.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero D.anchor := hsourceZero
  have haZero : a.order 0 =
      a.orderSequence.entryOrZero D.anchor := by
    rw [← a.orderSequence_entryOrZero_eq_order]
    exact haZeroRaw
  have hbZero : b.order 0 = a.order 0 + 1 := by
    change b.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero 0 + 1
    omega
  have hbCurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    exact hbCurrentRaw
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 + 1 := by
    omega
  let previous : Fin (n + 1) := ⟨i.val - 1, by
    have hiBound := i.lt_large
    omega⟩
  have hpreviousSucc : previous.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  have hpreviousCast : previous.castSucc =
      (⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hbPrevious : b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap at hgap
    rw [hpreviousSucc, hpreviousCast] at hgap
    omega
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hbZeroLe : b.order 0 ≤ c.order 0 := by
    omega
  have hcFirstStepRaw := c.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    (⟨0, by omega⟩ : Fin (n + 2)) (by simp)
  have hcFirstStep : c.order 0 ≤
      c.order ⟨1, by omega⟩ + 2 * (ramificationIndex K : Int) := by
    change -(2 * (ramificationIndex K : Int)) ≤
      c.order ⟨1, by omega⟩ - c.order 0 at hcFirstStepRaw
    omega
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    rcases hiEven with ⟨d, hd⟩
    omega
  have hdistanceEven : Even ((i.val - 1) - 1) := by
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    omega
  have hcMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    1 (i.val - 1) (by omega) (by
      have hiBound := i.lt_large
      omega) hdistanceEven
  have hcMonotone : c.order ⟨1, by omega⟩ ≤
      c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hcMonotoneRaw
  have hcZeroLe : c.order 0 ≤ b.order 0 := by
    calc
      c.order 0 ≤ c.order ⟨1, by omega⟩ +
          2 * (ramificationIndex K : Int) := hcFirstStep
      _ ≤ c.order ⟨i.val - 1, by
            have hiBound := i.lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) := by
        omega
      _ = b.order 0 := by
        rw [hprevious, hbPrevious]
        ring
  have hzero : b.order 0 = c.order 0 := by omega
  refine ⟨hzero, hbPrevious, ?_⟩
  rw [hprevious, hbPrevious, ← hzero]

/-- Lemma 7.5 applies to both prefixes in the exceptional case, with the
same high order and the same terminal order. -/
theorem beli2019Lemma79_typeI_caseOne_lemma75
    [Beli2006AlphaLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    let first : Fin (n + 1) := ⟨0, by omega⟩
    let lastPair : Fin (n + 1) := ⟨i.val - 2, by
      have hiBound := i.lt_large
      omega⟩
    Lemma75Consequences b first lastPair (b.order 0) ∧
      Lemma75Consequences c first lastPair (b.order 0) := by
  dsimp only
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    have hiPos := i.pos
    rcases hiEven with ⟨d, hd⟩
    omega
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let lastPair : Fin (n + 1) := ⟨i.val - 2, by
    have hiBound := i.lt_large
    omega⟩
  have hfirstLast : first ≤ lastPair := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hlastEven : Even (lastPair.val - first.val) := by
    simp only [first, lastPair]
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    omega
  have hlastSucc : lastPair.succ =
      (⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [lastPair, Fin.val_succ]
    omega
  rcases beli2019Lemma79_typeI_caseOne_endpointOrders
      a b c D C hnorm i hleft hgap hprevious with
    ⟨hfirstOrders, hbLast, hcLast⟩
  have hbInitial : b.order first.castSucc = b.order 0 := by
    apply congrArg b.order
    apply Fin.ext
    rfl
  have hcInitial : c.order first.castSucc = b.order 0 := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex, ← hfirstOrders]
  have hbTerminal : b.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc]
    exact hbLast
  have hcTerminal : c.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc, hcLast, ← hfirstOrders]
  constructor
  · exact b.beli2019Lemma75 first lastPair (b.order 0)
      hfirstLast hlastEven hbInitial hbTerminal
  · exact c.beli2019Lemma75 first lastPair (b.order 0)
      hfirstLast hlastEven hcInitial hcTerminal

end BONG.GoodBONG

end Bong
