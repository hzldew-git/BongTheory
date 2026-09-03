/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Theorem47
import Bong.Bong.HeHu2022SectionSix

/-!
# He--Hu 2022, Theorem 1.1

This file assembles the even and odd criteria, the Section 6 conversions,
and the ambient-rank classification into the exact criterion printed as
Theorem 1.1 of the published version.
-/

namespace Bong

open Dyadic Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem corollary46Invariants_castSelf
    (a : GoodBONG q L 4) (h : 4 = 4) :
    (a.castLength h).HeHuCorollary46Invariants ↔
      a.HeHuCorollary46Invariants := by
  have hh : h = (rfl : 4 = 4) := Subsingleton.elim _ _
  cases hh
  rfl

/-- The exceptional clause in Theorem 1.1 is exactly the invariant clause
of Corollary 4.6. -/
theorem heHuCorollary46Invariants_iff_theorem11Exceptional
    (a : GoodBONG q L 4) :
    a.HeHuCorollary46Invariants ↔
      a.HeHuExceptionalQuaternaryConditions 2 := by
  constructor
  · intro h
    refine ⟨rfl, rfl, h.splitSpace, ?_⟩
    intro _
    refine ⟨h.order0, h.order2, ?_, ?_⟩
    · rw [show (⟨1, by omega⟩ : Fin 4) = 1 by ext; rfl, h.order1]
      ring
    · rw [show (⟨3, by omega⟩ : Fin 4) = 3 by ext; rfl, h.order3]
      ring
  · rintro ⟨_, _, hsplit, horders⟩
    have h := horders rfl
    exact
      { splitSpace := hsplit
        order0 := h.1
        order2 := h.2.1
        order1 := by
          have hsum := h.2.2.1
          rw [show (⟨1, by omega⟩ : Fin 4) = 1 by ext; rfl] at hsum
          linear_combination hsum
        order3 := by
          have hsum := h.2.2.2
          rw [show (⟨3, by omega⟩ : Fin 4) = 3 by ext; rfl] at hsum
          linear_combination hsum }

/-- In the stable even-rank range, the printed clauses of Theorem 1.1 are
equivalent to the three invariant conditions of Theorem 4.1. -/
theorem heHuTheorem11EvenStableConditions_iff_sectionConditions
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 2 ≤ m)
    (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuStableConditions (2 * k + 2) (by omega) ↔
      a.HeHuEvenSectionConditions (2 * k + 2) (by omega) := by
  let n := 2 * k + 2
  have hnTwo : 2 ≤ n := by omega
  have hnEven : Even n := ⟨k + 1, by omega⟩
  have hmStable : n + 2 ≤ m + 2 := by omega
  have hI1Bridge :=
    a.heHuI1E_iff_alternatingInitialOrders_and_boundary hmStable hnEven
  constructor
  · intro hStable
    rcases hStable.parityBranch with hEven | hOdd
    · have hI1 : a.HeHuI1E n (by omega) :=
        hI1Bridge.mpr ⟨hStable.initialOrders, hEven.order_n1⟩
      have hI3 : a.HeHuI3E n (by omega) := by
        intro _ hGap
        exact hEven.large_last_gap hGap
      have h61 := a.heHu2022Lemma61 hnTwo hnEven hmStable hIntegral hI1
        hEven.order_n2_range
      have hI2 : a.HeHuI2E n (by omega) := by
        by_cases hBoundary : a.order ⟨n + 1, by omega⟩ =
            2 - 2 * (ramificationIndex K : Int)
        · apply (h61.1 hBoundary).mp
          unfold HeHuTheorem11EvenClause1a
          have hOuter : HeHuInEvenInterval
              (a.order ⟨n + 1, by omega⟩)
              (2 - 2 * (ramificationIndex K : Int)) 0 := by
            rw [hBoundary]
            refine ⟨le_rfl, ?_, ?_⟩
            · have hePos := ramificationIndex_pos (K := K)
              omega
            · exact ⟨1 - (ramificationIndex K : Int), by ring⟩
          exact (hEven.middle_even_branch hOuter).1 hBoundary
        · apply (h61.2 hBoundary).mp
          intro hOuter
          exact (hEven.middle_even_branch hOuter).2 hBoundary
      exact ⟨hI1, hI2, hI3⟩
    · have hParityImpossible : ¬ Odd n := Nat.not_odd_iff_even.mpr hnEven
      exact False.elim (hParityImpossible hOdd.parity)
  · intro hSection
    have hInitial := hI1Bridge.mp hSection.i1
    have hRange :
        HeHuInEvenInterval (a.order ⟨n + 1, by omega⟩)
            (-(2 * (ramificationIndex K : Int))) 0 ∨
          a.order ⟨n + 1, by omega⟩ = 1 := by
      have hI2 := hSection.i2
      unfold HeHuI2E at hI2
      dsimp only at hI2
      rcases hI2 with hZero | ⟨hOne, _⟩
      · left
        have hGap :=
          ((a.heHu2022Proposition26 ⟨n, by omega⟩).alphaZero).mp hZero
        have hGapValue : a.orderGap ⟨n, by omega⟩ =
            a.order ⟨n + 1, by omega⟩ := by
          unfold orderGap
          rw [show (⟨n, by omega⟩ : Fin (m + 2)).succ =
              (⟨n + 1, by omega⟩ : Fin (m + 3)) by ext; rfl]
          rw [show (⟨n, by omega⟩ : Fin (m + 2)).castSucc =
              (⟨n, by omega⟩ : Fin (m + 3)) by ext; rfl]
          rw [hInitial.2, sub_zero]
        rw [hGapValue] at hGap
        refine ⟨?_, ?_, ?_⟩
        · rw [hGap]
        · rw [hGap]
          exact neg_nonpos.mpr (by positivity)
        · exact ⟨-(ramificationIndex K : Int), by rw [hGap]; ring⟩
      · have hGapValue : a.orderGap ⟨n, by omega⟩ =
            a.order ⟨n + 1, by omega⟩ := by
          unfold orderGap
          rw [show (⟨n, by omega⟩ : Fin (m + 2)).succ =
              (⟨n + 1, by omega⟩ : Fin (m + 3)) by ext; rfl]
          rw [show (⟨n, by omega⟩ : Fin (m + 2)).castSucc =
              (⟨n, by omega⟩ : Fin (m + 3)) by ext; rfl]
          rw [hInitial.2, sub_zero]
        have hShape :=
          (a.heHu2022Proposition26 ⟨n, by omega⟩).alphaOne hOne |>.1
        rw [hGapValue] at hShape
        rcases hShape with hOrderOne | hEvenRange
        · exact Or.inr hOrderOne
        · exact Or.inl ⟨by omega, hEvenRange.2.2, hEvenRange.1⟩
    have h61 := a.heHu2022Lemma61 hnTwo hnEven hmStable hIntegral
      hSection.i1 hRange
    refine
      { initialOrders := hInitial.1
        parityBranch := Or.inl
          { parity := hnEven
            order_n1 := hInitial.2
            order_n2_range := hRange
            middle_even_branch := ?_
            large_last_gap := ?_ } }
    · intro hOuter
      constructor
      · intro hBoundary
        exact (h61.1 hBoundary).mpr hSection.i2
      · intro hNotBoundary
        exact (h61.2 hNotBoundary).mpr hSection.i2 hOuter
    · intro hGap
      exact (hSection.i3 hmStable hGap)

/-- In the stable odd-rank range, Corollary 6.2 and Lemma 6.3 identify the
printed clauses of Theorem 1.1 with the three conditions of Theorem 5.1. -/
theorem heHuTheorem11OddStableConditions_iff_sectionConditions
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuStableConditions (2 * k + 3) (by omega) ↔
      a.HeHuOddSectionConditions (2 * k + 3) (by omega) (by omega) := by
  let n := 2 * k + 3
  have hnThree : 3 ≤ n := by omega
  have hnOdd : Odd n := ⟨k + 1, by omega⟩
  have hmStable : n + 2 ≤ m + 2 := by omega
  constructor
  · intro hStable
    rcases hStable.parityBranch with hEven | hOdd
    · have hParityImpossible : ¬ Even n := Nat.not_even_iff_odd.mpr hnOdd
      exact False.elim (hParityImpossible hEven.parity)
    · let hInitialPrinted : a.HeHuTheorem11OddInitialConditions n hmStable :=
        { initial := hStable.initialOrders
          orderRange := hOdd.order_n1_range
          middle := hOdd.middle_even_branch }
      have hI1 : a.HeHuI1O n hnThree hmStable :=
        (a.heHu2022Corollary62 hnThree hnOdd hmStable).mp hInitialPrinted
      have hAlphaZeroIff :=
        a.heHuTheorem53_alpha_zero_iff_boundaryOrder hm hStable.initialOrders
      have hI2First :
          a.alphaValue ⟨n - 1, by omega⟩ = 0 →
            a.order ⟨n + 1, by omega⟩ = 0 ∨
              a.order ⟨n + 1, by omega⟩ = 1 := by
        intro hAlphaZero
        have hBottom : a.order ⟨n, by omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
          simpa only [show n - 1 = 2 * k + 2 by omega] using
            hAlphaZeroIff.mp (by
              simpa only [show n - 1 = 2 * k + 2 by omega] using hAlphaZero)
        exact hOdd.bottom_branch hBottom
      have hI2Second : a.HeHuI2OSecondPart n hnThree hmStable :=
        (a.heHu2022Lemma63 hnThree hnOdd hmStable hIntegral hI1).mp
          hOdd.upper_branch
      exact
        { i1 := hI1
          i2 := ⟨hI2First, hI2Second⟩
          i3 := hOdd.last_gap }
  · intro hSection
    have hInitialPrinted :
        a.HeHuTheorem11OddInitialConditions n hmStable :=
      (a.heHu2022Corollary62 hnThree hnOdd hmStable).mpr hSection.i1
    have hAlphaZeroIff :=
      a.heHuTheorem53_alpha_zero_iff_boundaryOrder hm
        hInitialPrinted.initial
    refine
      { initialOrders := hInitialPrinted.initial
        parityBranch := Or.inr
          { parity := hnOdd
            order_n1_range := hInitialPrinted.orderRange
            middle_even_branch := hInitialPrinted.middle
            upper_branch := ?_
            bottom_branch := ?_
            last_gap := hSection.i3 } }
    · exact
        (a.heHu2022Lemma63 hnThree hnOdd hmStable hIntegral hSection.i1).mpr
          hSection.i2.2
    · intro hBottom
      apply hSection.i2.1
      have hAlphaZero :
          a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 :=
        hAlphaZeroIff.mpr (by simpa only [n] using hBottom)
      rw [show (⟨n - 1, by omega⟩ : Fin (m + 2)) =
          ⟨2 * k + 2, by omega⟩ by ext; dsimp only [n]; omega]
      exact hAlphaZero

private theorem isNUniversal_ambient
    {n : Nat} (h : Lattice.IsNUniversal.{u, v, u} q L n) :
    Lattice.AmbientlyNUniversal.{u, v, u} q n := by
  intro W _ _ r M hRank hM
  exact (h.2 r M hRank hM).ambient

/-- The even-rank half of Theorem 1.1, with no rank assumption on the
source.  The impossible ranks are discharged by the ambient classification. -/
theorem heHu2022Theorem11Even
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 2) ↔
      a.HeHuTheorem11Conditions (2 * k + 2) := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hRank : 2 * k + 2 ≤ m + 1
  · rw [a.heHu2022Theorem47Even hRank hIntegral]
    constructor
    · intro h47
      rcases h47 with hStable | hExceptional
      · rcases hStable with ⟨hm, hStable⟩
        right
        have hSection :
            a.HeHuEvenSectionConditions (2 * k + 2) (by omega) :=
          (a.heHuEvenSectionConditions_iff_theorem47StableConditions
            (by omega) (by omega) ⟨k + 1, by omega⟩).mpr hStable
        exact ⟨by omega,
          (a.heHuTheorem11EvenStableConditions_iff_sectionConditions
            hm hIntegral).mpr hSection⟩
      · rcases hExceptional with ⟨hk, hm, hInvariant⟩
        subst k
        subst m
        left
        apply (a.heHuCorollary46Invariants_iff_theorem11Exceptional).mp
        exact (corollary46Invariants_castSelf a _).mp hInvariant
    · intro h11
      rcases h11 with hExceptional | hStable
      · unfold HeHuExceptionalQuaternaryConditions at hExceptional
        rcases hExceptional with ⟨hm, hk, hsplit, horders⟩
        have hmOne : m = 1 := by omega
        have hkZero : k = 0 := by omega
        subst k
        subst m
        right
        refine ⟨rfl, rfl, ?_⟩
        apply (corollary46Invariants_castSelf a _).mpr
        apply (a.heHuCorollary46Invariants_iff_theorem11Exceptional).mpr
        exact ⟨rfl, rfl, hsplit, horders⟩
      · rcases hStable with ⟨hmStable, hStable⟩
        left
        have hm : 2 * k + 2 ≤ m := by omega
        refine ⟨hm, ?_⟩
        apply
          (a.heHuEvenSectionConditions_iff_theorem47StableConditions
            (by omega) (by omega) ⟨k + 1, by omega⟩).mp
        exact
          (a.heHuTheorem11EvenStableConditions_iff_sectionConditions
            hm hIntegral).mp hStable
  · constructor
    · intro hUniversal
      exfalso
      apply hRank
      have hAmbient :
          Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) :=
        isNUniversal_ambient (q := q) (L := L) hUniversal
      have hfinrank : finrank K V = m + 3 :=
        a.toBONG.length_eq_finrank.symm
      rcases
          (Lattice.ambientlyEvenUniversal_rank_classification
            (q := q) k).mp hAmbient with hStable | hExceptional
      · omega
      · rcases hExceptional with ⟨hk, hfour, _⟩
        omega
    · intro h11
      exfalso
      apply hRank
      rcases h11 with hExceptional | hStable
      · exact by
          unfold HeHuExceptionalQuaternaryConditions at hExceptional
          omega
      · rcases hStable with ⟨hmStable, _⟩
        omega

/-- The odd-rank half of Theorem 1.1.  The ambient classification rules out
all ranks below the stable range, so no exceptional odd case remains. -/
theorem heHu2022Theorem11Odd
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 3) ↔
      a.HeHuTheorem11Conditions (2 * k + 3) := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hRank : 2 * k + 3 ≤ m
  · rw [(@heHu2022Theorem51Odd K _ _ _ _ _ V _ _ q L
      sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
      m k a hRank hIntegral)]
    constructor
    · rintro ⟨_hAmbient, hSection⟩
      right
      exact ⟨by omega,
        (a.heHuTheorem11OddStableConditions_iff_sectionConditions
          hRank hIntegral).mpr hSection⟩
    · intro h11
      rcases h11 with hExceptional | hStable
      · unfold HeHuExceptionalQuaternaryConditions at hExceptional
        omega
      · rcases hStable with ⟨hmStable, hStable⟩
        have hfinrank : finrank K V = m + 3 :=
          a.toBONG.length_eq_finrank.symm
        have hAmbient :
            Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) :=
          (Lattice.ambientlyOddUniversal_rank_classification
            (q := q) k).mpr (by omega)
        exact ⟨hAmbient,
          (a.heHuTheorem11OddStableConditions_iff_sectionConditions
            hRank hIntegral).mp hStable⟩
  · constructor
    · intro hUniversal
      exfalso
      apply hRank
      have hAmbient :
          Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) :=
        isNUniversal_ambient (q := q) (L := L) hUniversal
      have hfinrank : finrank K V = m + 3 :=
        a.toBONG.length_eq_finrank.symm
      have hStable :=
        (Lattice.ambientlyOddUniversal_rank_classification
          (q := q) k).mp hAmbient
      omega
    · intro h11
      exfalso
      apply hRank
      rcases h11 with hExceptional | hStable
      · unfold HeHuExceptionalQuaternaryConditions at hExceptional
        omega
      · rcases hStable with ⟨hmStable, _⟩
        omega

/-- Theorem 1.1 for a source rank written as `m+3`.  This is the natural
parameterization after the paper's rank classification. -/
theorem heHu2022Theorem11_rankAtLeastThree
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m n : Nat} (a : GoodBONG q L (m + 3))
    (hn : 2 ≤ n) (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuTheorem11Statement.{u, v, u} n hn hIntegral := by
  unfold HeHuTheorem11Statement
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨r, hr⟩
    cases r with
    | zero => omega
    | succ k =>
        have hnValue : n = 2 * k + 2 := by omega
        subst n
        simpa only [show k + 1 + (k + 1) = 2 * k + 2 by omega] using
          (a.heHu2022Theorem11Even (k := k) hIntegral)
  · rcases hnOdd with ⟨r, hr⟩
    cases r with
    | zero => omega
    | succ k =>
        have hnValue : n = 2 * k + 3 := by omega
        subst n
        simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using
          (@heHu2022Theorem11Odd K _ _ _ _ _ V _ _ q L
            sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
            m k a hIntegral)

/-- He--Hu, Theorem 1.1, for an arbitrary source rank.  The ranks below
three are included and proved impossible rather than excluded by a side
hypothesis. -/
theorem heHu2022Theorem11
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m n : Nat} (a : GoodBONG q L m)
    (hn : 2 ≤ n) (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuTheorem11Statement.{u, v, u} n hn hIntegral := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hmThree : 3 ≤ m
  · obtain ⟨d, hd⟩ : ∃ d : Nat, m = d + 3 :=
      ⟨m - 3, by omega⟩
    subst m
    exact @heHu2022Theorem11_rankAtLeastThree K _ _ _ _ _ V _ _ q L
      sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
      d n a hn hIntegral
  · unfold HeHuTheorem11Statement
    constructor
    · intro hUniversal
      exfalso
      have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q n :=
        isNUniversal_ambient (q := q) (L := L) hUniversal
      have hfinrank : finrank K V = m :=
        a.toBONG.length_eq_finrank.symm
      rcases Nat.even_or_odd n with hnEven | hnOdd
      · rcases hnEven with ⟨r, hr⟩
        cases r with
        | zero => omega
        | succ k =>
            have hnValue : n = 2 * k + 2 := by omega
            have hAmbientEven :
                Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) := by
              rw [← hnValue]
              exact hAmbient
            have hClass :=
              (Lattice.ambientlyEvenUniversal_rank_classification
                (q := q) k).mp hAmbientEven
            rcases hClass with hStable | hExceptional
            · omega
            · omega
      · rcases hnOdd with ⟨r, hr⟩
        cases r with
        | zero => omega
        | succ k =>
            have hnValue : n = 2 * k + 3 := by omega
            have hAmbientOdd :
                Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) := by
              rw [← hnValue]
              exact hAmbient
            have hClass :=
              (Lattice.ambientlyOddUniversal_rank_classification
                (q := q) k).mp hAmbientOdd
            omega
    · intro hConditions
      exfalso
      rcases hConditions with hExceptional | hStable
      · unfold HeHuExceptionalQuaternaryConditions at hExceptional
        omega
      · rcases hStable with ⟨hRank, _⟩
        omega

end BONG.GoodBONG

end Bong
