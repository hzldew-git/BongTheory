/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicSectionSix

/-!
# He (2024), Theorem 1.1

This file assembles Theorems 4.1 and 5.1 with Lemmas 6.1 and 6.2 and the
ambient-rank classification.  Its final theorem is the exact criterion printed
as Theorem 1.1 of the publisher version.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- For even `n`, the initial-order and printed parity clauses are exactly the
three invariant conditions of Theorem 4.1. -/
theorem heClassicEvenPrintedConditions_iff_sectionConditions
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnTwo : 2 ≤ n) (hnEven : Even n) (hmStable : n + 2 ≤ m) :
    ((∀ i : Fin n, a.order ⟨i.1, by omega⟩ = 0) ∧
        HeClassicEvenConditions a n (by omega)) ↔
      a.HeClassicEvenSectionConditions n (by omega) := by
  constructor
  · rintro ⟨hInitial, hPrinted⟩
    have hJ1 : a.HeClassicJ1E n (by omega) := by
      intro i
      by_cases hi : i.1 < n
      · exact hInitial ⟨i.1, hi⟩
      · have hiEq : i.1 = n := by omega
        simpa only [show (⟨i.1, by omega⟩ : Fin (m + 1)) =
            ⟨n, by omega⟩ by ext; exact hiEq] using hPrinted.order_n1
    have hClause : a.HeClassicTheorem11EvenClauseOne n hmStable :=
      ⟨hPrinted.order_n2, hPrinted.zero_branch⟩
    exact
      { j1 := hJ1
        j2 := (a.he2022ClassicLemma61 hnTwo hnEven hmStable hJ1).mp hClause
        j3 := by
          intro _
          exact hPrinted.last_gap }
  · intro hSection
    have hClause : a.HeClassicTheorem11EvenClauseOne n hmStable :=
      (a.he2022ClassicLemma61 hnTwo hnEven hmStable hSection.j1).mpr
        hSection.j2
    refine ⟨?_, ?_⟩
    · intro i
      exact hSection.j1 ⟨i.1, by omega⟩
    · exact
        { parity := hnEven
          order_n1 := hSection.j1 ⟨n, by omega⟩
          order_n2 := hClause.1
          zero_branch := hClause.2
          last_gap := hSection.j3 hmStable }

/-- For odd `n`, Lemmas 6.1 and 6.2 identify the printed clauses with the
three invariant conditions of Theorem 5.1. -/
theorem heClassicOddPrintedConditions_iff_sectionConditions
    {m n : Nat} (a : GoodBONG q L (m + 1))
    (hnThree : 3 ≤ n) (hnOdd : Odd n) (hmStable : n + 2 ≤ m)
    (hClassic : Lattice.IsClassicIntegral q L) :
    ((∀ i : Fin n, a.order ⟨i.1, by omega⟩ = 0) ∧
        HeClassicOddConditions a n (by omega)) ↔
      a.HeClassicOddSectionConditions n hnThree hmStable := by
  have hnPredTwo : 2 ≤ n - 1 := by omega
  have hnPredEven : Even (n - 1) := by
    rcases hnOdd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  constructor
  · rintro ⟨hInitial, hPrinted⟩
    have hJ1Pred : a.HeClassicJ1E (n - 1) (by omega) := by
      intro i
      exact hInitial ⟨i.1, by omega⟩
    have hPredClause :
        a.HeClassicTheorem11EvenClauseOne (n - 1) (by omega) := by
      unfold HeClassicTheorem11EvenClauseOne
      convert And.intro hPrinted.order_n1 hPrinted.zero_branch using 1 <;>
        simp only [show n - 1 + 1 = n by omega,
        show n - 1 + 2 = n + 1 by omega,
        show (n - 1 + 2) / 2 = (n + 1) / 2 by omega,
        show m + 1 - 1 = m by omega] <;> aesop
    have hJ2Pred : a.HeClassicJ2E (n - 1) (by omega) :=
      (a.he2022ClassicLemma61 hnPredTwo hnPredEven (by omega) hJ1Pred).mp
        hPredClause
    have hJ1 : a.HeClassicJ1O n hnThree hmStable :=
      (a.heClassicJ1O_iff_j1E_and_j2E hnThree hnOdd hmStable).mpr
        ⟨hJ1Pred, hJ2Pred⟩
    have hClauseTwo : a.HeClassicTheorem11OddClauseTwo n hmStable := by
      simpa [HeClassicTheorem11OddClauseTwo, HeClassicLemma62Branch] using
        hPrinted.upper_branch
    exact
      { j1 := hJ1
        j2 := (a.he2022ClassicLemma62 hnThree hnOdd hmStable hClassic hJ1).mp
          hClauseTwo
        j3 := hPrinted.last_gap }
  · intro hSection
    have hPred :=
      (a.heClassicJ1O_iff_j1E_and_j2E hnThree hnOdd hmStable).mp
        hSection.j1
    have hPredClause :
        a.HeClassicTheorem11EvenClauseOne (n - 1) (by omega) :=
      (a.he2022ClassicLemma61 hnPredTwo hnPredEven (by omega) hPred.1).mpr
        hPred.2
    have hClauseTwo : a.HeClassicTheorem11OddClauseTwo n hmStable :=
      (a.he2022ClassicLemma62 hnThree hnOdd hmStable hClassic hSection.j1).mpr
        hSection.j2
    refine ⟨?_, ?_⟩
    · intro i
      exact hPred.1 ⟨i.1, by omega⟩
    · refine
        { parity := hnOdd
          order_n1 := ?_
          zero_branch := ?_
          upper_branch := ?_
          last_gap := hSection.j3 }
      · unfold HeClassicTheorem11EvenClauseOne at hPredClause
        simpa only [show n - 1 + 1 = n by omega] using hPredClause.1
      · unfold HeClassicTheorem11EvenClauseOne at hPredClause
        convert hPredClause.2 using 1 <;>
          simp only [show n - 1 + 1 = n by omega,
          show n - 1 + 2 = n + 1 by omega,
          show (n - 1 + 2) / 2 = (n + 1) / 2 by omega,
          show m + 1 - 1 = m by omega] <;> aesop
      · simpa [HeClassicTheorem11OddClauseTwo, HeClassicLemma62Branch] using
          hClauseTwo

private theorem isClassicNUniversal_ambient
    {n : Nat} (h : Lattice.IsClassicNUniversal.{u, v, u} q L n) :
    Lattice.AmbientlyNUniversal.{u, v, u} q n := by
  intro W _ _ r M hRank _hIntegral
  obtain ⟨c, hc⟩ := Lattice.exists_classicIntegral_rescale r M
  exact (h.2 r (Lattice.rescale c M) hRank hc).ambient

/-- The even half of Theorem 1.1 once the source rank is written as `m+5`.
The ambient classification supplies the rank bound before Theorem 4.1 is
applied. -/
theorem he2022ClassicTheorem11Even_rankAtLeastFive
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hClassic : Lattice.IsClassicIntegral q L) :
    Lattice.IsClassicNUniversal.{u, v, u} q L (2 * k + 2) ↔
      a.HeClassicTheorem11Conditions (2 * k + 2) := by
  letI : Module.Finite K V := L.moduleFinite
  have hfinrank : finrank K V = m + 5 :=
    a.toBONG.length_eq_finrank.symm
  constructor
  · intro hUniversal
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
        (2 * k + 2) :=
      isClassicNUniversal_ambient (q := q) (L := L) hUniversal
    have hRank : 2 * k + 5 ≤ m + 5 := by
      rcases (Lattice.ambientlyEvenUniversal_rank_classification
        (q := q) k).mp hAmbient with hStable | hExceptional
      · omega
      · rcases hExceptional with ⟨_, hFour, _⟩
        omega
    have hSection :
        a.HeClassicEvenSectionConditions (2 * k + 2) (by omega) :=
      ((a.he2022ClassicTheorem41 (m := m + 1) (t := k) (by omega)).mp
        hUniversal).2.2
    have hPrinted :=
      (a.heClassicEvenPrintedConditions_iff_sectionConditions
        (m := m + 4) (n := 2 * k + 2) (by omega) ⟨k + 1, by omega⟩
          (by omega)).mpr hSection
    exact
      { rank_bound := hRank
        initial_orders := hPrinted.1
        parity_branch := Or.inl hPrinted.2 }
  · intro hConditions
    have hRank := hConditions.rank_bound
    rcases hConditions.parity_branch with hEven | hOdd
    · have hEven' : HeClassicEvenConditions a (2 * k + 2) (by omega) := by
        simpa using hEven
      have hSection :
          a.HeClassicEvenSectionConditions (2 * k + 2) (by omega) :=
        (a.heClassicEvenPrintedConditions_iff_sectionConditions
          (m := m + 4) (n := 2 * k + 2) (by omega) ⟨k + 1, by omega⟩
            (by omega)).mp ⟨hConditions.initial_orders, hEven'⟩
      have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
          (2 * k + 2) :=
        Lattice.ambientlyNUniversal_of_rank_add_three_le (2 * k + 2) (by
          omega)
      exact (a.he2022ClassicTheorem41 (m := m + 1) (t := k) (by omega)).mpr
        ⟨hClassic, hAmbient, hSection⟩
    · rcases hOdd.parity with ⟨r, hr⟩
      omega

/-- The odd half of Theorem 1.1 once the source rank is written as `m+5`. -/
theorem he2022ClassicTheorem11Odd_rankAtLeastFive
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 5))
    (hClassic : Lattice.IsClassicIntegral q L) :
    Lattice.IsClassicNUniversal.{u, v, u} q L (2 * k + 3) ↔
      a.HeClassicTheorem11Conditions (2 * k + 3) := by
  letI : Module.Finite K V := L.moduleFinite
  have hfinrank : finrank K V = m + 5 :=
    a.toBONG.length_eq_finrank.symm
  constructor
  · intro hUniversal
    have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q
        (2 * k + 3) :=
      isClassicNUniversal_ambient (q := q) (L := L) hUniversal
    have hRank : 2 * k + 6 ≤ m + 5 :=
      (Lattice.ambientlyOddUniversal_rank_classification
        (q := q) k).mp hAmbient |>.trans_eq hfinrank
    have hSection :
        a.HeClassicOddSectionConditions (2 * k + 3) (by omega) (by omega) :=
      ((a.he2022ClassicTheorem51 (m := m) (k := k) hRank).mp
        hUniversal).2
    have hPrinted :=
      (a.heClassicOddPrintedConditions_iff_sectionConditions
        (m := m + 4) (n := 2 * k + 3) (by omega) ⟨k + 1, by omega⟩
          (by omega) hClassic).mpr hSection
    exact
      { rank_bound := hRank
        initial_orders := hPrinted.1
        parity_branch := Or.inr hPrinted.2 }
  · intro hConditions
    have hRank := hConditions.rank_bound
    rcases hConditions.parity_branch with hEven | hOdd
    · rcases hEven.parity with ⟨r, hr⟩
      omega
    · have hOdd' : HeClassicOddConditions a (2 * k + 3) (by omega) := by
        simpa using hOdd
      have hSection :
          a.HeClassicOddSectionConditions (2 * k + 3) (by omega) (by omega) :=
        (a.heClassicOddPrintedConditions_iff_sectionConditions
          (m := m + 4) (n := 2 * k + 3) (by omega) ⟨k + 1, by omega⟩
            (by omega) hClassic).mp ⟨hConditions.initial_orders, hOdd'⟩
      exact (a.he2022ClassicTheorem51 (m := m) (k := k)
        hConditions.rank_bound).mpr ⟨hClassic, hSection⟩

/-- Theorem 1.1 for sources of rank at least five. -/
theorem he2022ClassicTheorem11_rankAtLeastFive
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m n : Nat} (a : GoodBONG q L (m + 5))
    (hn : 2 ≤ n) (hClassic : Lattice.IsClassicIntegral q L) :
    a.HeClassicTheorem11Statement.{u, v, u} n hn hClassic := by
  unfold HeClassicTheorem11Statement
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · rcases hnEven with ⟨r, hr⟩
    cases r with
    | zero => omega
    | succ k =>
        have hnValue : n = 2 * k + 2 := by omega
        subst n
        simpa only [show k + 1 + (k + 1) = 2 * k + 2 by omega] using
          (a.he2022ClassicTheorem11Even_rankAtLeastFive (k := k) hClassic)
  · rcases hnOdd with ⟨r, hr⟩
    cases r with
    | zero => omega
    | succ k =>
        have hnValue : n = 2 * k + 3 := by omega
        subst n
        exact a.he2022ClassicTheorem11Odd_rankAtLeastFive hClassic

/-- He (2024), Theorem 1.1, for an arbitrary source rank.  The split
quaternary ambient exception is eliminated by the binary-rank clause in
`J2_E`, so classic universality has exactly the stable rank range printed in
the paper. -/
theorem he2022ClassicTheorem11
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m n : Nat} (a : GoodBONG q L m)
    (hn : 2 ≤ n) (hClassic : Lattice.IsClassicIntegral q L) :
    a.HeClassicTheorem11Statement.{u, v, u} n hn hClassic := by
  letI : Module.Finite K V := L.moduleFinite
  by_cases hmFive : 5 ≤ m
  · obtain ⟨d, hd⟩ : ∃ d : Nat, m = d + 5 :=
      ⟨m - 5, by omega⟩
    subst m
    exact a.he2022ClassicTheorem11_rankAtLeastFive hn hClassic
  · unfold HeClassicTheorem11Statement
    constructor
    · intro hUniversal
      exfalso
      have hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q n :=
        isClassicNUniversal_ambient (q := q) (L := L) hUniversal
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
            have hUniversalEven :
                Lattice.IsClassicNUniversal.{u, v, u} q L (2 * k + 2) := by
              rw [← hnValue]
              exact hUniversal
            rcases (Lattice.ambientlyEvenUniversal_rank_classification
              (q := q) k).mp hAmbientEven with hStable | hExceptional
            · omega
            · rcases hExceptional with ⟨hk, hFour, _⟩
              subst k
              have hmFour : m = 4 := by omega
              subst m
              let aFour : GoodBONG q L 4 := a.castLength hFour
              have hSection :=
                ((aFour.he2022ClassicTheorem41 (m := 0) (t := 0) (by omega)).mp
                  hUniversalEven).2.2
              have hImpossible := hSection.j2.2.2 rfl
              omega
      · rcases hnOdd with ⟨r, hr⟩
        cases r with
        | zero => omega
        | succ k =>
            have hnValue : n = 2 * k + 3 := by omega
            have hAmbientOdd :
                Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) := by
              rw [← hnValue]
              exact hAmbient
            have hStable :=
              (Lattice.ambientlyOddUniversal_rank_classification
                (q := q) k).mp hAmbientOdd
            omega
    · intro hConditions
      exfalso
      exact hmFive (by
        have hRank := hConditions.rank_bound
        omega)

end BONG.GoodBONG

end Bong
