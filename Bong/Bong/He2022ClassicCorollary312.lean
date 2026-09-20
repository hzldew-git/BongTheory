/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary311

/-!
# He (2024), Corollary 3.12

This file assembles the publisher's two-defect form of condition (iii).
At paper index two, where the endpoint form of Lemma 3.1(iv) does not
contain its second essentiality comparison, Lemma 3.1(iii) supplies the
required implication directly.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.GoodBONG

/-- Corollary 3.12(i), even target rank: condition (iii) holds through
paper index `n - 2`. -/
theorem he2022ClassicCorollary312iEven {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (hSourceRank : 2 * t + 3 <= m + 3)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (i : CentralRepresentationIndex (m + 3) (2 * t + 2))
    (hiRange : i.val + 2 <= 2 * t + 2) :
    a.HeClassicPublishedCentralConditionAt b i := by
  by_cases hiEven : Even i.val
  · apply a.he2022ClassicLemma31iiiPublished b hBClassic i hiEven
    apply hzero
    change i.val < 2 * t + 2
    omega
  · have hiOdd := Nat.not_even_iff_odd.mp hiEven
    have hiThree : 2 < i.val := by
      rcases hiOdd with ⟨s, hs⟩
      have := i.one_lt
      omega
    have hiNext : i.val + 1 < m + 3 := by omega
    apply a.he2022ClassicLemma31ivPublished_corrected b hBClassic i
      hiThree hiNext
    rw [hzero ⟨i.val, i.lt_large⟩ (by
          change i.val < 2 * t + 2
          omega),
        hzero ⟨i.val + 1, hiNext⟩ (by
          change i.val + 1 < 2 * t + 2
          omega), add_zero]

/-- Corollary 3.12(i), odd target rank: condition (iii) holds through
paper index `n - 1`. -/
theorem he2022ClassicCorollary312iOdd {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hSourceRank : 2 * t + 4 <= m + 4)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 4), k.val < 2 * t + 3 ->
      a.order k = 0)
    (i : CentralRepresentationIndex (m + 4) (2 * t + 3))
    (hiRange : i.val + 1 <= 2 * t + 3) :
    a.HeClassicPublishedCentralConditionAt b i := by
  by_cases hiEven : Even i.val
  · apply a.he2022ClassicLemma31iiiPublished b hBClassic i hiEven
    apply hzero
    change i.val < 2 * t + 3
    omega
  · have hiOdd := Nat.not_even_iff_odd.mp hiEven
    have hiThree : 2 < i.val := by
      rcases hiOdd with ⟨s, hs⟩
      have := i.one_lt
      omega
    have hiSourcePair : i.val + 1 < 2 * t + 3 := by
      rcases hiOdd with ⟨s, hs⟩
      omega
    have hiNext : i.val + 1 < m + 4 := by omega
    apply a.he2022ClassicLemma31ivPublished_corrected b hBClassic i
      hiThree hiNext
    rw [hzero ⟨i.val, i.lt_large⟩ (by
          change i.val < 2 * t + 3
          omega),
        hzero ⟨i.val + 1, hiNext⟩ (by
          change i.val + 1 < 2 * t + 3
          exact hiSourcePair), add_zero]

/-- Corollary 3.12(ii), first assertion: at even target rank and
`R_(n+1)=0`, condition (iii) holds through paper index `n`. -/
theorem he2022ClassicCorollary312iiInitial {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 3))
    (b : GoodBONG r M (2 * t + 2))
    (hSourceRank : 2 * t + 3 <= m + 3)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 3), k.val < 2 * t + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (i : CentralRepresentationIndex (m + 3) (2 * t + 2))
    (hiRange : i.val <= 2 * t + 2) :
    a.HeClassicPublishedCentralConditionAt b i := by
  have hzeroExtended : forall k : Fin (m + 3),
      k.val <= 2 * t + 2 -> a.order k = 0 := by
    intro k hk
    by_cases hlt : k.val < 2 * t + 2
    · exact hzero k hlt
    · have heq : k.val = 2 * t + 2 := by omega
      have hindex : k = (⟨2 * t + 2, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        exact heq
      simpa only [hindex] using hnext
  by_cases hiEven : Even i.val
  · apply a.he2022ClassicLemma31iiiPublished b hBClassic i hiEven
    apply hzeroExtended
    change i.val <= 2 * t + 2
    exact hiRange
  · have hiOdd := Nat.not_even_iff_odd.mp hiEven
    have hiThree : 2 < i.val := by
      rcases hiOdd with ⟨s, hs⟩
      have := i.one_lt
      omega
    have hiPair : i.val + 1 <= 2 * t + 2 := by
      rcases hiOdd with ⟨s, hs⟩
      omega
    have hiNext : i.val + 1 < m + 3 := by omega
    apply a.he2022ClassicLemma31ivPublished_corrected b hBClassic i
      hiThree hiNext
    rw [hzeroExtended ⟨i.val, i.lt_large⟩ (by
          change i.val <= 2 * t + 2
          exact hiRange),
        hzeroExtended ⟨i.val + 1, hiNext⟩ (by
          change i.val + 1 <= 2 * t + 2
          exact hiPair), add_zero]

/-- Corollary 3.12(ii), second assertion: the signed-prefix equality and
`alpha_(n+1)=1` extend condition (iii) to paper index `n + 1`. -/
theorem he2022ClassicCorollary312ii {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 2))
    (hSourceRank : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 4), k.val < 2 * t + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨2 * t + 2, by omega⟩ = 0)
    (halphaNext : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (i : CentralRepresentationIndex (m + 4) (2 * t + 2)) :
    a.HeClassicPublishedCentralConditionAt b i := by
  by_cases hiInitial : i.val <= 2 * t + 2
  · exact a.he2022ClassicCorollary312iiInitial (m := m + 1) t b
      (by omega) hBClassic hzero hnext i hiInitial
  · have hiLast : i.val = 2 * t + 3 := by
      have := i.le_small_succ
      omega
    have hterminal := a.he2022ClassicLemma38LongSource t b hSourceRank
      hAClassic hBClassic
      (hzero ⟨2 * t + 1, by omega⟩ (by
        change 2 * t + 1 < 2 * t + 2
        omega))
      hnext halphaNext hSourceEquality
    let terminalIndex : CentralRepresentationIndex (m + 4) (2 * t + 2) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    have hiEq : i = terminalIndex := by
      cases i with
      | mk val hOne hLarge hSmall =>
          simp only [terminalIndex]
          cases hiLast
          rfl
    rw [hiEq]
    exact hterminal

/-- Corollary 3.12(iii), first assertion: at odd target rank the
signed-prefix equality gives condition (iii) through paper index `n`. -/
theorem he2022ClassicCorollary312iiiInitial {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hSourceRank : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 4), k.val < 2 * t + 3 ->
      a.order k = 0)
    (halpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (i : CentralRepresentationIndex (m + 4) (2 * t + 3))
    (hiRange : i.val <= 2 * t + 3) :
    a.HeClassicPublishedCentralConditionAt b i := by
  by_cases hiBefore : i.val < 2 * t + 3
  · exact a.he2022ClassicCorollary312iOdd t b hSourceRank hBClassic
      hzero i (by omega)
  · have hiLast : i.val = 2 * t + 3 := by omega
    have hterminal := a.he2022ClassicLemma39iLongSource t b hSourceRank
      hAClassic hBClassic
      (hzero ⟨2 * t + 1, by omega⟩ (by
        change 2 * t + 1 < 2 * t + 3
        omega))
      (hzero ⟨2 * t + 2, by omega⟩ (by
        change 2 * t + 2 < 2 * t + 3
        omega))
      halpha hSourceEquality
    let terminalIndex : CentralRepresentationIndex (m + 4) (2 * t + 3) :=
      { val := 2 * t + 3
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    have hiEq : i = terminalIndex := by
      cases i with
      | mk val hOne hLarge hSmall =>
          simp only [terminalIndex]
          cases hiLast
          rfl
    rw [hiEq]
    exact hterminal

/-- Corollary 3.12(iii), second assertion: `R_(n+1)=0` and
`R_(n+2) in {0,1}` extend condition (iii) through `n + 1`. -/
theorem he2022ClassicCorollary312iii {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (2 * t + 3))
    (hSourceRank : 2 * t + 5 <= m + 5)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 5), k.val < 2 * t + 3 ->
      a.order k = 0)
    (halpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)))
    (hnext : a.order ⟨2 * t + 3, by omega⟩ = 0)
    (hnextTwo : a.order ⟨2 * t + 4, by omega⟩ = 0 ∨
      a.order ⟨2 * t + 4, by omega⟩ = 1)
    (i : CentralRepresentationIndex (m + 5) (2 * t + 3)) :
    a.HeClassicPublishedCentralConditionAt b i := by
  by_cases hiInitial : i.val <= 2 * t + 3
  · exact a.he2022ClassicCorollary312iiiInitial (m := m + 1) t b
      (by omega) hAClassic hBClassic hzero halpha hSourceEquality i hiInitial
  · have hiLast : i.val = 2 * t + 4 := by
      have := i.le_small_succ
      omega
    have hterminal := a.he2022ClassicLemma39iiLongSource t b hSourceRank
      hAClassic hBClassic
      (hzero ⟨2 * t + 1, by omega⟩ (by
        change 2 * t + 1 < 2 * t + 3
        omega))
      (hzero ⟨2 * t + 2, by omega⟩ (by
        change 2 * t + 2 < 2 * t + 3
        omega))
      halpha hSourceEquality hnext hnextTwo
    let terminalIndex : CentralRepresentationIndex (m + 5) (2 * t + 3) :=
      { val := 2 * t + 4
        one_lt := by omega
        lt_large := by omega
        le_small_succ := by omega }
    have hiEq : i = terminalIndex := by
      cases i with
      | mk val hOne hLarge hSmall =>
          simp only [terminalIndex]
          cases hiLast
          rfl
    rw [hiEq]
    exact hterminal

end BONG.GoodBONG

end Bong
