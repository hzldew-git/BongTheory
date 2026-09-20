/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma39

/-!
# He (2024), Corollary 3.10

The paper's order condition is assembled pointwise from Lemma 3.1(i)--(ii).
The two even-rank alternatives are kept separate as useful exact endpoints
and then combined in the literal disjunctive statement.
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

/-- Corollary 3.10(i), first alternative: even target rank and
`R_(n+1)=0`. -/
theorem he2022ClassicCorollary310i_of_nextOrderZero {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (2 * t + 2))
    (hRank : 2 * t + 1 <= m + 1)
    (hNextBound : 2 * t + 2 < m + 2)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨2 * t + 2, hNextBound⟩ = 0) :
    forall i : Fin (2 * t + 2),
      a.HeClassicOrderConditionAt b hRank i := by
  intro i
  by_cases hiEven : Even i.val
  · exact a.he2022ClassicLemma31i b hRank hBClassic i hiEven
      (hzero _ i.isLt)
  · have hiPositive : 0 < i.val := by
      by_contra hi
      have hiZero : i.val = 0 := by omega
      exact hiEven ⟨0, by omega⟩
    have hiLarge : i.val + 1 < m + 2 := by
      have := i.isLt
      omega
    apply a.he2022ClassicLemma31ii b hRank hBClassic i hiPositive
      hiLarge
    have hcurrent : a.order ⟨i.val, by omega⟩ = 0 :=
      hzero _ i.isLt
    have hfollowing : a.order ⟨i.val + 1, hiLarge⟩ = 0 := by
      by_cases hlt : i.val + 1 < 2 * t + 2
      · exact hzero _ hlt
      · have heq : i.val + 1 = 2 * t + 2 := by
          have := i.isLt
          omega
        have hindex : (⟨i.val + 1, hiLarge⟩ : Fin (m + 2)) =
            ⟨2 * t + 2, hNextBound⟩ := by
          apply Fin.ext
          exact heq
        rw [hindex]
        exact hnext
    rw [hcurrent, hfollowing, add_zero]

/-- Corollary 3.10(i), second alternative: even target rank and
nonnegative final target order. -/
theorem he2022ClassicCorollary310i_of_targetLastNonnegative {m : Nat}
    (t : Nat) (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (2 * t + 2))
    (hRank : 2 * t + 1 <= m + 1)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.order k = 0)
    (hSn : 0 <= b.order ⟨2 * t + 1, by omega⟩) :
    forall i : Fin (2 * t + 2),
      a.HeClassicOrderConditionAt b hRank i := by
  intro i
  by_cases hiLast : i.val = 2 * t + 1
  · left
    have hsource : a.order ⟨i.val, by
        have := i.isLt
        omega⟩ = 0 := hzero _ i.isLt
    rw [hsource]
    convert hSn using 1
    apply congrArg b.order
    apply Fin.ext
    exact hiLast
  · by_cases hiEven : Even i.val
    · exact a.he2022ClassicLemma31i b hRank hBClassic i hiEven
        (hzero _ i.isLt)
    · have hiPositive : 0 < i.val := by
        by_contra hi
        have hiZero : i.val = 0 := by omega
        exact hiEven ⟨0, by omega⟩
      have hiTargetNext : i.val + 1 < 2 * t + 2 := by
        have := i.isLt
        omega
      have hiLarge : i.val + 1 < m + 2 := by omega
      apply a.he2022ClassicLemma31ii b hRank hBClassic i hiPositive
        hiLarge
      rw [hzero _ i.isLt, hzero _ hiTargetNext, add_zero]

/-- Literal disjunctive form of Corollary 3.10(i). -/
theorem he2022ClassicCorollary310i {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (2 * t + 2))
    (hRank : 2 * t + 1 <= m + 1)
    (hNextBound : 2 * t + 2 < m + 2)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 2), k.val < 2 * t + 2 ->
      a.order k = 0)
    (hbranch : a.order ⟨2 * t + 2, hNextBound⟩ = 0 ∨
      0 <= b.order ⟨2 * t + 1, by omega⟩) :
    forall i : Fin (2 * t + 2),
      a.HeClassicOrderConditionAt b hRank i := by
  rcases hbranch with hnext | hSn
  · exact a.he2022ClassicCorollary310i_of_nextOrderZero t b hRank
      hNextBound hBClassic hzero hnext
  · exact a.he2022ClassicCorollary310i_of_targetLastNonnegative t b
      hRank hBClassic hzero hSn

/-- Corollary 3.10(ii): at odd target rank, vanishing of the first `n`
source orders gives condition (i) at every target index. -/
theorem he2022ClassicCorollary310ii {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 2))
    (b : GoodBONG r M (2 * t + 3))
    (hRank : 2 * t + 2 <= m + 1)
    (hBClassic : Lattice.IsClassicIntegral r M)
    (hzero : forall k : Fin (m + 2), k.val < 2 * t + 3 ->
      a.order k = 0) :
    forall i : Fin (2 * t + 3),
      a.HeClassicOrderConditionAt b hRank i := by
  intro i
  by_cases hiEven : Even i.val
  · exact a.he2022ClassicLemma31i b hRank hBClassic i hiEven
      (hzero _ i.isLt)
  · have hiPositive : 0 < i.val := by
      by_contra hi
      have hiZero : i.val = 0 := by omega
      exact hiEven ⟨0, by omega⟩
    have hiNext : i.val + 1 < 2 * t + 3 := by
      have hiOdd := Nat.not_even_iff_odd.mp hiEven
      rcases hiOdd with ⟨s, hs⟩
      have := i.isLt
      omega
    have hiLarge : i.val + 1 < m + 2 := by omega
    apply a.he2022ClassicLemma31ii b hRank hBClassic i hiPositive
      hiLarge
    rw [hzero _ i.isLt, hzero _ hiNext, add_zero]

end BONG.GoodBONG

end Bong
