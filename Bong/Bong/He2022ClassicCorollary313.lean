/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary312

/-!
# He (2024), Corollary 3.13

Parts (i) and (ii) are literal formalizations of the publisher statement.
For part (iii), Lemma 3.1(v) also needs the preceding gap
`R_(n+2)-R_(n+1) <= 2e` at paper index `n`; the publisher states only the
next gap.  The theorem below exposes this missing premise rather than
silently assuming it.
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

private theorem he2022ClassicCorollary313EarlyGap {s m : Nat}
    (a : GoodBONG q L (m + 3))
    (hSourceRank : s + 3 <= m + 3)
    (hzero : forall k : Fin (m + 3), k.val < s + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨s + 2, by omega⟩ = 0 ∨
      a.order ⟨s + 2, by omega⟩ = 1)
    (i : LongRepresentationIndex (m + 3) (s + 2))
    (hiRange : i.val + 1 <= s + 2) :
    a.order ⟨i.val + 1, i.succ_lt_large⟩ -
        a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ <=
      2 * (ramificationIndex K : Int) := by
  have hcurrent :
      a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ = 0 := by
    apply hzero
    change i.val < s + 2
    omega
  have hnextValue :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ = 0 ∨
        a.order ⟨i.val + 1, i.succ_lt_large⟩ = 1 := by
    by_cases hlt : i.val + 1 < s + 2
    · exact Or.inl (hzero _ hlt)
    · have heq : i.val + 1 = s + 2 := by omega
      have hindex : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 3)) =
          ⟨s + 2, by omega⟩ := by
        apply Fin.ext
        exact heq
      simpa only [hindex] using hnext
  have hePositive : 0 < ramificationIndex K :=
    ramificationIndex_pos (K := K)
  rcases hnextValue with hnextZero | hnextOne
  · rw [hcurrent, hnextZero]
    omega
  · rw [hcurrent, hnextOne]
    omega

/-- Corollary 3.13(i): when the source rank is `n + 1`, condition (iv)
holds through paper index `n - 1`. -/
theorem he2022ClassicCorollary313i (s : Nat)
    (a : GoodBONG q L (s + 3))
    (b : GoodBONG r M (s + 2))
    (hzero : forall k : Fin (s + 3), k.val < s + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨s + 2, by omega⟩ = 0 ∨
      a.order ⟨s + 2, by omega⟩ = 1)
    (i : LongRepresentationIndex (s + 3) (s + 2))
    (hiRange : i.val + 1 <= s + 2) :
    a.HeClassicLongConditionAt b i := by
  apply a.he2022ClassicLemma31v b i
  exact a.he2022ClassicCorollary313EarlyGap (m := s) (s := s)
    (by omega) hzero hnext i hiRange

/-- Corollary 3.13(ii): when the source rank is `n + 2`, the displayed
terminal gap extends condition (iv) through paper index `n`. -/
theorem he2022ClassicCorollary313ii (s : Nat)
    (a : GoodBONG q L (s + 4))
    (b : GoodBONG r M (s + 2))
    (hzero : forall k : Fin (s + 4), k.val < s + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨s + 2, by omega⟩ = 0 ∨
      a.order ⟨s + 2, by omega⟩ = 1)
    (hgap : a.order ⟨s + 3, by omega⟩ -
        a.order ⟨s + 2, by omega⟩ <=
      2 * (ramificationIndex K : Int))
    (i : LongRepresentationIndex (s + 4) (s + 2))
    (hiRange : i.val <= s + 2) :
    a.HeClassicLongConditionAt b i := by
  apply a.he2022ClassicLemma31v b i
  by_cases hiLast : i.val = s + 2
  · have hleft :
        (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (s + 4)) =
          ⟨s + 2, by omega⟩ := by
      apply Fin.ext
      exact hiLast
    have hright : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (s + 4)) =
        ⟨s + 3, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = s + 3
      omega
    rw [hleft, hright]
    exact hgap
  · exact a.he2022ClassicCorollary313EarlyGap (m := s + 1) (s := s)
      (by omega) hzero hnext i (by omega)

/-- Corrected form of Corollary 3.13(iii).  The explicit `hPriorGap`
is the premise needed to apply Lemma 3.1(v) at paper index `n`; the
publisher's `hLastGap` then handles paper index `n + 1`. -/
theorem he2022ClassicCorollary313iii_with_prior_gap {m : Nat} (s : Nat)
    (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (s + 2))
    (hSourceRank : s + 5 <= m + 5)
    (hzero : forall k : Fin (m + 5), k.val < s + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨s + 2, by omega⟩ = 0 ∨
      a.order ⟨s + 2, by omega⟩ = 1)
    (hPriorGap : a.order ⟨s + 3, by omega⟩ -
        a.order ⟨s + 2, by omega⟩ <=
      2 * (ramificationIndex K : Int))
    (hLastGap : a.order ⟨s + 4, by omega⟩ -
        a.order ⟨s + 3, by omega⟩ <=
      2 * (ramificationIndex K : Int))
    (i : LongRepresentationIndex (m + 5) (s + 2)) :
    a.HeClassicLongConditionAt b i := by
  apply a.he2022ClassicLemma31v b i
  by_cases hiEarly : i.val + 1 <= s + 2
  · exact a.he2022ClassicCorollary313EarlyGap (m := m + 2) (s := s)
      (by omega) hzero hnext i hiEarly
  · by_cases hiMiddle : i.val = s + 2
    · have hleft :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (m + 5)) =
            ⟨s + 2, by omega⟩ := by
        apply Fin.ext
        exact hiMiddle
      have hright : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 5)) =
          ⟨s + 3, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = s + 3
        omega
      rw [hleft, hright]
      exact hPriorGap
    · have hiLast : i.val = s + 3 := by
        have := i.le_small_succ
        omega
      have hleft :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (m + 5)) =
            ⟨s + 3, by omega⟩ := by
        apply Fin.ext
        exact hiLast
      have hright : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 5)) =
          ⟨s + 4, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = s + 4
        omega
      rw [hleft, hright]
      exact hLastGap

/-- A source-valid specialization of Corollary 3.13(iii): if both
`R_(n+1)` and `R_(n+2)` lie in `{0,1}`, the omitted preceding gap is
automatic because the dyadic ramification index is positive. -/
theorem he2022ClassicCorollary313iii_of_nextTwo_zeroOrOne {m : Nat}
    (s : Nat) (a : GoodBONG q L (m + 5))
    (b : GoodBONG r M (s + 2))
    (hSourceRank : s + 5 <= m + 5)
    (hzero : forall k : Fin (m + 5), k.val < s + 2 ->
      a.order k = 0)
    (hnext : a.order ⟨s + 2, by omega⟩ = 0 ∨
      a.order ⟨s + 2, by omega⟩ = 1)
    (hnextTwo : a.order ⟨s + 3, by omega⟩ = 0 ∨
      a.order ⟨s + 3, by omega⟩ = 1)
    (hLastGap : a.order ⟨s + 4, by omega⟩ -
        a.order ⟨s + 3, by omega⟩ <=
      2 * (ramificationIndex K : Int))
    (i : LongRepresentationIndex (m + 5) (s + 2)) :
    a.HeClassicLongConditionAt b i := by
  have hePositive : 0 < ramificationIndex K :=
    ramificationIndex_pos (K := K)
  have hPriorGap : a.order ⟨s + 3, by omega⟩ -
        a.order ⟨s + 2, by omega⟩ <=
      2 * (ramificationIndex K : Int) := by
    rcases hnext with hNextZero | hNextOne
    · rcases hnextTwo with hNextTwoZero | hNextTwoOne
      · rw [hNextZero, hNextTwoZero]
        omega
      · rw [hNextZero, hNextTwoOne]
        omega
    · rcases hnextTwo with hNextTwoZero | hNextTwoOne
      · rw [hNextOne, hNextTwoZero]
        omega
      · rw [hNextOne, hNextTwoOne]
        omega
  exact a.he2022ClassicCorollary313iii_with_prior_gap s b hSourceRank
    hzero hnext hPriorGap hLastGap i

end BONG.GoodBONG

end Bong
