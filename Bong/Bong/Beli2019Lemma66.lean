/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ExtremalDifference
import Bong.Bong.Beli2009TwoAdic

/-!
# Beli (2019), Lemma 6.6

Equal order entries at endpoints of the same parity force the whole interval
to have one parity, and every internal forward gap is at most `2e`.  The
opposite-parity version gives an even closed interval sum.
-/

namespace Bong

open Dyadic
open scoped BigOperators

universe u v

/-- Finite sums preserve congruence modulo two, without requiring the
big-operator congruence module. -/
theorem int_modEq_two_sum_Ico (f g : Nat → Int) {i j : Nat} (hij : i ≤ j)
    (h : ∀ k, i ≤ k → k < j → Int.ModEq 2 (f k) (g k)) :
    Int.ModEq 2 (∑ k ∈ Finset.Ico i j, f k)
      (∑ k ∈ Finset.Ico i j, g k) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
      rw [Finset.sum_Ico_succ_top hij, Finset.sum_Ico_succ_top hij]
      exact (ih fun k hik hkj ↦ h k hik (hkj.trans (Nat.lt_succ_self j))).add
        (h j hij (Nat.lt_succ_self j))

/-- An even difference is the same parity congruence used in the paper. -/
theorem int_modEq_two_of_even_sub {a b : Int} (h : Even (a - b)) :
    Int.ModEq 2 a b := by
  rcases h with ⟨c, hc⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨-c, ?_⟩
  omega

/-- An even difference makes the sum of the same two integers even. -/
theorem even_add_of_even_sub {a b : Int} (h : Even (b - a)) :
    Even (a + b) := by
  rcases h with ⟨c, hc⟩
  refine ⟨a + c, ?_⟩
  omega

namespace BeliOrderSequence

/-- The sum over the closed, zero-based interval `[i, j]`. -/
def closedSegmentSum {n : Nat} (x : BeliOrderSequence n Int)
    (i j : Nat) : Int :=
  ∑ k ∈ Finset.Ico i (j + 1), x.entryOrZero k

@[simp]
theorem closedSegmentSum_pair {n : Nat} (x : BeliOrderSequence n Int)
    (i : Nat) :
    x.closedSegmentSum i (i + 1) =
      x.entryOrZero i + x.entryOrZero (i + 1) := by
  simp [closedSegmentSum, Finset.sum_Ico_succ_top]

theorem closedSegmentSum_add_two {n : Nat} (x : BeliOrderSequence n Int)
    (i j : Nat) (hij : i ≤ j) :
    x.closedSegmentSum i (j + 2) = x.closedSegmentSum i j +
      x.entryOrZero (j + 1) + x.entryOrZero (j + 2) := by
  rw [closedSegmentSum, closedSegmentSum]
  rw [show j + 2 + 1 = (j + 2) + 1 by omega,
    Finset.sum_Ico_succ_top (by omega),
    Finset.sum_Ico_succ_top (by omega)]

end BeliOrderSequence

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- A nonpositive adjacent order gap in a good BONG is even. -/
theorem orderGap_even_of_nonpositive
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hnonpositive : b.orderGap i ≤ 0) : Even (b.orderGap i) := by
  by_cases hzero : b.orderGap i = 0
  · rw [hzero]
    exact ⟨0, by simp⟩
  · exact b.orderGap_even_of_negative i (by omega)

/-- The complete conclusions of Beli (2019), Lemma 6.6(i). -/
structure Lemma66EqualEndpointConsequences
    (b : GoodBONG q L (n + 1)) (i j : Fin (n + 1)) : Prop where
  order_modEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    Int.ModEq 2 (b.order k) (b.order i)
  gap_le (k : Fin n) (hik : i.1 ≤ k.1) (hkj : k.1 < j.1) :
    b.orderGap k ≤ 2 * (ramificationIndex K : Int)
  closedSum_modEq : Int.ModEq 2
    (b.orderSequence.closedSegmentSum i.1 j.1) (b.order i)

/-- Beli (2019), Lemma 6.6(i), in zero-based indexing. -/
theorem beli2019Lemma66_i
    (b : GoodBONG q L (n + 1)) (i j : Fin (n + 1))
    (hij : i ≤ j) (hijParity : Even (j.1 - i.1))
    (heq : b.order i = b.order j) :
    Lemma66EqualEndpointConsequences b i j := by
  have hsameParityOrder (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j)
      (hkParity : Even (k.1 - i.1)) : b.order k = b.order i := by
    have hleft := b.orderSequence.entryOrZero_le_of_evenGap
      i.1 k.1 (by exact hik) k.isLt hkParity
    have hjkParity : Even (j.1 - k.1) := by
      rcases hijParity with ⟨r, hr⟩
      rcases hkParity with ⟨s, hs⟩
      refine ⟨r - s, ?_⟩
      omega
    have hright := b.orderSequence.entryOrZero_le_of_evenGap
      k.1 j.1 (by exact hkj) j.isLt hjkParity
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence k.isLt] at hleft
    change b.order i ≤ b.order k at hleft
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence k.isLt,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence j.isLt] at hright
    change b.order k ≤ b.order j at hright
    exact le_antisymm (hright.trans_eq heq.symm) hleft
  have horderMod (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
      Int.ModEq 2 (b.order k) (b.order i) := by
    rcases Nat.even_or_odd (k.1 - i.1) with hkEven | hkOdd
    · rw [hsameParityOrder k hik hkj hkEven]
    · rcases hkOdd with ⟨d, hd⟩
      have hikStrict : i < k := by
        change i.1 < k.1
        omega
      have hkjStrict : k < j := by
        rcases hijParity with ⟨r, hr⟩
        change k.1 < j.1
        omega
      let previous : Fin (n + 1) := ⟨k.1 - 1, by omega⟩
      let next : Fin (n + 1) := ⟨k.1 + 1, by omega⟩
      have hpreviousParity : Even (previous.1 - i.1) := by
        refine ⟨d, ?_⟩
        simp only [previous]
        omega
      have hnextParity : Even (next.1 - i.1) := by
        refine ⟨d + 1, ?_⟩
        simp only [next]
        omega
      have hprevious := hsameParityOrder previous
        (by change i.1 ≤ previous.1; simp only [previous]; omega)
        (by change previous.1 ≤ j.1; simp only [previous]; omega)
        hpreviousParity
      have hnext := hsameParityOrder next
        (by change i.1 ≤ next.1; simp only [next]; omega)
        (by change next.1 ≤ j.1; simp only [next]; omega)
        hnextParity
      by_cases hki : b.order k ≤ b.order i
      · let gap : Fin n := ⟨k.1 - 1, by omega⟩
        have hgapSucc : gap.succ = k := by
          apply Fin.ext
          change gap.1 + 1 = k.1
          simp only [gap]
          omega
        have hgapCast : gap.castSucc = previous := by
          apply Fin.ext
          rfl
        have hgapNonpositive : b.orderGap gap ≤ 0 := by
          unfold orderGap
          rw [hgapSucc, hgapCast, hprevious]
          omega
        have hgapEven := b.orderGap_even_of_nonpositive gap hgapNonpositive
        unfold orderGap at hgapEven
        rw [hgapSucc, hgapCast, hprevious] at hgapEven
        exact int_modEq_two_of_even_sub hgapEven
      · let gap : Fin n := ⟨k.1, by omega⟩
        have hgapSucc : gap.succ = next := by
          apply Fin.ext
          rfl
        have hgapCast : gap.castSucc = k := by
          apply Fin.ext
          rfl
        have hgapNonpositive : b.orderGap gap ≤ 0 := by
          unfold orderGap
          rw [hgapSucc, hgapCast, hnext]
          omega
        have hgapEven := b.orderGap_even_of_nonpositive gap hgapNonpositive
        unfold orderGap at hgapEven
        rw [hgapSucc, hgapCast, hnext] at hgapEven
        exact (int_modEq_two_of_even_sub hgapEven).symm
  refine {
    order_modEq := horderMod
    gap_le := ?_
    closedSum_modEq := ?_ }
  · intro k hik hkj
    rcases Nat.even_or_odd (k.1 - i.1) with hkEven | hkOdd
    · rcases hijParity with ⟨r, hr⟩
      rcases hkEven with ⟨s, hs⟩
      have hkTwo : k.1 + 2 ≤ j.1 := by omega
      let nextGap : Fin n := ⟨k.1 + 1, by omega⟩
      let far : Fin (n + 1) := ⟨k.1 + 2, by omega⟩
      have hkCastParity : Even (k.castSucc.1 - i.1) := by
        change Even (k.1 - i.1)
        exact ⟨s, hs⟩
      have hkOrder := hsameParityOrder k.castSucc
        (by change i.1 ≤ k.1; exact hik)
        (by change k.1 ≤ j.1; omega) hkCastParity
      have hfarParity : Even (far.1 - i.1) := by
        refine ⟨s + 1, ?_⟩
        simp only [far]
        omega
      have hfarOrder := hsameParityOrder far
        (by change i.1 ≤ far.1; simp only [far]; omega)
        (by change far.1 ≤ j.1; simp only [far]; exact hkTwo)
        hfarParity
      have hmiddle : k.succ = nextGap.castSucc := by
        apply Fin.ext
        rfl
      have hfar : nextGap.succ = far := by
        apply Fin.ext
        rfl
      have hzero : b.orderGap k + b.orderGap nextGap = 0 := by
        unfold orderGap
        rw [hmiddle, hfar, hkOrder, hfarOrder]
        ring
      have hlower := b.orderGap_ge_neg_two_mul_e nextGap
      omega
    · rcases hkOdd with ⟨s, hs⟩
      have hikStrict : i.1 < k.1 := by omega
      let previousGap : Fin n := ⟨k.1 - 1, by omega⟩
      let previous : Fin (n + 1) := ⟨k.1 - 1, by omega⟩
      let next : Fin (n + 1) := ⟨k.1 + 1, by omega⟩
      have hpreviousParity : Even (previous.1 - i.1) := by
        refine ⟨s, ?_⟩
        simp only [previous]
        omega
      have hnextParity : Even (next.1 - i.1) := by
        refine ⟨s + 1, ?_⟩
        simp only [next]
        omega
      have hpreviousOrder := hsameParityOrder previous
        (by change i.1 ≤ previous.1; simp only [previous]; omega)
        (by change previous.1 ≤ j.1; simp only [previous]; omega)
        hpreviousParity
      have hnextOrder := hsameParityOrder next
        (by change i.1 ≤ next.1; simp only [next]; omega)
        (by change next.1 ≤ j.1; simp only [next]; omega)
        hnextParity
      have hpreviousCast : previousGap.castSucc = previous := by
        apply Fin.ext
        rfl
      have hmiddle : previousGap.succ = k.castSucc := by
        apply Fin.ext
        change previousGap.1 + 1 = k.1
        simp only [previousGap]
        omega
      have hnext : k.succ = next := by
        apply Fin.ext
        rfl
      have hzero : b.orderGap previousGap + b.orderGap k = 0 := by
        unfold orderGap
        rw [hpreviousCast, hmiddle, hnext, hpreviousOrder, hnextOrder]
        ring
      have hlower := b.orderGap_ge_neg_two_mul_e previousGap
      omega
  · let f : Nat → Int := b.orderSequence.entryOrZero
    let g : Nat → Int := fun _ ↦ b.order i
    have hterms := int_modEq_two_sum_Ico f g
      (i := i.1) (j := j.1 + 1) (by omega) (by
        intro k hik hkj
        have hkLe : k ≤ j.1 := by omega
        have hkBound : k < n + 1 := hkLe.trans_lt j.isLt
        let kFin : Fin (n + 1) := ⟨k, hkBound⟩
        have hkMod := horderMod kFin
          (by change i.1 ≤ kFin.1; exact hik)
          (by change kFin.1 ≤ j.1; omega)
        simp only [f, g]
        rw [BeliOrderSequence.entryOrZero_of_lt
          (i := k) b.orderSequence hkBound]
        change Int.ModEq 2 (b.order kFin) (b.order i)
        exact hkMod)
    have hcount : Int.ModEq 2 ((j.1 + 1 - i.1 : Nat) : Int) 1 := by
      rcases hijParity with ⟨d, hd⟩
      have hlen : j.1 + 1 - i.1 = 2 * d + 1 := by omega
      rw [hlen, Int.modEq_iff_dvd]
      refine ⟨-(d : Int), ?_⟩
      push_cast
      ring
    have hconstant : Int.ModEq 2
        (∑ _k ∈ Finset.Ico i.1 (j.1 + 1), b.order i) (b.order i) := by
      rw [Finset.sum_const, Nat.card_Ico]
      simpa only [nsmul_eq_mul, one_mul] using hcount.mul_right (b.order i)
    exact hterms.trans hconstant

/-- Beli (2019), Lemma 6.6(ii), in zero-based indexing. -/
theorem beli2019Lemma66_ii
    (b : GoodBONG q L (n + 1)) (i j : Fin (n + 1))
    (hij : i < j) (hijParity : Odd (j.1 - i.1))
    (horder : b.order j ≤ b.order i) :
    Even (b.orderSequence.closedSegmentSum i.1 j.1) := by
  generalize hd : j.1 - i.1 = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
      by_cases hbase : d = 1
      · let gap : Fin n := ⟨i.1, by omega⟩
        have hgapCast : gap.castSucc = i := by
          apply Fin.ext
          rfl
        have hgapSucc : gap.succ = j := by
          apply Fin.ext
          change gap.1 + 1 = j.1
          simp only [gap]
          omega
        have hgapNonpositive : b.orderGap gap ≤ 0 := by
          unfold orderGap
          rw [hgapCast, hgapSucc]
          omega
        have hgapEven := b.orderGap_even_of_nonpositive gap hgapNonpositive
        unfold orderGap at hgapEven
        rw [hgapCast, hgapSucc] at hgapEven
        have hpair : Even (b.order i + b.order j) :=
          even_add_of_even_sub hgapEven
        have hnextIndex : j.1 = i.1 + 1 := by omega
        rw [hnextIndex, BeliOrderSequence.closedSegmentSum_pair]
        rw [← hnextIndex]
        rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence i.isLt,
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence j.isLt]
        exact hpair
      · rcases hijParity with ⟨r, hr⟩
        have hdLarge : 3 ≤ d := by omega
        let previous : Fin (n + 1) := ⟨j.1 - 2, by omega⟩
        have hpreviousLt : i < previous := by
          change i.1 < previous.1
          simp only [previous]
          omega
        have hpreviousParity : Odd (previous.1 - i.1) := by
          refine ⟨r - 1, ?_⟩
          simp only [previous]
          omega
        have hpreviousOrderLeJ : b.order previous ≤ b.order j := by
          have hle := b.orderSequence.entryOrZero_le_of_evenGap
            previous.1 j.1 (by simp only [previous]; omega) j.isLt
            (by refine ⟨1, ?_⟩; simp only [previous]; omega)
          rw [BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence previous.isLt,
            BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence j.isLt] at hle
          change b.order previous ≤ b.order j at hle
          exact hle
        have hpreviousOrder : b.order previous ≤ b.order i :=
          hpreviousOrderLeJ.trans horder
        have hrecursive := ih (previous.1 - i.1)
          (by simp only [previous]; omega) i previous hpreviousLt
          hpreviousParity hpreviousOrder rfl
        let lastGap : Fin n := ⟨j.1 - 1, by omega⟩
        have hlastSucc : lastGap.succ = j := by
          apply Fin.ext
          change lastGap.1 + 1 = j.1
          simp only [lastGap]
          omega
        have hbeforeParity : Even (lastGap.castSucc.1 - i.1) := by
          change Even ((j.1 - 1) - i.1)
          refine ⟨r, ?_⟩
          omega
        have hiLeBefore : b.order i ≤ b.order lastGap.castSucc := by
          have hle := b.orderSequence.entryOrZero_le_of_evenGap
            i.1 lastGap.castSucc.1
            (by change i.1 ≤ j.1 - 1; omega) lastGap.castSucc.isLt
            hbeforeParity
          rw [BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence i.isLt,
            BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence lastGap.castSucc.isLt] at hle
          change b.order i ≤ b.order lastGap.castSucc at hle
          exact hle
        have hlastNonpositive : b.orderGap lastGap ≤ 0 := by
          unfold orderGap
          rw [hlastSucc]
          omega
        have hlastEven :=
          b.orderGap_even_of_nonpositive lastGap hlastNonpositive
        unfold orderGap at hlastEven
        rw [hlastSucc] at hlastEven
        have hlastPair :
            Even (b.order lastGap.castSucc + b.order j) :=
          even_add_of_even_sub hlastEven
        have hfirstIndex : j.1 - 2 + 1 = lastGap.castSucc.1 := by
          change j.1 - 2 + 1 = j.1 - 1
          omega
        have hsecondIndex : j.1 - 2 + 2 = j.1 := by omega
        rw [show j.1 = (j.1 - 2) + 2 by omega,
          BeliOrderSequence.closedSegmentSum_add_two]
        · rw [hfirstIndex, hsecondIndex]
          rw [BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence lastGap.castSucc.isLt,
            BeliOrderSequence.entryOrZero_of_lt
              b.orderSequence j.isLt]
          simpa only [previous, lastGap, BeliOrderSequence.entry,
            orderSequence, add_assoc] using hrecursive.add hlastPair
        · omega

end BONG.GoodBONG

end Bong
