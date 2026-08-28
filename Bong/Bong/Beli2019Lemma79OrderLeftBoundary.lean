/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeI

/-!
# Beli (2019), Lemma 7.9(i): the left no-gap transition

At the left transition of a type-II or type-III profile, the target order is
one above the source plateau.  If the third lattice has strictly larger norm
order, its even-coordinate monotonicity dominates that boundary entry.
-/

namespace Bong

namespace BeliOrderLE.NoGapTwoOuterConsequences

variable {n : Nat}
  {x y : BeliOrderSequence n Int}

/-- If the first difference is at zero, the left transition has even
zero-based index. -/
theorem left_even_of_first_eq_zero
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0) :
    Even O.transition.lastZero := by
  by_cases heq : O.first = O.transition.lastZero
  · rw [← heq, hfirst]
    exact ⟨0, by omega⟩
  · have hlt : O.first < O.transition.lastZero :=
      lt_of_le_of_ne O.first_le_left heq
    simpa only [hfirst, Nat.sub_zero] using (O.leftProfile hlt).1

/-- The source order at the left transition is the first source order. -/
theorem source_leftBoundary_eq_first
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0) :
    x.entryOrZero O.transition.lastZero = x.entryOrZero 0 := by
  by_cases heq : O.first = O.transition.lastZero
  · have := congrArg (fun k ↦ x.entryOrZero k) heq
    simpa only [hfirst] using this.symm
  · have hlt : O.first < O.transition.lastZero :=
      lt_of_le_of_ne O.first_le_left heq
    have hp := O.leftProfile hlt
    have hvalue := hp.2.2 O.transition.lastZero
      O.first_le_left le_rfl hp.1
    simpa only [hfirst] using hvalue

/-- A one-step lower bound at the first coordinate of a third order sequence
dominates the target order at the left no-gap transition. -/
theorem target_leftBoundary_le_of_first_add_one_le
    {z : BeliOrderSequence n Int}
    (O : NoGapTwoOuterConsequences x y) (hfirst : O.first = 0)
    (hfirstLower : x.entryOrZero 0 + 1 ≤ z.entryOrZero 0) :
    y.entryOrZero O.transition.lastZero ≤
      z.entryOrZero O.transition.lastZero := by
  have hbound : O.transition.lastZero < n := by
    have hfirstTwoBound := O.transition.firstTwo_le_rank
    have hseparated := O.transition.separated
    omega
  have heven := O.left_even_of_first_eq_zero hfirst
  have hmono := z.entryOrZero_le_of_evenGap 0
    O.transition.lastZero (Nat.zero_le _) hbound heven
  have hsource := O.source_leftBoundary_eq_first hfirst
  have htarget := O.transition.leftBoundary
  omega

end BeliOrderLE.NoGapTwoOuterConsequences

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Part 5 of Lemma 7.9(i), at the left boundary of a type-II pair. -/
theorem beli2019Lemma79_i_typeII_leftBoundary
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : a.order 0 + 1 ≤ c.order 0) :
    b.order ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hseparated := D.outer.transition.separated
        omega⟩ ≤
      c.order ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hseparated := D.outer.transition.separated
        omega⟩ := by
  have hk : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hseparated := D.outer.transition.separated
    omega
  have hnorm' : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnorm
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have h := D.outer.target_leftBoundary_le_of_first_add_one_le
    hfirst hnorm'
  calc
    b.order ⟨D.outer.transition.lastZero, hk⟩ =
        b.orderSequence.entryOrZero D.outer.transition.lastZero := by
      rw [b.orderSequence.entryOrZero_of_lt hk]
      rfl
    _ ≤ c.orderSequence.entryOrZero D.outer.transition.lastZero := h
    _ = c.order ⟨D.outer.transition.lastZero, hk⟩ := by
      rw [c.orderSequence.entryOrZero_of_lt hk]
      rfl

/-- Part 6 of Lemma 7.9(i), at the left boundary of a type-III pair. -/
theorem beli2019Lemma79_i_typeIII_leftBoundary
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : a.order 0 + 1 ≤ c.order 0) :
    b.order ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hseparated := D.outer.transition.separated
        omega⟩ ≤
      c.order ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        have hseparated := D.outer.transition.separated
        omega⟩ := by
  have hk : D.outer.transition.lastZero < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hseparated := D.outer.transition.separated
    omega
  have hnorm' : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnorm
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have h := D.outer.target_leftBoundary_le_of_first_add_one_le
    hfirst hnorm'
  calc
    b.order ⟨D.outer.transition.lastZero, hk⟩ =
        b.orderSequence.entryOrZero D.outer.transition.lastZero := by
      rw [b.orderSequence.entryOrZero_of_lt hk]
      rfl
    _ ≤ c.orderSequence.entryOrZero D.outer.transition.lastZero := h
    _ = c.order ⟨D.outer.transition.lastZero, hk⟩ := by
      rw [c.orderSequence.entryOrZero_of_lt hk]
      rfl

end BONG.GoodBONG

end Bong
