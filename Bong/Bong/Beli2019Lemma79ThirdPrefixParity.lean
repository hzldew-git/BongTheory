/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderRightAlternating

/-!
# Beli (2019), Lemma 7.9(i): parity of the third BONG prefix

Lemma 6.5 is invoked after showing that the first order of the third BONG is
at least a reference order `T`, while its current order is at most `T`.
Lemma 6.6 then gives the uniform formula for the prefix-order parity, with
separate even- and odd-coordinate proofs hidden behind one interface.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- If the first order is at least `T` and the order at zero-based index `k`
is at most `T`, then the first `k + 1` orders have parity `(k + 1)T`. -/
theorem prefixSum_modEq_mul_of_current_le_reference_le_first
    (b : GoodBONG q L (n + 1)) (T : Int) (k : Nat) (hk : k < n + 1)
    (hfirst : T ≤ b.orderSequence.entryOrZero 0)
    (hcurrent : b.orderSequence.entryOrZero k ≤ T) :
    Int.ModEq 2 (b.orderSequence.prefixSum (k + 1))
      (((k + 1 : Nat) : Int) * T) := by
  rcases Nat.even_or_odd k with heven | hodd
  · have hmono := b.orderSequence.entryOrZero_le_of_evenGap
      0 k (Nat.zero_le k) hk heven
    have hfirstEq : b.orderSequence.entryOrZero 0 = T := by omega
    have hcurrentEq : b.orderSequence.entryOrZero k = T := by omega
    let first : Fin (n + 1) := ⟨0, by omega⟩
    let current : Fin (n + 1) := ⟨k, hk⟩
    have hendpoint : b.order first = b.order current := by
      rw [← b.orderSequence_entryOrZero_eq_order first,
        ← b.orderSequence_entryOrZero_eq_order current]
      simpa only [first, current] using hfirstEq.trans hcurrentEq.symm
    have hdata := b.beli2019Lemma66_i first current
      (by change 0 ≤ k; omega)
      (by simpa only [first, current, Nat.sub_zero] using heven)
      hendpoint
    apply b.orderSequence.prefixSum_modEq_mul T (k + 1)
    intro j hj
    have hjBound : j < n + 1 := hj.trans_le (by omega)
    let jFin : Fin (n + 1) := ⟨j, hjBound⟩
    have hmod := hdata.order_modEq jFin
      (by change 0 ≤ j; omega) (by change j ≤ k; omega)
    rw [← b.orderSequence_entryOrZero_eq_order jFin,
      ← b.orderSequence_entryOrZero_eq_order first] at hmod
    simpa only [jFin, first, hfirstEq] using hmod
  · let first : Fin (n + 1) := ⟨0, by omega⟩
    let current : Fin (n + 1) := ⟨k, hk⟩
    have hclosed := b.beli2019Lemma66_ii first current
      (by change 0 < k; rcases hodd with ⟨d, hd⟩; omega)
      (by simpa only [first, current, Nat.sub_zero] using hodd)
      (by
        rw [← b.orderSequence_entryOrZero_eq_order current,
          ← b.orderSequence_entryOrZero_eq_order first]
        simpa only [first, current] using hcurrent.trans hfirst)
    have hprefixEven : Even (b.orderSequence.prefixSum (k + 1)) := by
      simp only [first, current] at hclosed
      simpa only [BeliOrderSequence.closedSegmentSum,
        BeliOrderSequence.prefixSum, Nat.Ico_zero_eq_range] using hclosed
    have hprefixZero : Int.ModEq 2
        (b.orderSequence.prefixSum (k + 1)) 0 := by
      apply int_modEq_two_of_even_sub
      simpa using hprefixEven
    rcases hodd with ⟨d, hd⟩
    have hcountZero : Int.ModEq 2 (((k + 1 : Nat) : Int)) 0 := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-((d + 1 : Nat) : Int), ?_⟩
      push_cast
      omega
    exact hprefixZero.trans (by
      simpa using (hcountZero.mul_right T).symm)

end BONG.GoodBONG

end Bong
