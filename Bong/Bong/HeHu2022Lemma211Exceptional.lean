/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionTwo
import Bong.Bong.HeHu2022Lemma211Parity
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.Beli2019Lemma69TypeIRightEndpoint

/-! # He--Hu (2024), Lemma 2.11: exceptional tail -/

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

set_option maxHeartbeats 500000 in
-- The finite-tail construction merits its own checking budget and unit.
/-- The exceptional parity calculation inside He--Hu, Lemma 2.11. -/
theorem heHu2022Lemma211ExceptionalTailLong {m : Nat} (t : Nat)
    (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (2 * t + 3))
    (hm : 2 * t + 4 ≤ m + 1)
    (hBIntegral : Lattice.IsIntegral r M)
    (j : Fin (2 * t + 2))
    (hjEven : Even j.val)
    (hjBefore : j.val + 1 < 2 * t + 2)
    (hJZero : b.order j.castSucc = 0)
    (hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))))
    (hProductOdd : Odd (ordUnit K
      (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))))
    (hSourceLeJ : a.order ⟨2 * t + 3, by omega⟩ ≤ b.order j.succ) :
    ((a.order ⟨2 * t + 3, by omega⟩ -
        b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨2 * t + 1, by omega⟩ ≤ 0 := by
  let targetLast : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
  let lastGap : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
  let sourceNext : Fin (m + 1) := ⟨2 * t + 3, by omega⟩
  have hTargetPrefixOrderOdd :
      Odd (ordUnit K (b.prefixProduct (2 * t + 3))) := by
    rw [ordUnit_mul] at hProductOdd
    rcases hSourcePrefixOrderEven with ⟨s, hs⟩
    rcases hProductOdd with ⟨p, hp⟩
    refine ⟨p - s, ?_⟩
    omega
  have hTargetPrefixSumOdd :
      Odd (b.orderSequence.prefixSum (2 * t + 3)) := by
    rw [← b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * t + 3) (by omega)]
    exact hTargetPrefixOrderOdd
  have hJEvenAsTarget : Even (j.castSucc.val) := by
    simpa only [Fin.val_castSucc] using hjEven
  let targetParity := b.heHu2022Proposition27ii hBIntegral
    j.castSucc hJEvenAsTarget hJZero
  let start := j.val + 1
  have hStartOdd : Odd start := by
    rcases hjEven with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    simp only [start]
    omega
  have hStartBound : start < 2 * t + 3 := by
    simp only [start]
    omega
  have hStartPrefixEven :
      Even (b.orderSequence.prefixSum start) := by
    apply b.orderSequence.prefixSum_even_of_entries_even start
    intro k hk
    let kFin : Fin (2 * t + 3) := ⟨k, by omega⟩
    rw [b.orderSequence_entryOrZero_eq_order kFin]
    exact targetParity.precedingOrdersEven kFin
      (Fin.mk_le_mk.mpr (by
        simp only [start] at hk ⊢
        omega))
  have hTailOdd : Odd
      (b.orderSequence.prefixSum (2 * t + 3) -
        b.orderSequence.prefixSum start) := by
    rcases hTargetPrefixSumOdd with ⟨p, hp⟩
    rcases hStartPrefixEven with ⟨s, hs⟩
    refine ⟨p - s, ?_⟩
    omega
  have hTailLengthEven : Even ((2 * t + 3) - start) := by
    rcases hjEven with ⟨d, hd⟩
    refine ⟨t - d + 1, ?_⟩
    simp only [start]
    omega
  rcases b.orderSequence.exists_odd_pair_sum_odd_of_prefixDifference_odd
      start (2 * t + 3) hStartOdd hTailLengthEven hStartBound hTailOdd with
    ⟨ell, hEllOdd, hStartEll, hEllBound, hEllPairOdd⟩
  let ellGap : Fin (2 * t + 2) := ⟨ell, by omega⟩
  have hEllOrderPairOdd :
      Odd (b.order ellGap.castSucc + b.order ellGap.succ) := by
    rw [← b.orderSequence_entryOrZero_eq_order ellGap.castSucc,
      ← b.orderSequence_entryOrZero_eq_order ellGap.succ]
    simpa only [ellGap, Fin.val_castSucc, Fin.val_succ] using hEllPairOdd
  have hEllDefectZero : b.adjacentDefect ellGap = 0 :=
    b.adjacentDefect_eq_zero_of_order_sum_odd ellGap hEllOrderPairOdd
  have hEllLeLast : ellGap ≤ lastGap := by
    apply Fin.mk_le_mk.mpr
    omega
  have hBetaEllRaw := b.alpha_le_leftDefectCandidate
    (i := lastGap) (j := ellGap) hEllLeLast
  have hBetaEll :
      b.alphaValue lastGap ≤
        ((b.order targetLast - b.order ellGap.castSucc : Int) : ℚ) := by
    rw [← b.coe_alphaValue, leftDefectCandidate,
      hEllDefectZero, add_zero] at hBetaEllRaw
    norm_cast at hBetaEllRaw
  let targetOrders := b.heHu2022Proposition27i hBIntegral
  have hJSuccOdd : Odd (j.succ.val) := by
    rcases hjEven with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    simp only [Fin.val_succ]
    omega
  have hEllGapOdd : Odd (ellGap.castSucc.val) := by
    simpa only [ellGap, Fin.val_castSucc] using hEllOdd
  have hJSuccLeEll : j.succ ≤ ellGap.castSucc := by
    apply Fin.mk_le_mk.mpr
    simp only [ellGap, start] at hStartEll ⊢
    exact hStartEll
  have hJLeEll := (targetOrders.evenIndexed j.succ ellGap.castSucc
    hJSuccLeEll hJSuccOdd hEllGapOdd).2
  have hSourceLeEll : a.order sourceNext ≤ b.order ellGap.castSucc := by
    have hSourceLeJ' : a.order sourceNext ≤ b.order j.succ := by
      simpa only [sourceNext] using hSourceLeJ
    exact hSourceLeJ'.trans hJLeEll
  push_cast at hBetaEll ⊢
  have hSourceLeEllQ : (a.order sourceNext : ℚ) ≤
      (b.order ellGap.castSucc : ℚ) := by
    exact_mod_cast hSourceLeEll
  linarith

/-- Exact-rank specialization of the long-source exceptional calculation. -/
theorem heHu2022Lemma211ExceptionalTail (t : Nat)
    (a : GoodBONG q L (2 * t + 4))
    (b : GoodBONG r M (2 * t + 3))
    (hBIntegral : Lattice.IsIntegral r M)
    (j : Fin (2 * t + 2))
    (hjEven : Even j.val)
    (hjBefore : j.val + 1 < 2 * t + 2)
    (hJZero : b.order j.castSucc = 0)
    (hSourcePrefixOrderEven :
      Even (ordUnit K (a.prefixProduct (2 * t + 3))))
    (hProductOdd : Odd (ordUnit K
      (a.prefixProduct (2 * t + 3) * b.prefixProduct (2 * t + 3))))
    (hSourceLeJ : a.order ⟨2 * t + 3, by omega⟩ ≤ b.order j.succ) :
    ((a.order ⟨2 * t + 3, by omega⟩ -
        b.order ⟨2 * t + 2, by omega⟩ : Int) : ℚ) +
        b.alphaValue ⟨2 * t + 1, by omega⟩ ≤ 0 := by
  exact a.heHu2022Lemma211ExceptionalTailLong t b (by omega)
    hBIntegral j hjEven hjBefore hJZero hSourcePrefixOrderEven
    hProductOdd hSourceLeJ

end BONG.GoodBONG

end Bong
