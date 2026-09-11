/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCTheorem74
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# He (2025), Lemma 7.14

The parity of the ambient determinant fixes the last BONG order.  Both
ambient columns are retained, and the two source rows are normalized to a
valuation unit and a valuation unit times a uniformizer.
-/

namespace Bong

open Dyadic Module AlternatingEndpointTower

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem even_ordUnit_of_square_for_lemma714 (x : Kˣ)
    (hx : IsSquare x) : Even (ordUnit K x) := by
  rcases hx with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

private theorem even_left_iff_right_of_add_even (x y : Int)
    (h : Even (x + y)) : Even x ↔ Even y := by
  constructor
  · intro hx
    simpa only [add_sub_cancel_left] using h.sub hx
  · intro hy
    simpa only [add_sub_cancel_right] using h.sub hy

/-- The determinant parity of an arbitrary source equals the parity of the
parameter in either odd-dimensional ambient column. -/
theorem heADC2025Lemma714_fullOrderEven_iff (k : Nat)
    (a : GoodBONG q L (2 * k + 5)) (c : Kˣ)
    (ambient :
      q.IsIsometric (BONG.coefficientDiagonalSpace (heADCW1Odd (k + 1) c)) ∨
        q.IsIsometric
          (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) c))) :
    Even (ordUnit K (a.prefixProduct (2 * k + 5))) ↔
      Even (ordUnit K c) := by
  let first := heADCW1Odd (K := K) (k + 1) c
  let second := heADCW2Odd (K := K) (k + 1) c
  have hfirstOrder : ordUnit K (diagonalUnitDeterminant first) =
      ordUnit K c := by
    dsimp only [first, heADCW1Odd]
    rw [diagonalUnitDeterminant_heHuOddFirst, ordUnit_mul, ordUnit_pow,
      ordUnit_neg_one_eq_zero]
    simp
  rcases ambient with hfirst | hsecond
  · have hproduct := even_ordUnit_of_square_for_lemma714
      (a.prefixProduct (2 * k + 5) * diagonalUnitDeterminant first)
      (a.heADC_prefixProduct_det_square_of_ambient first hfirst)
    rw [ordUnit_mul] at hproduct
    exact (even_left_iff_right_of_add_even _ _ hproduct).trans (by rw [hfirstOrder])
  · have hsourceSecond := even_ordUnit_of_square_for_lemma714
      (a.prefixProduct (2 * k + 5) * diagonalUnitDeterminant second)
      (a.heADC_prefixProduct_det_square_of_ambient second hsecond)
    rw [ordUnit_mul] at hsourceSecond
    have hsecondFirst := even_ordUnit_of_square_for_lemma714
      (diagonalUnitDeterminant second * diagonalUnitDeterminant first)
      (heADC2025Proposition42iOdd (K := K) (k + 1) c).determinantSquare
    rw [ordUnit_mul] at hsecondFirst
    exact (even_left_iff_right_of_add_even _ _ hsourceSecond).trans
      ((even_left_iff_right_of_add_even _ _ hsecondFirst).trans (by rw [hfirstOrder]))

/-- All source orders before the last one have even total order under the
conditions of Theorem 7.4. -/
theorem heADC2025Lemma714_initialPrefixEven (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (C : a.HeADCTheorem74Conditions k) :
    Even (ordUnit K (a.prefixProduct (2 * k + 4))) := by
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 4) (by omega)]
  unfold BeliOrderSequence.prefixSum
  apply Finset.even_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [a.orderSequence_entryOrZero_eq_order ⟨i, by omega⟩]
  by_cases hpenultimate : i = 2 * k + 3
  · subst i
    exact C.penultimate.1
  · have hinitial : i < 2 * k + 3 := by omega
    rcases Nat.even_or_odd i with heven | hodd
    · rw [C.initial.oddOrder ⟨i, hinitial⟩ heven.add_one]
      exact Even.zero
    · have hbound : i < 2 * k + 2 := by
        obtain ⟨j, hj⟩ := hodd
        omega
      rw [C.initial.evenOrder ⟨i, hbound⟩ hodd.add_one]
      exact ⟨-(ramificationIndex K : Int), by ring⟩

/-- He (2025), Lemma 7.14(i): a unit ambient parameter forces
`R_(n+2)=0`. -/
theorem heADC2025Lemma714i (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K))
    (ambient :
      q.IsIsometric
          (BONG.coefficientDiagonalSpace (heADCW1Odd (k + 1) delta)) ∨
        q.IsIsometric
          (BONG.coefficientDiagonalSpace (heADCW2Odd (k + 1) delta))) :
    a.order ⟨2 * k + 4, by omega⟩ = 0 := by
  have C := a.heADC2025Theorem74Necessity k hADC
  have hfullEven : Even (ordUnit K (a.prefixProduct (2 * k + 5))) :=
    (a.heADC2025Lemma714_fullOrderEven_iff k delta ambient).2 (by
      rw [(isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdelta]
      exact Even.zero)
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 5) le_rfl,
    a.orderSequence.prefixSum_succ (2 * k + 4),
    a.orderSequence_entryOrZero_eq_order ⟨2 * k + 4, by omega⟩] at hfullEven
  have hprefixEven := a.heADC2025Lemma714_initialPrefixEven k C
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 4) (by omega)]
    at hprefixEven
  have hlastEven : Even (a.order ⟨2 * k + 4, by omega⟩) := by
    simpa only [add_sub_cancel_left] using
      hfullEven.sub hprefixEven
  rcases C.last with hzero | hone
  · exact hzero
  · rw [hone] at hlastEven
    norm_num at hlastEven

/-- He (2025), Lemma 7.14(ii): a unit-times-uniformizer ambient parameter
forces `R_(n+2)=1`. -/
theorem heADC2025Lemma714ii (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3))
    (delta : Kˣ) (hdelta : IsValuationUnit K (delta : K))
    (ambient :
      q.IsIsometric (BONG.coefficientDiagonalSpace
          (heADCW1Odd (k + 1) (delta * uniformizerPowerUnit K 1))) ∨
        q.IsIsometric (BONG.coefficientDiagonalSpace
          (heADCW2Odd (k + 1) (delta * uniformizerPowerUnit K 1)))) :
    a.order ⟨2 * k + 4, by omega⟩ = 1 := by
  have C := a.heADC2025Theorem74Necessity k hADC
  have hparameterOdd : Odd
      (ordUnit K (delta * uniformizerPowerUnit K 1)) := by
    rw [ordUnit_mul, (isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdelta,
      ordUnit_uniformizerPowerUnit]
    exact odd_one
  have hfullOdd : Odd (ordUnit K (a.prefixProduct (2 * k + 5))) := by
    apply Int.not_even_iff_odd.mp
    intro hfullEven
    have hparameterEven :=
      (a.heADC2025Lemma714_fullOrderEven_iff k
        (delta * uniformizerPowerUnit K 1) ambient).mp hfullEven
    exact (Int.not_even_iff_odd.mpr hparameterOdd) hparameterEven
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 5) le_rfl,
    a.orderSequence.prefixSum_succ (2 * k + 4),
    a.orderSequence_entryOrZero_eq_order ⟨2 * k + 4, by omega⟩] at hfullOdd
  have hprefixEven := a.heADC2025Lemma714_initialPrefixEven k C
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum (2 * k + 4) (by omega)]
    at hprefixEven
  have hlastOdd : Odd (a.order ⟨2 * k + 4, by omega⟩) := by
    simpa only [add_sub_cancel_left] using
      hfullOdd.sub_even hprefixEven
  rcases C.last with hzero | hone
  · rw [hzero] at hlastOdd
    norm_num at hlastOdd
  · exact hone

end BONG.GoodBONG

end Bong
