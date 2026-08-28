/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIEarlySecond
import Bong.Bong.Beli2019Lemma79NextAlphaLocal

/-!
# Beli (2019), Lemma 7.9(iii): the common early type-II/type-III profile

Before the first no-gap-two transition, types II and III have the same
outer order profile.  This file isolates the arguments shared by cases 1,
5, 7, and 8: even active boundaries are impossible, an odd first
alternative has the endpoint-tower form, and an odd second alternative is
impossible strictly before the transition boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The second alternative of Lemma 2.18 is bounded above by the two
adjacent target alphas. -/
theorem lemma79Central_secondAlternative_targetAlphaSum
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) :
    2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by omega⟩ +
        b.alphaValue ⟨i.val, by omega⟩ := by
  have hcap : b.centralCurrentDefect c i ≤
      b.prefixAlphaCap (i.val + 1) := by
    unfold centralCurrentDefect
    exact b.truncatedPrefixDefect_le_leftCap c (-1)
      (i.val + 1) (i.val - 1)
  have hstrict :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) :=
    hcurrent.trans_le (add_le_add le_rfl hcap)
  rw [b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large,
    b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) hiNext] at hstrict
  have hstrictQ :
      2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by omega⟩ +
          b.alphaValue ⟨i.val + 1 - 1, by omega⟩ := by
    exact_mod_cast hstrict
  simpa only [show i.val + 1 - 1 = i.val by omega] using hstrictQ

/-- At an even boundary in the early no-gap-two outer interval, the
target current order is already the norm-floor order.  The strict order
part of the central trigger is therefore impossible. -/
theorem lemma79Central_outerEarly_even_trigger_not
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ O.transition.lastZero + 1)
    (hiEven : Even i.val)
    (htrigger : b.centralAlphaTrigger c i) : False := by
  have hleftEven := O.left_even_of_first_eq_zero hfirst
  have hiLeft : i.val ≤ O.transition.lastZero := by
    rcases hiEven with ⟨d, hd⟩
    rcases hleftEven with ⟨e, he⟩
    omega
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have htargetCurrent := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hiLeft hiEven
  have htargetZero := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent.trans htargetZero.symm
  have hbZero : b.order 0 = a.order 0 + 1 := by
    change b.order (0 : Fin (n + 2)) =
      a.order (0 : Fin (n + 2)) + 1
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact htargetZero
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 2) (Nat.zero_le _) (by
      have := i.lt_large
      omega) hiPreviousEven
  have hcMonotone : c.order 0 ≤ c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hcMonotoneRaw
  have hcross := htrigger.1
  rw [hbCurrent, hbZero] at hcross
  exact (not_lt_of_ge (hnormOrder.trans hcMonotone)) hcross

/-- At an odd boundary strictly before the transition, the second
Lemma 2.18 alternative would force strict growth between two equal even
entries of the target profile. -/
theorem lemma79Central_outerEarly_odd_second_not_of_lt
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiOdd : Odd i.val)
    (hstrictEarly : i.val < O.transition.lastZero + 1)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hleftEven := O.left_even_of_first_eq_zero hfirst
  have hiNextLeft : i.val + 1 ≤ O.transition.lastZero := by
    rcases hiOdd with ⟨d, hd⟩
    rcases hleftEven with ⟨e, he⟩
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := O.transition.firstTwo_le_rank
    have htransition := O.transition.lastZero_lt_firstTwo
    omega
  have hsum := b.lemma79Central_secondAlternative_targetAlphaSum
    c i hiNext hcurrent
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by
      have := i.one_lt
      omega, hiNext, by
        have := i.lt_large
        omega⟩
  have hgrowth := b.order_twoStep_lt_of_alphaSum_gt_twoE j (by
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum)
  have hpreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hnextEven : Even (i.val + 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d + 1, by omega⟩
  have hprevious := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val - 1) (by omega) hpreviousEven
  have hnext := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val + 1) hiNextLeft hnextEven
  have heq : b.order ⟨i.val - 1, by omega⟩ =
      b.order ⟨i.val + 1, hiNext⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hprevious.trans hnext.symm
  have hgrowth' : b.order ⟨i.val - 1, by omega⟩ <
      b.order ⟨i.val + 1, hiNext⟩ := by
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega] using hgrowth
  exact (ne_of_lt hgrowth') heq

/-- In the common outer early profile, an odd first alternative forces
the preceding target gap to be exactly `2e`. -/
theorem lemma79Central_outerEarly_odd_previousGap_eq_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ O.transition.lastZero + 1)
    (hiOdd : Odd i.val)
    (halpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩) :
    b.orderGap ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ = 2 * (ramificationIndex K : Int) := by
  have hleftEven := O.left_even_of_first_eq_zero hfirst
  let right : Fin (n + 2) := ⟨O.transition.lastZero, by
    have hbound := O.transition.firstTwo_le_rank
    have htransition := O.transition.lastZero_lt_firstTwo
    omega⟩
  have hzeroEntry := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hrightEntry := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo O.transition.lastZero le_rfl hleftEven
  have horders : b.order (0 : Fin (n + 2)) = b.order right := by
    rw [← b.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2)),
      ← b.orderSequence_entryOrZero_eq_order right]
    exact hzeroEntry.trans hrightEntry.symm
  have hrightEven : Even right.val := by
    simpa only [right] using hleftEven
  have hinterval := b.beli2019Lemma66_i (0 : Fin (n + 2)) right
    (Fin.zero_le _) (by
      simpa only [right, Fin.val_zero, Nat.sub_zero] using hrightEven) horders
  let gap : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hgapUpper : b.orderGap gap ≤
      2 * (ramificationIndex K : Int) :=
    hinterval.gap_le gap (by
      change 0 ≤ i.val - 2
      omega) (by
        change i.val - 2 < O.transition.lastZero
        have := i.one_lt
        omega)
  have halphaLower : 2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue gap := by
    apply b.alphaValue_ge_twoE_of_gt_twoE_sub_one gap
    simpa only [gap] using halpha
  have hgapLower : 2 * (ramificationIndex K : Int) ≤ b.orderGap gap :=
    b.orderGap_ge_twoE_of_alphaValue_ge_twoE_early gap halphaLower
  simpa only [gap] using (show b.orderGap gap =
    2 * (ramificationIndex K : Int) by omega)

/-- The last two target entries in the odd outer early branch are the
high endpoint and the endpoint `2e` below it. -/
theorem lemma79Central_outerEarly_first_odd_targetOrders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ O.transition.lastZero + 1) (hiOdd : Odd i.val)
    (hgap : b.orderGap ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ = 2 * (ramificationIndex K : Int)) :
    b.order ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ = b.order 0 ∧
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
  have hpreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hzero := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hhigh := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val - 1) (by omega) hpreviousEven
  have htargetHigh : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = b.order 0 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hhigh.trans hzero.symm
  let p : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hpSucc : p.succ = (⟨i.val - 1, by
      have := i.lt_large
      omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    have := i.one_lt
    omega
  have hpCast : p.castSucc = (⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hgap' : b.orderGap p = 2 * (ramificationIndex K : Int) := by
    simpa only [p] using hgap
  unfold orderGap at hgap'
  rw [hpSucc, hpCast, htargetHigh] at hgap'
  exact ⟨htargetHigh, by omega⟩

/-- Endpoint-average arithmetic for an odd early profile.  Only the high
target order, its alpha bound, and the one-unit norm-floor shift are used;
the statement is therefore shared by all three normalized profile types. -/
theorem lemma79Central_first_odd_comparisonOrders_of_highProfile
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiOdd : Odd i.val)
    (hbCurrent : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = b.order 0)
    (hbetaCurrent : b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ ≤ 1)
    (hbZero : b.order 0 = a.order 0 + 1)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    c.order 0 = b.order 0 ∧
      c.order ⟨i.val - 3, by
        have := i.one_lt
        have := i.lt_large
        rcases hiOdd with ⟨d, hd⟩
        omega⟩ = b.order 0 ∧
      c.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
  have hiBound := i.lt_large
  have hiThree : 3 ≤ i.val := by
    have := i.one_lt
    rcases hiOdd with ⟨d, hd⟩
    omega
  have hiCurrentEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hiFarEven : Even (i.val - 3) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  let sourceCurrent : Fin (n + 2) := ⟨i.val - 1, by omega⟩
  let comparisonFar : Fin (n + 2) := ⟨i.val - 3, by omega⟩
  let comparisonNear : Fin (n + 2) := ⟨i.val - 2, by omega⟩
  let comparisonGap : Fin (n + 1) := ⟨i.val - 3, by omega⟩
  have hbCurrent' : b.order sourceCurrent = b.order 0 := by
    simpa only [sourceCurrent] using hbCurrent
  have hpreviousLower :=
    b.lemma79Central_firstAlternative_previousAlphaLower c i hprevious
  have hrepresentationLower :
      2 * (ramificationIndex K : ℚ) - 1 <
        b.representationAlphaValue c i.previous := by
    linarith
  have haverage := b.lemma79Central_previousAlpha_le_endpointAverage c i
    hiThree
  have haverageQ : b.representationAlphaValue c i.previous ≤
      (b.order sourceCurrent : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) := by
    exact_mod_cast haverage
  have hstrictAverage : 2 * (ramificationIndex K : ℚ) - 1 <
      (b.order sourceCurrent : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) :=
    hrepresentationLower.trans_le haverageQ
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  change a.order 0 + 1 ≤ c.order 0 at hnormOrder
  have hcZeroLower : b.order 0 ≤ c.order 0 := by omega
  have hcFarMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 3) (Nat.zero_le _) (by omega) hiFarEven
  have hcFarMonotone : c.order 0 ≤ c.order comparisonFar := by
    calc
      c.order 0 = c.orderSequence.entryOrZero 0 :=
        (c.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2))).symm
      _ ≤ c.orderSequence.entryOrZero (i.val - 3) := hcFarMonotoneRaw
      _ = c.order comparisonFar := by
        simpa only [comparisonFar] using
          c.orderSequence_entryOrZero_eq_order comparisonFar
  have hcFarLower : b.order 0 ≤ c.order comparisonFar :=
    hcZeroLower.trans hcFarMonotone
  have hgapLowerRaw := c.orderGap_ge_neg_two_mul_e comparisonGap
  have hgapLower :
      -(2 * (ramificationIndex K : Int)) ≤
        c.order comparisonNear - c.order comparisonFar := by
    unfold orderGap at hgapLowerRaw
    have hsucc : comparisonGap.succ = comparisonNear := by
      apply Fin.ext
      simp only [comparisonGap, comparisonNear, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonFar := by
      apply Fin.ext
      rfl
    simpa only [hsucc, hcast] using hgapLowerRaw
  have hgapLowerQ :
      -(2 * (ramificationIndex K : ℚ)) ≤
        (c.order comparisonNear : ℚ) -
          (c.order comparisonFar : ℚ) := by
    exact_mod_cast hgapLower
  have hcFarUpperQ : (c.order comparisonFar : ℚ) <
      (b.order 0 : ℚ) + 1 := by
    rw [hbCurrent'] at hstrictAverage
    linarith
  have hcFarUpper : c.order comparisonFar < b.order 0 + 1 := by
    exact_mod_cast hcFarUpperQ
  have hcFar : c.order comparisonFar = b.order 0 := by omega
  have hcNearUpperQ : (c.order comparisonNear : ℚ) <
      (b.order 0 : ℚ) - 2 * (ramificationIndex K : ℚ) + 2 := by
    rw [hbCurrent', hcFar] at hstrictAverage
    linarith
  have hcNearUpper : c.order comparisonNear <
      b.order 0 - 2 * (ramificationIndex K : Int) + 2 := by
    exact_mod_cast hcNearUpperQ
  have hePos : 0 < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos (K := K)
  have hgapNegative : c.orderGap comparisonGap < 0 := by
    unfold orderGap
    have hsucc : comparisonGap.succ = comparisonNear := by
      apply Fin.ext
      simp only [comparisonGap, comparisonNear, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonFar := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hcFar]
    omega
  have hgapEven := c.orderGap_even_of_negative comparisonGap hgapNegative
  have hgapUpper : c.orderGap comparisonGap <
      2 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    have hsucc : comparisonGap.succ = comparisonNear := by
      apply Fin.ext
      simp only [comparisonGap, comparisonNear, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonFar := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hcFar]
    omega
  have hgapExact : c.orderGap comparisonGap =
      -(2 * (ramificationIndex K : Int)) := by
    rcases hgapEven with ⟨z, hz⟩
    omega
  have hcNear : c.order comparisonNear =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap at hgapExact
    have hsucc : comparisonGap.succ = comparisonNear := by
      apply Fin.ext
      simp only [comparisonGap, comparisonNear, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonFar := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hcFar] at hgapExact
    omega
  have hcZero : c.order 0 = b.order 0 := by omega
  exact ⟨hcZero, by simpa only [comparisonFar] using hcFar,
    by simpa only [comparisonNear] using hcNear⟩

/-- Case 1 for the common type-II/type-III early profile: the target and
comparison prefixes are equal-scale endpoint towers and the target has one
additional high-order line. -/
theorem lemma79Central_outerEarly_first_odd_direct
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ O.transition.lastZero + 1) (hiOdd : Odd i.val)
    (hbetaCurrent : b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ ≤ 1)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  have hiBound := i.lt_large
  have hsum := b.lemma79Central_firstAlternative_targetAlphaSum c
    hdefectBC i hprevious
  have hpreviousAlpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ := by
    linarith
  have hgap := lemma79Central_outerEarly_odd_previousGap_eq_twoE
    a b O hfirst hnoTwo i hearly hiOdd hpreviousAlpha
  rcases lemma79Central_outerEarly_first_odd_targetOrders
      a b O hfirst hnoTwo i hearly hiOdd hgap with ⟨hbExtra, hbLow⟩
  have hpreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have htargetCurrent := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo (i.val - 1) (by omega) hpreviousEven
  have htargetZero := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hbCurrent : b.order ⟨i.val - 1, by omega⟩ = b.order 0 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent.trans htargetZero.symm
  have hbZero : b.order 0 = a.order 0 + 1 := by
    change b.order (0 : Fin (n + 2)) =
      a.order (0 : Fin (n + 2)) + 1
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact htargetZero
  rcases lemma79Central_first_odd_comparisonOrders_of_highProfile
      a b c hnorm i hiOdd hbCurrent hbetaCurrent hbZero hprevious with
    ⟨hcFirst, hcHigh, hcLow⟩
  rcases hiOdd with ⟨pairs, hpairsEq⟩
  have hpairs : 0 < pairs := by
    have := i.one_lt
    omega
  have htwice : 2 * pairs = i.val - 1 := by omega
  have htargetLast : b.order ⟨2 * pairs - 1, by omega⟩ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    have hindex : (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) =
        ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hindex]
    exact hbLow
  have hcomparisonLast : c.order ⟨2 * pairs - 1, by omega⟩ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    have hindex : (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) =
        ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hindex]
    exact hcLow
  have hextra : b.order ⟨2 * pairs, by omega⟩ = b.order 0 := by
    simpa only [htwice] using hbExtra
  have hrep := b.lemma79_endpointTower_representationInUnaryExtension
    c (b.order 0) pairs hpairs (by omega) rfl htargetLast hcFirst
      hcomparisonLast hextra
  exact prefixRepresents_cast c b htwice (by omega) hrep

end BONG.GoodBONG

end Bong
