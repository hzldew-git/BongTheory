/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralEarlyArithmetic

/-!
# Beli (2019), Lemma 7.9(iii), case 1 for type I

This file treats the first Lemma 2.18 alternative in the early type-I
region.  Odd indices give two equal endpoint towers and one additional
target line.  Even indices are forced to the first switch and give a tower
with one additional binary pair.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At an odd early index, the target prefix in case 1 has high order at
its first and extra entries and low order `2e` below it at the end of the
even tower. -/
theorem lemma79Central_typeIEarly_first_odd_targetOrders
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiOdd : Odd i.val)
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
  have hiTwo := i.one_lt
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  have hiStrict : i.val < C.leftSwitch := by
    rcases hiOdd with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hiPreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hzero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have hhigh := C.target_before_left (i.val - 1) (by omega)
    hiPreviousEven
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

/-- The endpoint-average estimate identifies the two final comparison
orders in the odd branch: the leading member of the last pair has the high
order, and its partner is exactly `2e` lower. -/
theorem lemma79Central_typeIEarly_first_odd_comparisonOrders
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiOdd : Odd i.val)
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
  have hiThree : 3 ≤ i.val := by
    have := i.one_lt
    rcases hiOdd with ⟨d, hd⟩
    omega
  have hiBound := i.lt_large
  have hleftPos : 0 < C.leftSwitch := by omega
  have hiStrict : i.val < C.leftSwitch := by
    rcases hiOdd with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
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
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
  have htargetCurrent := C.target_before_left (i.val - 1) (by omega)
    hiCurrentEven
  have hbCurrent : b.order sourceCurrent = b.order 0 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact htargetCurrent.trans htargetZero.symm
  have hbetaCurrent : b.alphaValue ⟨i.val - 1, by omega⟩ ≤ 1 :=
    beli2019Lemma69_i_typeI_targetLeftTail a b D C hfirst hleftPos
      (i.val - 1) (by omega) hiCurrentEven
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
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have hbZero : b.order 0 = a.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    calc
      b.orderSequence.entryOrZero 0 =
          a.orderSequence.entryOrZero D.anchor + 1 := htargetZero
      _ = a.orderSequence.entryOrZero 0 + 1 := by rw [hsourceZero]
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
    rw [hbCurrent] at hstrictAverage
    linarith
  have hcFarUpper : c.order comparisonFar < b.order 0 + 1 := by
    exact_mod_cast hcFarUpperQ
  have hcFar : c.order comparisonFar = b.order 0 := by omega
  have hcNearUpperQ : (c.order comparisonNear : ℚ) <
      (b.order 0 : ℚ) - 2 * (ramificationIndex K : ℚ) + 2 := by
    rw [hbCurrent, hcFar] at hstrictAverage
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

/-- Case 1, odd branch: the two length-`i-1` prefixes are equal-scale
endpoint towers and the target has one additional line at their high scale.
The endpoint-tower representation therefore supplies condition (iii)
directly. -/
theorem lemma79Central_typeIEarly_first_odd_direct
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiOdd : Odd i.val)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  have hiCurrentEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hbetaCurrent : b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ ≤ 1 :=
    beli2019Lemma69_i_typeI_targetLeftTail a b D C hfirst hleftPos
      (i.val - 1) (by
        rcases hiOdd with ⟨d, hd⟩
        rcases C.left_even with ⟨e, he⟩
        omega) hiCurrentEven
  have hsum := b.lemma79Central_firstAlternative_targetAlphaSum c
    hdefectBC i hprevious
  have hpreviousAlpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 2, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ := by
    linarith
  have hgap := lemma79Central_typeIEarly_odd_previousGap_eq_twoE
    a b D C hfirst i hearly hiOdd hpreviousAlpha
  rcases lemma79Central_typeIEarly_first_odd_targetOrders
      a b D C i hearly hiOdd hgap with ⟨hbExtra, hbLow⟩
  rcases lemma79Central_typeIEarly_first_odd_comparisonOrders
      a b c D C hfirst hnorm i hearly hiOdd hprevious with
    ⟨hcFirst, hcHigh, hcLow⟩
  rcases hiOdd with ⟨pairs, hpairsEq⟩
  have hiBound := i.lt_large
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

/-- In the nonempty even branch, the endpoint average forces the last entry
of the shorter comparison tower to be exactly `R - 2e`. -/
theorem lemma79Central_typeIEarly_first_even_comparisonLow
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiFour : 4 ≤ i.val)
    (hgap : b.orderGap ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hbLow : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int))
    (hcFirst : c.order 0 = b.order 0)
    (hcExtra : c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ = b.order 0)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    c.order ⟨i.val - 3, by
      have := i.lt_large
      omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
  have hiBound := i.lt_large
  let currentGap : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let comparisonFar : Fin (n + 2) := ⟨i.val - 3, by omega⟩
  let comparisonNear : Fin (n + 2) := ⟨i.val - 2, by omega⟩
  have hhalf : b.halfGapValue currentGap =
      2 * (ramificationIndex K : ℚ) + 1 / 2 := by
    unfold halfGapValue
    have hgap' : b.orderGap currentGap =
        2 * (ramificationIndex K : Int) + 1 := by
      simpa only [currentGap] using hgap
    rw [hgap']
    push_cast
    ring
  have hcurrentUpper : b.alphaValue currentGap ≤
      2 * (ramificationIndex K : ℚ) + 1 / 2 := by
    calc
      b.alphaValue currentGap ≤ b.halfGapValue currentGap :=
        b.alphaValue_le_halfGapValue currentGap
      _ = _ := hhalf
  have hpreviousLower :=
    b.lemma79Central_firstAlternative_previousAlphaLower c i hprevious
  have hrepresentationLower : -(1 / 2 : ℚ) <
      b.representationAlphaValue c i.previous := by
    have hcurrentIndex : currentGap = (⟨i.val - 1, by omega⟩ :
        Fin (n + 1)) := by rfl
    rw [← hcurrentIndex] at hpreviousLower
    linarith
  have haverage := b.lemma79Central_previousAlpha_le_endpointAverage c i
    (by omega)
  have haverageQ : b.representationAlphaValue c i.previous ≤
      (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) := by
    exact_mod_cast haverage
  have hstrictAverage : -(1 / 2 : ℚ) <
      (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) :=
    hrepresentationLower.trans_le haverageQ
  have hfarUpperQ : (c.order comparisonFar : ℚ) <
      (b.order 0 : ℚ) - 2 * (ramificationIndex K : ℚ) + 1 := by
    have hcNear : c.order comparisonNear = b.order 0 := by
      simpa only [comparisonNear] using hcExtra
    rw [hbLow, hcNear] at hstrictAverage
    push_cast at hstrictAverage
    linarith
  have hfarUpper : c.order comparisonFar <
      b.order 0 - 2 * (ramificationIndex K : Int) + 1 := by
    exact_mod_cast hfarUpperQ
  let firstGap : Fin (n + 1) := ⟨0, by omega⟩
  have hfirstGapLowerRaw := c.orderGap_ge_neg_two_mul_e firstGap
  have hfirstGapLower : c.order 0 - 2 * (ramificationIndex K : Int) ≤
      c.order ⟨1, by omega⟩ := by
    unfold orderGap at hfirstGapLowerRaw
    have hsucc : firstGap.succ = (⟨1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hcast : firstGap.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at hfirstGapLowerRaw
    omega
  have hiFarOdd : Odd (i.val - 3) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 2, by omega⟩
  have hoddGap : Even ((i.val - 3) - 1) := by
    rcases hiFarOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hfarMonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    1 (i.val - 3) (by omega) (by omega) hoddGap
  have hfarMonotone : c.order ⟨1, by omega⟩ ≤ c.order comparisonFar := by
    calc
      c.order ⟨1, by omega⟩ = c.orderSequence.entryOrZero 1 :=
        (c.orderSequence_entryOrZero_eq_order ⟨1, by omega⟩).symm
      _ ≤ c.orderSequence.entryOrZero (i.val - 3) := hfarMonotoneRaw
      _ = c.order comparisonFar := by
        simpa only [comparisonFar] using
          c.orderSequence_entryOrZero_eq_order comparisonFar
  have hfarLower : b.order 0 - 2 * (ramificationIndex K : Int) ≤
      c.order comparisonFar := by
    rw [← hcFirst]
    exact hfirstGapLower.trans hfarMonotone
  have hfar : c.order comparisonFar =
      b.order 0 - 2 * (ramificationIndex K : Int) := by omega
  simpa only [comparisonFar] using hfar

/-- Case 1, even branch: the index is the first type-I switch.  The target
endpoint tower has one more binary pair than the comparison tower, and the
remaining comparison entry has the common high order. -/
theorem lemma79Central_typeIEarly_first_even_direct
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ < b.order ⟨i.val, i.lt_large⟩)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  have hleft := lemma79Central_typeIEarly_even_eq_leftSwitch
    a b c D C hnorm i hearly hiEven hcross
  have hleftPos : 0 < C.leftSwitch := by
    have := i.one_lt
    omega
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hbetaPrevious : b.alphaValue ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ ≤ 1 :=
    beli2019Lemma69_i_typeI_targetLeftTail a b D C hfirst hleftPos
      (i.val - 2) (by omega) hiPreviousEven
  have hsum := b.lemma79Central_firstAlternative_targetAlphaSum c
    hdefectBC i hprevious
  have hcurrentAlpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
    linarith
  have hgap := lemma79Central_typeIEarly_leftSwitch_gap_eq_twoE_add_one
    a b D C hfirst i hleft hcurrentAlpha
  have hbLow := lemma79Central_typeIEarly_leftSwitch_targetLowOrder
    a b D C i hleft hgap
  rcases lemma79Central_typeIEarly_leftSwitch_baseOrders
      a b c D C hnorm i hleft hcross with ⟨hbCurrent, hcFirst, hcExtra⟩
  rcases hiEven with ⟨half, hhalfEq⟩
  have hhalfPos : 0 < half := by
    have := i.one_lt
    omega
  let pairs := half - 1
  have hiBound := i.lt_large
  have hlargeLength : 2 * (pairs + 1) = i.val := by
    simp only [pairs]
    omega
  have hsmallLength : 2 * pairs = i.val - 2 := by
    simp only [pairs]
    omega
  have hlargeLast : b.order ⟨2 * (pairs + 1) - 1, by omega⟩ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    have hindex : (⟨2 * (pairs + 1) - 1, by omega⟩ : Fin (n + 2)) =
        ⟨i.val - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hindex]
    exact hbLow
  have hextra : c.order ⟨2 * pairs, by omega⟩ = b.order 0 := by
    have hindex : (⟨2 * pairs, by omega⟩ : Fin (n + 2)) =
        ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hindex]
    exact hcExtra
  have hsmallClasses : AlternatingEndpointPairClasses
      (c.prefixValueUnits (2 * pairs) (by omega)) := by
    by_cases hpairsZero : pairs = 0
    · intro t
      exact Fin.elim0 (Fin.cast hpairsZero t)
    · have hpairs : 0 < pairs := Nat.pos_of_ne_zero hpairsZero
      have hiFour : 4 ≤ i.val := by omega
      have hcLow := lemma79Central_typeIEarly_first_even_comparisonLow
        b c i ⟨half, hhalfEq⟩ hiFour hgap hbLow hcFirst hcExtra hprevious
      have hsmallLast : c.order ⟨2 * pairs - 1, by omega⟩ =
          b.order 0 - 2 * (ramificationIndex K : Int) := by
        have hindex : (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) =
            ⟨i.val - 3, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hindex]
        exact hcLow
      exact c.lemma79_endpointTower_pairClasses (b.order 0) pairs
        hpairs (by omega) hcFirst hsmallLast
  have hsmallOrders : ∀ t : Fin pairs,
      ordUnit K ((c.prefixValueUnits (2 * pairs) (by omega))
        ⟨2 * t.val, by omega⟩) = b.order 0 := by
    by_cases hpairsZero : pairs = 0
    · intro t
      exact Fin.elim0 (Fin.cast hpairsZero t)
    · have hpairs : 0 < pairs := Nat.pos_of_ne_zero hpairsZero
      have hiFour : 4 ≤ i.val := by omega
      have hcLow := lemma79Central_typeIEarly_first_even_comparisonLow
        b c i ⟨half, hhalfEq⟩ hiFour hgap hbLow hcFirst hcExtra hprevious
      have hsmallLast : c.order ⟨2 * pairs - 1, by omega⟩ =
          b.order 0 - 2 * (ramificationIndex K : Int) := by
        have hindex : (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) =
            ⟨i.val - 3, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hindex]
        exact hcLow
      exact c.lemma79_endpointTower_leadingOrders (b.order 0) pairs
        hpairs (by omega) hcFirst hsmallLast
  have hrep := b.lemma79_endpointTower_onePairExtension c (b.order 0)
    pairs (by omega) rfl hlargeLast hsmallClasses hsmallOrders hextra
  exact prefixRepresents_cast c b (by omega) hlargeLength hrep

/-- Complete case 1 on the type-I early region, with parity selecting the
equal-tower or one-pair-extension construction. -/
theorem lemma79CentralWitness_typeIEarly_firstAlternative
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    Lemma79CentralWitness a b c i := by
  apply Lemma79CentralWitness.direct
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact lemma79Central_typeIEarly_first_even_direct
      a b c D C hfirst hdefectBC hnorm i hearly hiEven htriggerBC.1
        hprevious
  · exact lemma79Central_typeIEarly_first_odd_direct
      a b c D C hfirst hdefectBC hnorm i hearly hiOdd hprevious

end BONG.GoodBONG

end Bong
