/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIEarlyFirst

/-!
# Beli (2019), Lemma 7.9(iii), case 5 for type I

This file treats the second Lemma 2.18 alternative in the early type-I
region.  The even branch is forced to the first canonical switch.  At that
switch the mixed prefix product has odd valuation, hence zero truncated
defect; the remaining endpoint arithmetic gives the one-pair extension
appearing in the printed proof.  The odd branch is excluded separately.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the first type-I switch the current target order is the canonical
reference order plus two. -/
theorem lemma79Central_typeIEarly_boundary_targetOrder
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch) :
    b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero D.anchor + 2 := by
  have hboundary := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  simpa only [hleft] using hboundary

/-- The order trigger and condition (i) determine the parity of the
comparison prefix of length `i - 1` at the first type-I switch. -/
theorem lemma79Central_typeIEarly_boundary_thirdPrefixParity
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch) (hcross :
      c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Int.ModEq 2 (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 1)) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hbCurrent := lemma79Central_typeIEarly_boundary_targetOrder
    a b D C i hleft
  have hbCurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    rw [← b.orderSequence_entryOrZero_eq_order
      (⟨i.val, i.lt_large⟩ : Fin (n + 2))]
    simpa using hbCurrent
  have hcCurrent : c.orderSequence.entryOrZero (i.val - 2) ≤ T := by
    let current : Fin (n + 2) := ⟨i.val - 2, by
      have := i.lt_large
      omega⟩
    have hcurrentOrder : c.order current ≤ T := by
      dsimp only [current, T]
      omega
    rw [← c.orderSequence_entryOrZero_eq_order current] at hcurrentOrder
    simpa only [current] using hcurrentOrder
  have hbFirst := lemma79Central_typeI_targetFirst_ge_reference_add_one
    a b D C
  have hbcFirst := horderBC (0 : Fin (n + 2))
  have hcFirst : T ≤ c.orderSequence.entryOrZero 0 := by
    rcases hbcFirst with hle | ⟨hpositive, _⟩
    · have hle' : b.orderSequence.entryOrZero 0 ≤
          c.orderSequence.entryOrZero 0 := by
        rw [b.orderSequence.entryOrZero_of_lt (by omega),
          c.orderSequence.entryOrZero_of_lt (by omega)]
        exact hle
      exact (by simpa only [T] using hbFirst.trans hle')
    · change 0 < 0 at hpositive
      omega
  have hmod := c.prefixSum_modEq_mul_of_current_le_reference_le_first
    T (i.val - 2) (by
      have := i.lt_large
      omega) hcFirst hcCurrent
  have hlength : i.val - 2 + 1 = i.val - 1 := by
    have := i.one_lt
    omega
  rw [hlength] at hmod
  simpa only [T] using hmod

/-- The signed mixed prefix at the first even switch has odd valuation. -/
theorem lemma79Central_typeIEarly_boundary_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch) (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hb := a.lemma72_typeI_target_after_of_canonical
    b D C hfirst (i.val + 1) (by omega) (by
      have hlast := C.left_le_anchor.trans D.profile.anchor_le_last
      omega)
  have hc := lemma79Central_typeIEarly_boundary_thirdPrefixParity
    a b c D C horderBC i hleft hcross
  apply lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEven (by
      have := i.one_lt
      omega) (Nat.succ_le_of_lt i.lt_large) T
  · convert hb using 1 <;> dsimp only [T] <;> ring
  · simpa only [T] using hc

/-- Consequently the current mixed-prefix defect in case 5 is zero. -/
theorem lemma79Central_typeIEarly_boundary_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch) (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIEarly_boundary_currentProduct_odd
    a b c D C hfirst horderBC i hleft hiEven hcross

/-- In the nonempty even branch of case 5, the trigger and the vanishing
mixed defect force the last entry of the shorter comparison tower to be
the low endpoint `R - 2e`. -/
theorem lemma79Central_typeIEarly_second_even_comparisonLow
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiFour : 4 ≤ i.val)
    (hdefectZero : b.centralCurrentDefect c i = 0)
    (hbLow : b.order ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int))
    (hbCurrent : b.order ⟨i.val, i.lt_large⟩ = b.order 0 + 1)
    (hcFirst : c.order 0 = b.order 0)
    (hcExtra : c.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.lt_large
      omega⟩ = b.order 0)
    (htrigger : b.centralAlphaTrigger c i) :
    c.order ⟨i.val - 3, by
      have := i.lt_large
      omega⟩ = b.order 0 - 2 * (ramificationIndex K : Int) := by
  have hiBound := i.lt_large
  let comparisonBefore : Fin (n + 2) := ⟨i.val - 4, by omega⟩
  let comparisonFar : Fin (n + 2) := ⟨i.val - 3, by omega⟩
  let comparisonNear : Fin (n + 2) := ⟨i.val - 2, by omega⟩
  let comparisonGap : Fin (n + 1) := ⟨i.val - 4, by omega⟩
  have hbound := b.centralAdjustedAlpha_le_currentOrder_add_defect c i
  rw [hdefectZero, add_zero] at hbound
  have hsumBound :
      ((b.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
          b.centralAdjustedAlpha c i ≤
        ((b.representationAlphaValue c i.previous : ℚ) : WithTop ℚ) +
          (((b.order ⟨i.val, i.lt_large⟩ : Int) : ℚ) : WithTop ℚ) :=
    add_le_add le_rfl hbound
  have hfull := htrigger.2.trans_le hsumBound
  have hfullQ :
      2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 1, by omega⟩ : ℚ) <
        b.representationAlphaValue c i.previous +
          (b.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast hfull
  have hrepresentationLower : (-1 : ℚ) <
      b.representationAlphaValue c i.previous := by
    rw [hbLow, hbCurrent] at hfullQ
    push_cast at hfullQ
    linarith
  have haverage := b.lemma79Central_previousAlpha_le_endpointAverage c i
    (by omega)
  have haverageQ : b.representationAlphaValue c i.previous ≤
      (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) := by
    exact_mod_cast haverage
  have hstrictAverage : (-1 : ℚ) <
      (b.order ⟨i.val - 1, by omega⟩ : ℚ) -
        ((c.order comparisonFar : ℚ) +
          (c.order comparisonNear : ℚ)) / 2 +
        (ramificationIndex K : ℚ) :=
    hrepresentationLower.trans_le haverageQ
  have hfarUpperQ : (c.order comparisonFar : ℚ) <
      (b.order 0 : ℚ) - 2 * (ramificationIndex K : ℚ) + 2 := by
    have hcNear : c.order comparisonNear = b.order 0 := by
      simpa only [comparisonNear] using hcExtra
    rw [hbLow, hcNear] at hstrictAverage
    push_cast at hstrictAverage
    linarith
  have hfarUpper : c.order comparisonFar <
      b.order 0 - 2 * (ramificationIndex K : Int) + 2 := by
    exact_mod_cast hfarUpperQ
  have hiBeforeEven : Even (i.val - 4) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 2, by omega⟩
  have hzeroBeforeRaw := c.orderSequence.entryOrZero_le_of_evenGap
    0 (i.val - 4) (Nat.zero_le _) (by omega) hiBeforeEven
  have hzeroBefore : c.order 0 ≤ c.order comparisonBefore := by
    calc
      c.order 0 = c.orderSequence.entryOrZero 0 :=
        (c.orderSequence_entryOrZero_eq_order (0 : Fin (n + 2))).symm
      _ ≤ c.orderSequence.entryOrZero (i.val - 4) := hzeroBeforeRaw
      _ = c.order comparisonBefore := by
        simpa only [comparisonBefore] using
          c.orderSequence_entryOrZero_eq_order comparisonBefore
  have hbeforeNearRaw := c.orderSequence.entryOrZero_le_of_evenGap
    (i.val - 4) (i.val - 2) (by omega) (by omega) ⟨1, by omega⟩
  have hbeforeNear : c.order comparisonBefore ≤
      c.order comparisonNear := by
    calc
      c.order comparisonBefore =
          c.orderSequence.entryOrZero (i.val - 4) := by
        simpa only [comparisonBefore] using
          (c.orderSequence_entryOrZero_eq_order comparisonBefore).symm
      _ ≤ c.orderSequence.entryOrZero (i.val - 2) := hbeforeNearRaw
      _ = c.order comparisonNear := by
        simpa only [comparisonNear] using
          c.orderSequence_entryOrZero_eq_order comparisonNear
  have hbefore : c.order comparisonBefore = b.order 0 := by
    have hcNear : c.order comparisonNear = b.order 0 := by
      simpa only [comparisonNear] using hcExtra
    omega
  have hgapLowerRaw := c.orderGap_ge_neg_two_mul_e comparisonGap
  have hgapLower : -(2 * (ramificationIndex K : Int)) ≤
      c.order comparisonFar - c.order comparisonBefore := by
    unfold orderGap at hgapLowerRaw
    have hsucc : comparisonGap.succ = comparisonFar := by
      apply Fin.ext
      simp only [comparisonGap, comparisonFar, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonBefore := by
      apply Fin.ext
      rfl
    simpa only [hsucc, hcast] using hgapLowerRaw
  have hgapUpper : c.orderGap comparisonGap <
      2 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    have hsucc : comparisonGap.succ = comparisonFar := by
      apply Fin.ext
      simp only [comparisonGap, comparisonFar, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonBefore := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hbefore]
    omega
  have hePos : 0 < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos (K := K)
  have hgapNegative : c.orderGap comparisonGap < 0 := by omega
  have hgapEven := c.orderGap_even_of_negative comparisonGap hgapNegative
  have hgapExact : c.orderGap comparisonGap =
      -(2 * (ramificationIndex K : Int)) := by
    rcases hgapEven with ⟨z, hz⟩
    omega
  have hfar : c.order comparisonFar =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap at hgapExact
    have hsucc : comparisonGap.succ = comparisonFar := by
      apply Fin.ext
      simp only [comparisonGap, comparisonFar, Fin.val_succ]
      omega
    have hcast : comparisonGap.castSucc = comparisonBefore := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast, hbefore] at hgapExact
    omega
  simpa only [comparisonFar] using hfar

/-- Case 5, even branch: after the mixed defect vanishes, the target
endpoint tower has one additional binary pair and the final comparison
entry supplies its unary extension. -/
theorem lemma79Central_typeIEarly_second_even_direct
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiEven : Even i.val)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  have hleft := lemma79Central_typeIEarly_even_eq_leftSwitch
    a b c D C hnorm i hearly hiEven htrigger.1
  have hdefectZero :=
    lemma79Central_typeIEarly_boundary_currentDefect_eq_zero
      a b c D C hfirst horderBC i hleft hiEven htrigger.1
  have hcurrentAlpha : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by
        have := i.lt_large
        omega⟩ := by
    rw [hdefectZero, add_zero,
      b.prefixAlphaCap_of_internal (by
        have := i.one_lt
        omega) i.lt_large] at hcurrent
    exact_mod_cast hcurrent
  have hgap := lemma79Central_typeIEarly_leftSwitch_gap_eq_twoE_add_one
    a b D C hfirst i hleft (by linarith)
  have hbLow := lemma79Central_typeIEarly_leftSwitch_targetLowOrder
    a b D C i hleft hgap
  rcases lemma79Central_typeIEarly_leftSwitch_baseOrders
      a b c D C hnorm i hleft htrigger.1 with
    ⟨hbCurrent, hcFirst, hcExtra⟩
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
      have hcLow := lemma79Central_typeIEarly_second_even_comparisonLow
        b c i ⟨half, hhalfEq⟩ hiFour hdefectZero hbLow hbCurrent
          hcFirst hcExtra htrigger
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
      have hcLow := lemma79Central_typeIEarly_second_even_comparisonLow
        b c i ⟨half, hhalfEq⟩ hiFour hdefectZero hbLow hbCurrent
          hcFirst hcExtra htrigger
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

/-- Case 5, odd branch: the right adjacent-alpha sum first forces the
exceptional coordinate immediately before the switch.  Its switch gap is
then `2e + 1`, making the target order `R - 2e`; condition (i) and the norm
floor put the comparison order on the opposite side of the strict trigger. -/
theorem lemma79Central_typeIEarly_second_odd_not
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch) (hiOdd : Odd i.val)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hiStrict : i.val < C.leftSwitch := by
    rcases hiOdd with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hiNext : i.val + 1 < n + 2 := by
    have hleftBound := C.left_le_anchor.trans_lt D.anchor_bound
    omega
  have hcurrentCap : b.centralCurrentDefect c i ≤
      b.prefixAlphaCap (i.val + 1) :=
    b.centralCurrentDefect_le_leftCap c i
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) :=
    hcurrent.trans_le (add_le_add le_rfl hcurrentCap)
  rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large,
    b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) hiNext] at hsumTop
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by omega⟩ +
        b.alphaValue ⟨i.val, by omega⟩ := by
    exact_mod_cast hsumTop
  have hboundary : i.val + 1 = C.leftSwitch := by
    by_contra hne
    have hfarEarly : i.val + 1 < C.leftSwitch := by omega
    let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by
          have := i.le_small_succ
          omega⟩
    have hsumJ : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨j.val - 2, by
          have := j.lt_large
          omega⟩ +
          b.alphaValue ⟨j.val - 1, by
            have := j.lt_large
            omega⟩ := by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
        show i.val + 1 - 1 = i.val by omega] using hsum
    have hstrict := b.order_twoStep_lt_of_alphaSum_gt_twoE j hsumJ
    have hpreviousEven : Even (i.val - 1) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d, by omega⟩
    have hnextEven : Even (i.val + 1) := by
      rcases hiOdd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hprevious := C.target_before_left (i.val - 1) (by omega)
      hpreviousEven
    have hnext := C.target_before_left (i.val + 1) hfarEarly hnextEven
    have heq : b.order ⟨i.val - 1, by omega⟩ =
        b.order ⟨i.val + 1, hiNext⟩ := by
      rw [← b.orderSequence_entryOrZero_eq_order,
        ← b.orderSequence_entryOrZero_eq_order]
      exact hprevious.trans hnext.symm
    have hstrict' : b.order ⟨i.val - 1, by omega⟩ <
        b.order ⟨i.val + 1, hiNext⟩ := by
      simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega] using hstrict
    exact (ne_of_lt hstrict') heq
  have hleftPos : 0 < C.leftSwitch := by omega
  have hiPreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hpreviousAlpha : b.alphaValue ⟨i.val - 1, by omega⟩ ≤ 1 :=
    beli2019Lemma69_i_typeI_targetLeftTail a b D C hfirst hleftPos
      (i.val - 1) (by omega) hiPreviousEven
  have hcurrentAlpha : 2 * (ramificationIndex K : ℚ) - 1 <
      b.alphaValue ⟨i.val, by omega⟩ := by
    linarith
  let j : CentralRepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val + 1, by
      have := i.one_lt
      omega, hiNext, by
        have := i.le_small_succ
        omega⟩
  have hjLeft : j.val = C.leftSwitch := by
    simpa only [j] using hboundary
  have hgapJ := lemma79Central_typeIEarly_leftSwitch_gap_eq_twoE_add_one
    a b D C hfirst j hjLeft (by
      simpa only [j, show i.val + 1 - 1 = i.val by omega] using
        hcurrentAlpha)
  have hbLowJ := lemma79Central_typeIEarly_leftSwitch_targetLowOrder
    a b D C j hjLeft hgapJ
  have hbLow : b.order ⟨i.val, i.lt_large⟩ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    simpa only [j, show i.val + 1 - 1 = i.val by omega] using hbLowJ
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le D.anchor)
    ⟨0, by omega⟩
  have htargetZero := C.target_before_left 0 hleftPos ⟨0, by omega⟩
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
  have hcZero : b.order 0 ≤ c.order 0 := by omega
  let firstGap : Fin (n + 1) := ⟨0, by omega⟩
  have hfirstGapRaw := c.orderGap_ge_neg_two_mul_e firstGap
  have hcOne : c.order 0 - 2 * (ramificationIndex K : Int) ≤
      c.order ⟨1, by omega⟩ := by
    unfold orderGap at hfirstGapRaw
    have hsucc : firstGap.succ = (⟨1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hcast : firstGap.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at hfirstGapRaw
    omega
  have hdistanceEven : Even ((i.val - 2) - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hiThree : 3 ≤ i.val := by
    rcases hiOdd with ⟨d, hd⟩
    have := i.one_lt
    omega
  have hmonotoneRaw := c.orderSequence.entryOrZero_le_of_evenGap
    1 (i.val - 2) (by omega) (by omega) hdistanceEven
  have hmonotone : c.order ⟨1, by omega⟩ ≤
      c.order ⟨i.val - 2, by omega⟩ := by
    rw [← c.orderSequence_entryOrZero_eq_order,
      ← c.orderSequence_entryOrZero_eq_order]
    exact hmonotoneRaw
  have hcLower : b.order 0 - 2 * (ramificationIndex K : Int) ≤
      c.order ⟨i.val - 2, by omega⟩ := by
    omega
  have hcross := htrigger.1
  rw [hbLow] at hcross
  exact (not_lt_of_ge hcLower) hcross

/-- Complete case 5 on the type-I early region.  Even indices use the
endpoint-tower construction; odd indices contradict the trigger. -/
theorem lemma79CentralWitness_typeIEarly_secondAlternative
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) :
    Lemma79CentralWitness a b c i := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact .direct (lemma79Central_typeIEarly_second_even_direct
      a b c D C hfirst horderBC hnorm i hearly hiEven htrigger hcurrent)
  · exact False.elim (lemma79Central_typeIEarly_second_odd_not
      a b c D C hfirst hnorm i hearly hiOdd htrigger hcurrent)

/-- The complete witness family on the type-I early interval, assembling
cases 1 and 5 through the two alternatives of Lemma 2.18. -/
theorem lemma79CentralWitness_typeIEarly
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ C.leftSwitch)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
    hprevious | hcurrent
  · exact lemma79CentralWitness_typeIEarly_firstAlternative
      a b c D C hfirst hdefectBC hnorm i hearly htrigger hprevious
  · exact lemma79CentralWitness_typeIEarly_secondAlternative
      a b c D C hfirst horderBC hnorm i hearly htrigger hcurrent

end BONG.GoodBONG

end Bong
