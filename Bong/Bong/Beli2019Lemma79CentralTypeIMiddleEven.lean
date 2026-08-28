/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIMiddle
import Bong.Bong.Beli2019Lemma79EvenTargetParity

/-!
# Beli (2019), Lemma 7.9(iii), case 6: the even type-I middle interval

At an even boundary between the canonical type-I switches, the first
alternative of Lemma 2.18 is excluded by the constant even target plateau.
For the second alternative, Lemmas 7.2(i) and 6.6(i) show that the signed
product of the target prefix of length `i + 1` and the third prefix of
length `i - 1` has odd valuation.  Its truncated defect is therefore zero.

The remaining strict inequality would force the current target alpha above
`2e`.  The two equal even target orders on either side of that alpha and
Lemma 6.6(i) instead put the intervening order gap, hence the alpha, at most
`2e`.  This is case 6 of the printed proof.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The target order at an even type-I middle coordinate is the canonical
reference order plus two. -/
theorem lemma79Central_typeIMiddle_even_targetOrder
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) :
    b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero D.anchor + 2 := by
  have hplateau := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hleft.le hright hiEven
  have hboundary := C.target_from_left C.leftSwitch le_rfl
    C.left_le_anchor C.left_even
  exact hplateau.symm.trans hboundary

/-- The first target order is at least one above the canonical source
reference.  This formulation also covers a zero left switch. -/
theorem lemma79Central_typeI_targetFirst_ge_reference_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D) :
    a.orderSequence.entryOrZero D.anchor + 1 ≤
      b.orderSequence.entryOrZero 0 := by
  by_cases hzero : C.leftSwitch = 0
  · have hvalue := C.target_from_left 0 (by omega)
      (by simpa only [hzero] using C.left_le_anchor) ⟨0, by omega⟩
    omega
  · have hvalue := C.target_before_left 0 (Nat.pos_of_ne_zero hzero)
      ⟨0, by omega⟩
    omega

/-- The trigger cross inequality and condition (i) give the two endpoint
bounds needed to apply Lemma 6.6(i) to the third BONG prefix. -/
theorem lemma79Central_typeIMiddle_even_thirdPrefixParity
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) (hcross :
      c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Int.ModEq 2 (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 1)) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hbCurrent := lemma79Central_typeIMiddle_even_targetOrder
    a b D C hfirst i hleft hright hiEven
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

/-- In the even type-I middle case, the signed mixed prefix occurring in
the current defect has odd valuation. -/
theorem lemma79Central_typeIMiddle_even_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) (hcross :
      c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hb := a.lemma72_typeI_target_after_of_canonical
    b D C hfirst (i.val + 1) (by omega) (by
      have hlast := C.right_le_last
      omega)
  have hc := lemma79Central_typeIMiddle_even_thirdPrefixParity
    a b c D C hfirst horderBC i hleft hright hiEven hcross
  apply lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEven (by
      have := i.one_lt
      omega) (Nat.succ_le_of_lt i.lt_large) T
  · convert hb using 1 <;> dsimp only [T] <;> ring
  · simpa only [T] using hc

/-- Consequently the current mixed prefix defect in case 6 is zero. -/
theorem lemma79Central_typeIMiddle_even_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) (hcross :
      c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIMiddle_even_currentProduct_odd
    a b c D C hfirst horderBC i hleft hright hiEven hcross

/-- The target alpha selected by the second Lemma 2.18 alternative is at
most `2e`, because its two neighboring even target orders are equal. -/
theorem lemma79Central_typeIMiddle_even_currentAlpha_le_twoE
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) :
    b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ ≤
      2 * (ramificationIndex K : ℚ) := by
  let previous : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let current : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let gap : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  have hiPreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hleftPrevious : C.leftSwitch ≤ i.val - 2 := by
    rcases C.left_even with ⟨d, hd⟩
    rcases hiEven with ⟨e, he⟩
    omega
  have hprevious := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) hleftPrevious (by omega) hiPreviousEven
  have hcurrent := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hleft.le hright hiEven
  have horders : b.order previous = b.order current := by
    rw [← b.orderSequence_entryOrZero_eq_order previous,
      ← b.orderSequence_entryOrZero_eq_order current]
    exact hprevious.symm.trans hcurrent
  have hsegment := b.beli2019Lemma66_i previous current (by
      change i.val - 2 ≤ i.val
      omega) (by
      change Even (i.val - (i.val - 2))
      exact ⟨1, by
        have := i.one_lt
        omega⟩) horders
  have hgap : b.orderGap gap ≤ 2 * (ramificationIndex K : Int) :=
    hsegment.gap_le gap (by
      change i.val - 2 ≤ i.val - 1
      omega) (by
      change i.val - 1 < i.val
      omega)
  simpa only [gap] using
    (b.alphaValue_le_twoE_iff_orderGap_le_twoE gap).2 hgap

set_option maxHeartbeats 3000000 in
-- The proof combines the two Lemma 2.18 branches with the parity calculation.
/-- Case 6 of Lemma 7.9(iii): an even index in the type-I middle interval
cannot satisfy the central trigger. -/
theorem lemma79Central_typeIMiddle_even_not_trigger
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : C.leftSwitch < i.val) (hright : i.val ≤ C.rightSwitch)
    (hiEven : Even i.val) :
    ¬ b.centralAlphaTrigger c i := by
  intro htrigger
  have hleftNot := lemma79Central_typeIMiddle_not_leftAlphaSum_of_even
    a b D C hfirst i hleft hright hiEven
  rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
    hprevious | hcurrent
  · apply hleftNot
    have hcomparison : b.representationAlpha c i.previous ≤
        b.prefixAlphaCap (i.val - 1) := by
      calc
        b.representationAlpha c i.previous =
            b.representationAlphaValue c i.previous := by
          rw [b.coe_representationAlphaValue c i.previous]
        _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1) := by
          simpa only [CentralRepresentationIndex.previous] using
            hdefectBC i.previous
        _ ≤ b.prefixAlphaCap (i.val - 1) :=
          b.truncatedPrefixDefect_le_leftCap c 1
            (i.val - 1) (i.val - 1)
    have hcap := hprevious.trans_le (add_le_add le_rfl hcomparison)
    rw [b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) i.lt_large,
      b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) (by
          have := i.lt_large
          omega)] at hcap
    have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ +
          b.alphaValue ⟨i.val - 1 - 1, by
            have := i.lt_large
            omega⟩ := by
      exact_mod_cast hcap
    have hindex : (⟨i.val - 1 - 1, by
        have := i.lt_large
        omega⟩ : Fin (n + 1)) = ⟨i.val - 2, by
          have := i.lt_large
          omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hindex] at hsum
    calc
      2 * (ramificationIndex K : ℚ) <
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ +
            b.alphaValue ⟨i.val - 2, by
              have := i.lt_large
              omega⟩ := hsum
      _ = b.alphaValue ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ +
          b.alphaValue ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := add_comm _ _
  · have hzero := lemma79Central_typeIMiddle_even_currentDefect_eq_zero
      a b c D C hfirst horderBC i hleft hright hiEven htrigger.1
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, hzero,
      add_zero] at hcurrent
    have hstrict : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by
          have := i.lt_large
          omega⟩ := by
      exact_mod_cast hcurrent
    exact (not_lt_of_ge
      (lemma79Central_typeIMiddle_even_currentAlpha_le_twoE
        a b D C hfirst i hleft hright hiEven)) hstrict

end BONG.GoodBONG

end Bong
