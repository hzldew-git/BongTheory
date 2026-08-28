/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIRightExclusions

/-!
# Beli (2019), Lemma 7.9(iii): completion of the type-I right region

The first Lemma 2.18 alternative is localized to the first coordinate after
the right switch and is discharged by case 3.  For the second alternative,
an index before the last unequal coordinate again contradicts the adjacent
target-alpha bound.  At the last coordinate, Lemmas 7.2(i) and 6.6 show that
the mixed product has odd valuation, so its defect is zero; the remaining
target alpha is one.  This is case 9 of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the last type-I difference coordinate, the trigger cross inequality
and condition (i) put the third prefix in the Lemma 6.6(i) congruence class. -/
theorem lemma79Central_typeIRight_terminal_thirdPrefixParity
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hiLast : i.val = D.profile.last)
    (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Int.ModEq 2 (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) *
        (a.orderSequence.entryOrZero D.anchor + 1)) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hbCurrent := lemma79_typeI_caseSix_current_eq_reference_add_one
    a b D C hfirst (i.current i.lt_large.le) (by
      simp only [CentralRepresentationIndex.current]
      exact hright) (by
      simp only [CentralRepresentationIndex.current]
      omega) (by
      simpa only [CentralRepresentationIndex.current] using hiEven)
  have hbCurrentEntry : b.orderSequence.entryOrZero i.val =
      (a.orderSequence.entryOrZero D.anchor + 1) + 1 := by
    simpa only [CentralRepresentationIndex.current] using hbCurrent
  have hbCurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      a.orderSequence.entryOrZero D.anchor + 2 := by
    calc
      b.order ⟨i.val, i.lt_large⟩ =
          b.orderSequence.entryOrZero i.val := by
            simpa only using
              (b.orderSequence_entryOrZero_eq_order
                ⟨i.val, i.lt_large⟩).symm
      _ = a.orderSequence.entryOrZero D.anchor + 2 := by omega
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

/-- In terminal case 9, the target prefix and third prefix have an odd
signed product valuation. -/
theorem lemma79Central_typeIRight_terminal_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hiLast : i.val = D.profile.last)
    (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := a.orderSequence.entryOrZero D.anchor + 1
  have hleftRight : C.leftSwitch ≤ C.rightSwitch :=
    C.left_le_anchor.trans C.anchor_le_right
  have hb := a.lemma72_typeI_target_after_of_canonical
    b D C hfirst (i.val + 1) (by omega) (by omega)
  have hc := lemma79Central_typeIRight_terminal_thirdPrefixParity
    a b c D C hfirst horderBC i hright hiLast hiEven hcross
  apply lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEven (by
      have := i.one_lt
      omega) (Nat.succ_le_of_lt i.lt_large) T
  · convert hb using 1 <;> dsimp only [T] <;> ring
  · simpa only [T] using hc

/-- The terminal current mixed defect in case 9 is zero. -/
theorem lemma79Central_typeIRight_terminal_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hiLast : i.val = D.profile.last)
    (hiEven : Even i.val)
    (hcross : c.order ⟨i.val - 2, by
        have := i.lt_large
        omega⟩ < b.order ⟨i.val, i.lt_large⟩) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIRight_terminal_currentProduct_odd
    a b c D C hfirst horderBC i hright hiLast hiEven hcross

/-- The alpha selected at the last type-I difference coordinate is one. -/
theorem lemma79Central_typeIRight_terminal_currentAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hiLast : i.val = D.profile.last) :
    b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 1 := by
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  have hlastEven := lemma79_typeI_last_even
    a b D C hfirst hrightLast
  have hpreviousOdd : Odd (i.val - 1) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  apply beli2019Remark613_typeI_targetRightAlpha_eq_one
    a b D C hfirst hrightLast hdefect (i.val - 1)
  · rcases C.right_even with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    omega
  · omega
  · exact hpreviousOdd

set_option maxHeartbeats 3000000 in
-- The proof separates the ordinary right-tail bound from the terminal parity case.
/-- Case 9: the second Lemma 2.18 alternative is impossible throughout
the type-I right difference region. -/
theorem lemma79Central_typeIRight_secondAlternative_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hrightLast : C.rightSwitch < D.profile.last := by omega
  by_cases hiLast : i.val = D.profile.last
  · have hiEven : Even i.val := by
      simpa only [hiLast] using
        lemma79_typeI_last_even a b D C hfirst hrightLast
    have hzero := lemma79Central_typeIRight_terminal_currentDefect_eq_zero
      a b c D C hfirst horderBC i hright hiLast hiEven htriggerBC.1
    have hbeta := lemma79Central_typeIRight_terminal_currentAlpha_eq_one
      a b D C hfirst hab.defectCondition i hright hiLast
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, hzero, add_zero, hbeta] at hcurrent
    have hstrict : 2 * (ramificationIndex K : ℚ) < 1 := by
      exact_mod_cast hcurrent
    have heOneQ : (1 : ℚ) ≤ (ramificationIndex K : ℚ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (ramificationIndex_pos (K := K)))
    linarith
  · have hiBeforeLast : i.val < D.profile.last := by omega
    have hiNext : i.val + 1 < n + 2 :=
      (by omega : i.val + 1 ≤ D.profile.last) |>.trans_lt
        D.profile.lastDifference.bound
    have hcap :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.prefixAlphaCap (i.val + 1) := by
      apply hcurrent.trans_le
      apply add_le_add le_rfl
      unfold centralCurrentDefect
      exact b.truncatedPrefixDefect_le_leftCap c (-1)
        (i.val + 1) (i.val - 1)
    rw [b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) i.lt_large,
      b.prefixAlphaCap_of_internal (by
          have := i.one_lt
          omega) hiNext] at hcap
    have hsum : 2 * (ramificationIndex K : ℚ) <
        b.alphaValue ⟨i.val - 1, by omega⟩ +
          b.alphaValue ⟨i.val, by omega⟩ := by
      exact_mod_cast hcap
    let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by omega⟩
    have hnot :=
      lemma79Central_typeIRight_not_leftAlphaSum_of_not_boundary
        a b D C hfirst hab.defectCondition j (by
          simp only [j]
          omega) (by simp only [j]; omega) (by
          simp only [j]
          omega)
    apply hnot
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum

set_option maxHeartbeats 4000000 in
-- The complete dispatcher keeps the two Lemma 2.18 alternatives explicit.
/-- The complete central witness family on the type-I right region. -/
theorem lemma79CentralWitness_typeIRight
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last)
    (htriggerBC : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htriggerBC with
    hprevious | hcurrent
  · by_cases hi : i.val = C.rightSwitch + 1
    · exact .viaCertificate
        (lemma79CentralCertificate_typeIRightBoundary
          a b c D C hfirst hab hac horderBC hdefectBC i hi
            hthroughLast htriggerBC hprevious)
    · exfalso
      apply lemma79Central_typeIRight_not_leftAlphaSum_of_not_boundary
        a b D C hfirst hab.defectCondition i hright hthroughLast hi
      have hcomparison : b.representationAlpha c i.previous ≤
          b.prefixAlphaCap (i.val - 1) := by
        calc
          b.representationAlpha c i.previous =
              b.representationAlphaValue c i.previous := by
            rw [b.coe_representationAlphaValue c i.previous]
          _ ≤ b.truncatedPrefixDefect c 1 (i.val - 1)
              (i.val - 1) := by
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
            b.alphaValue ⟨i.val - 2, by
              have := i.lt_large
              omega⟩ := by
        exact_mod_cast hcap
      rw [add_comm]
      exact hsum
  · exact False.elim
      (lemma79Central_typeIRight_secondAlternative_impossible
        a b c D C hfirst hab horderBC i hright hthroughLast
          htriggerBC hcurrent)

end BONG.GoodBONG

end Bong
