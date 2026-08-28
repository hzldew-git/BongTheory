/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIIRightExclusions

/-!
# Beli (2019), Lemma 7.9(iii): complete type-II right region

The adjacent-alpha bounds exclude case 3 and every nonterminal instance of
case 9.  At the final difference coordinate, Lemmas 7.2(ii) and 6.6 put the
two shifted prefixes in opposite parity classes.  Thus the mixed defect is
zero, while the selected target alpha is one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the last type-II difference coordinate, the target prefix of length
`i + 1` and comparison prefix of length `i - 1` have opposite parity. -/
theorem lemma79Central_typeIIRight_terminal_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hbaseLast := D.outer.right_le_last
  have hbaseI : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
  have hiEven : Even
      (i.val - (D.outer.transition.firstTwo - 1)) := by
    simpa only [hiLast] using D.outer.right_even_distance
  have htargetCurrent := D.outer.target_rightEven_eq_boundary
    i.val hbaseI (by omega) hiEven
  have htargetCurrentOrder : b.order ⟨i.val, i.lt_large⟩ = T + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order]
    simpa only [T, D.right_target] using htargetCurrent
  have hcCurrent : c.orderSequence.entryOrZero (i.val - 2) ≤ T := by
    have hcross := htrigger.1
    rw [htargetCurrentOrder] at hcross
    rw [c.orderSequence_entryOrZero_eq_order ⟨i.val - 2, by
      have := i.lt_large
      omega⟩]
    omega
  have hfirstLower :=
    beli2019Lemma79_typeII_caseSix_reference_le_thirdFirst
      a b c D hfirst hnorm
  have hcRaw := c.prefixSum_modEq_mul_of_current_le_reference_le_first
    T (i.val - 2) (by
      have := i.lt_large
      omega) (by simpa only [T] using hfirstLower) hcCurrent
  have hc : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * T) := by
    simpa only [show i.val - 2 + 1 = i.val - 1 by
      have := i.one_lt
      omega] using hcRaw
  let P := a.beli2019Lemma72_ii b D hfirst
  have hbRaw := P.target_after (i.val + 1) (by omega) (by omega)
  have hb : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * (T + 1) +
        ((D.outer.transition.firstTwo - 1 : Nat) : Int)) := by
    simpa only [P, T] using hbRaw
  have hsumMod := hb.add hc
  have hformulaOdd : Odd
      (((i.val + 1 : Nat) : Int) * (T + 1) +
        ((D.outer.transition.firstTwo - 1 : Nat) : Int) +
        ((i.val - 1 : Nat) : Int) * T) := by
    have hrecover := Nat.sub_add_cancel hbaseI
    rcases hiEven with ⟨d, hd⟩
    have hiCast : (i.val : Int) =
        ((D.outer.transition.firstTwo - 1 : Nat) : Int) +
          (d : Int) + (d : Int) := by
      exact_mod_cast (show i.val =
        (D.outer.transition.firstTwo - 1) + d + d by omega)
    rw [Nat.cast_sub i.one_lt.le]
    push_cast
    refine ⟨(i.val : Int) * T +
      ((D.outer.transition.firstTwo - 1 : Nat) : Int) + (d : Int), ?_⟩
    rw [hiCast]
    ring
  have hsumOdd : Odd
      (b.orderSequence.prefixSum (i.val + 1) +
        c.orderSequence.prefixSum (i.val - 1)) :=
    caseSix_odd_of_modEq_two_of_odd hsumMod hformulaOdd
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨i.val, by have := i.one_lt; omega, i.lt_large, i.lt_large.le⟩
  have hproduct := signed_shifted_prefixProduct_order_odd_of_sum_odd
    b c idx (by simpa only [idx] using hsumOdd)
  change Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
    c.prefixProduct (i.val - 1))) at hproduct
  exact hproduct

/-- Hence the terminal type-II mixed-prefix defect in case 9 is zero. -/
theorem lemma79Central_typeIIRight_terminal_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIIRight_terminal_currentProduct_odd
    a b c D hfirst hnorm i hright hiLast htrigger

/-- The alpha immediately before the final type-II boundary is one. -/
theorem lemma79Central_typeIIRight_terminal_currentAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hiLast : i.val = D.outer.last) :
    b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 1 := by
  have hlastEven := D.outer.right_even_distance
  have hbaseLast := D.outer.right_le_last
  have hrecover := Nat.sub_add_cancel hbaseLast
  have hseparated := D.outer.transition.separated
  have hpreviousOdd : Odd
      ((i.val - 1) - (D.outer.transition.firstTwo - 1)) := by
    rcases hlastEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousRight : D.outer.transition.firstTwo ≤ i.val - 1 := by
    rcases hlastEven with ⟨d, hd⟩
    omega
  have hpreviousBefore : i.val - 1 < D.outer.last := by
    have := i.one_lt
    omega
  exact a.beli2019Remark613_typeII_targetRightAlpha_eq_one_local
    b D horder hdefect htotal (i.val - 1) hpreviousRight
      hpreviousBefore hpreviousOdd

set_option maxHeartbeats 2000000 in
-- The proof separates the terminal parity computation from the ordinary tail bound.
/-- Case 9: the second Lemma 2.18 alternative is impossible throughout the
type-II right difference region. -/
theorem lemma79Central_typeIIRight_secondAlternative_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  by_cases hiLast : i.val = D.outer.last
  · have hzero := lemma79Central_typeIIRight_terminal_currentDefect_eq_zero
      a b c D hfirst hnorm i hright hiLast htrigger
    have hbeta := lemma79Central_typeIIRight_terminal_currentAlpha_eq_one
      a b D hab.orderCondition hab.defectCondition htotal i hright hiLast
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, hzero, add_zero, hbeta] at hcurrent
    have hstrict : 2 * (ramificationIndex K : ℚ) < 1 := by
      exact_mod_cast hcurrent
    have heOne : (1 : ℚ) ≤ ramificationIndex K := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (ramificationIndex_pos (K := K)))
    linarith
  · have hiBeforeLast : i.val < D.outer.last := by omega
    have hiNext : i.val + 1 < n + 2 := by
      have hbound := D.outer.lastDifference.bound
      omega
    have hsum := b.lemma79Central_secondAlternative_targetAlphaSum
      c i hiNext hcurrent
    let j : CentralRepresentationIndex (n + 2) (n + 2) :=
      ⟨i.val + 1, by
        have := i.one_lt
        omega, hiNext, by omega⟩
    have hnot := lemma79Central_typeIIRight_not_leftAlphaSum
      a b D hfirst hab.orderCondition hab.defectCondition htotal j (by
        simp only [j]
        omega) (by simp only [j]; omega)
    apply hnot
    simpa only [j, show i.val + 1 - 2 = i.val - 1 by omega,
      show i.val + 1 - 1 = i.val by omega] using hsum

/-- Complete central witness family on the type-II right interval. -/
theorem lemma79CentralWitness_typeIIRight
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hab : RepresentationConditions a b le_rfl)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
    hprevious | hcurrent
  · exfalso
    apply lemma79Central_typeIIRight_not_leftAlphaSum
      a b D hfirst hab.orderCondition hab.defectCondition htotal i
        hright hthroughLast
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
      (lemma79Central_typeIIRight_secondAlternative_impossible
        a b c D hfirst hab htotal hnorm i hright hthroughLast
          htrigger hcurrent)

end BONG.GoodBONG

end Bong
