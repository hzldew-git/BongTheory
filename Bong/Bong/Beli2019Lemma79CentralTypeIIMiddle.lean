/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIIEarly
import Bong.Bong.Beli2019Lemma79CentralExclusions
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeII

/-!
# Beli (2019), Lemma 7.9(iii): middle type II

The first alternative of Lemma 2.18 is impossible because the two target
alphas immediately to the left are one.  The second alternative has the same
elementary contradiction away from the right transition.  At the remaining
boundary `i = firstTwo - 1`, Lemmas 7.2(ii) and 6.6 show that the shifted mixed
prefix product has odd order.  Its truncated defect is therefore zero and the
remaining target alpha is one.  This is case 7 of the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At `i = firstTwo - 1`, the target prefix and the comparison prefix
have opposite parity. -/
theorem lemma79Central_typeIIMiddle_boundary_currentProduct_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val + 1 = D.outer.transition.firstTwo)
    (htrigger : b.centralAlphaTrigger c i) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
  have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by omega
  have hthroughLast : i.val ≤ D.outer.last := by
    have hrightLast := D.outer.right_le_last
    omega
  have heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)) := by
    exact ⟨0, by omega⟩
  have htargetCurrent := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
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
  have hbRaw := P.target_after (i.val + 1) (by omega) (by
    have hrightLast := D.outer.right_le_last
    omega)
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
    rw [← hboundary]
    simp only [Nat.add_sub_cancel]
    rw [Nat.cast_sub i.one_lt.le]
    have hiCast : ((i.val + 1 : Nat) : Int) = (i.val : Int) + 1 := by
      exact_mod_cast rfl
    rw [hiCast]
    norm_num
    refine ⟨(i.val : Int) * T + (i.val : Int), by ring⟩
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

/-- Consequently the current mixed-prefix defect at the type-II transition
boundary is zero. -/
theorem lemma79Central_typeIIMiddle_boundary_currentDefect_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val + 1 = D.outer.transition.firstTwo)
    (htrigger : b.centralAlphaTrigger c i) :
    b.centralCurrentDefect c i = 0 := by
  unfold centralCurrentDefect
  apply truncatedPrefixDefect_eq_zero_of_odd_order_general
  exact lemma79Central_typeIIMiddle_boundary_currentProduct_odd
    a b c D hfirst hnorm i hboundary htrigger

/-- The target alpha selected at the exceptional type-II boundary is one. -/
theorem lemma79Central_typeIIMiddle_boundary_currentAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val + 1 = D.outer.transition.firstTwo) :
    b.alphaValue ⟨i.val - 1, by
      have := i.lt_large
      omega⟩ = 1 := by
  have hseparated := D.outer.transition.separated
  exact a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst (i.val - 1) (by omega) (by omega)

/-- The first Lemma 2.18 alternative is impossible throughout the type-II
middle interval. -/
theorem lemma79Central_typeIIMiddle_firstAlternative_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero + 1 < i.val)
    (hright : i.val < D.outer.transition.firstTwo)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) : False := by
  apply lemma79Central_typeIIMiddle_not_leftAlphaSum
    a b D hfirst i hleft hright
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
  have hiLarge := i.lt_large
  have hsum : 2 * (ramificationIndex K : ℚ) <
      b.alphaValue ⟨i.val - 1, by omega⟩ +
        b.alphaValue ⟨i.val - 2, by omega⟩ := by
    exact_mod_cast hcap
  rw [add_comm]
  exact hsum

/-- Case 7: the second Lemma 2.18 alternative is impossible on the complete
type-II middle interval. -/
theorem lemma79Central_typeIIMiddle_secondAlternative_impossible
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero + 1 < i.val)
    (hright : i.val < D.outer.transition.firstTwo)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  by_cases hboundary : i.val + 1 = D.outer.transition.firstTwo
  · have hzero := lemma79Central_typeIIMiddle_boundary_currentDefect_eq_zero
      a b c D hfirst hnorm i hboundary htrigger
    have hbeta := lemma79Central_typeIIMiddle_boundary_currentAlpha_eq_one
      a b D hfirst i hboundary
    rw [b.prefixAlphaCap_of_internal (by
      have := i.one_lt
      omega) i.lt_large, hzero, add_zero, hbeta] at hcurrent
    have hstrict : 2 * (ramificationIndex K : ℚ) < 1 := by
      exact_mod_cast hcurrent
    have heOne : (1 : ℚ) ≤ ramificationIndex K := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (ramificationIndex_pos (K := K)))
    linarith
  · have hiNext : i.val + 1 < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      omega
    have hsum := b.lemma79Central_secondAlternative_targetAlphaSum
      c i hiNext hcurrent
    have hprevious := a.beli2019Lemma69_i_typeII_targetCore_eq_one
      b D hfirst (i.val - 1) (by omega) (by omega)
    have hnext := a.beli2019Lemma69_i_typeII_targetCore_eq_one
      b D hfirst i.val (by omega) (by omega)
    rw [hprevious, hnext] at hsum
    have hePos := ramificationIndex_pos (K := K)
    norm_num at hsum
    exact (Nat.ne_of_gt hePos) hsum

/-- Complete type-II witness family on the middle interval.  Both alternatives
of Lemma 2.18 are contradictory, so an active trigger cannot occur here. -/
theorem lemma79CentralWitness_typeIIMiddle
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hleft : D.outer.transition.lastZero + 1 < i.val)
    (hright : i.val < D.outer.transition.firstTwo)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
    hprevious | hcurrent
  · exact False.elim (lemma79Central_typeIIMiddle_firstAlternative_impossible
      a b c D hfirst hdefectBC i hleft hright hprevious)
  · exact False.elim (lemma79Central_typeIIMiddle_secondAlternative_impossible
      a b c D hfirst hnorm i hleft hright htrigger hcurrent)

end BONG.GoodBONG

end Bong
