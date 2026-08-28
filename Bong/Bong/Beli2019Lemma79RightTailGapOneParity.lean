/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneComparison

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the gap-one parity engine

This file packages the parity split common to types I and II.  Once the
target prefix of length `i + 1` and the comparison prefix of length `i`
are both in the paper's class `j * T + 1`, Lemma 6.6 supplies either the
odd signed primary product or an earlier odd adjacent comparison pair.
Those are precisely the first two constructors of
`CaseEightGapOneBetaEvidence`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- An odd integer is congruent to one modulo two. -/
theorem modEq_two_one_of_odd {x : Int} (hx : Odd x) :
    Int.ModEq 2 x 1 := by
  rcases hx with ⟨d, hd⟩
  rw [Int.modEq_iff_dvd]
  exact ⟨-d, by omega⟩

/-- Congruence modulo two transports oddness. -/
theorem caseEight_odd_of_modEq_two_of_odd {x y : Int}
    (hmod : Int.ModEq 2 x y) (hy : Odd y) : Odd x := by
  rw [Int.modEq_iff_dvd] at hmod
  rcases hmod with ⟨z, hz⟩
  rcases hy with ⟨d, hd⟩
  exact ⟨d - z, by omega⟩

/-- The order of the signed unequal-prefix product is the sum of the two
prefix orders; hence an odd sum gives odd product order. -/
theorem signed_shifted_prefixProduct_order_odd_of_sum_odd
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd (b.orderSequence.prefixSum (i.val + 1) +
      c.orderSequence.prefixSum (i.val - 1))) :
    Odd (ordUnit K ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
      c.prefixProduct (i.val - 1))) := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
    b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val + 1) (Nat.succ_le_of_lt i.lt_large),
    c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (i.val - 1) ((Nat.sub_le i.val 1).trans i.lt_large.le)]
  exact hodd

/-- An odd comparison prefix with a suitably congruent final order gives
the comparison-alpha constructor of the gap-one evidence. -/
theorem caseEight_gapOne_comparisonAlpha_evidence_of_prefix_odd
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (length : Nat) (reference : Int)
    (hlengthPos : 0 < length) (hlengthBound : length ≤ n + 2)
    (hlengthEven : Even length)
    (hprefix : Odd (c.orderSequence.prefixSum length))
    (hlengthLast : length - 1 ≤ i.val - 1)
    (hfirstLower : reference ≤ c.orderSequence.entryOrZero 0)
    (hfinalMod : Int.ModEq 2
      (c.orderSequence.entryOrZero (i.val - 1)) reference) :
    CaseEightGapOneBetaEvidence b c i (reference + 1) := by
  have hfinalBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  rcases c.exists_odd_entryPair_above_reference_of_even_prefix_odd
      length (i.val - 1) reference hlengthPos hlengthBound hlengthEven
      hprefix hfinalBound hlengthLast hfirstLower hfinalMod with
    ⟨k, hkFinal, hkOdd, hkAbove⟩
  have hiTwo : 2 ≤ i.val := by
    rcases hlengthEven with ⟨d, hd⟩
    omega
  have hkBound : k < n + 1 := by omega
  let j : Fin (n + 1) := ⟨k, hkBound⟩
  have hsumOdd : Odd (c.order j.castSucc + c.order j.succ) := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc,
      ← c.orderSequence_entryOrZero_eq_order j.succ]
    simpa only [j, Fin.val_castSucc, Fin.val_succ] using hkOdd
  have hreference : reference < c.order j.castSucc := by
    rw [← c.orderSequence_entryOrZero_eq_order j.castSucc]
    simpa only [j, Fin.val_castSucc] using hkAbove
  have hjlt : j.val + 1 < i.val := by
    change k + 1 < i.val
    have hiPos := i.pos
    omega
  have hgamma :=
    caseSix_previousAlpha_le_current_sub_reference_sub_one_of_odd_pair
      c i reference j hjlt hsumOdd hreference
  apply CaseEightGapOneBetaEvidence.comparisonAlpha hiTwo
  push_cast at hgamma ⊢
  linarith

/-- The complete parity engine for the type-I/type-II gap-one branch. -/
theorem caseEight_gapOne_evidence_of_prefix_parity
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (reference : Int)
    (htarget : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * reference + 1))
    (hcomparison : Int.ModEq 2
      (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * reference + 1))
    (hfirstLower : reference ≤ c.orderSequence.entryOrZero 0) :
    CaseEightGapOneBetaEvidence b c i (reference + 1) := by
  have hcSucc : c.orderSequence.prefixSum i.val =
      c.orderSequence.prefixSum (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1) := by
    simpa only [Nat.sub_add_cancel i.pos] using
      c.orderSequence.prefixSum_succ (i.val - 1)
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · have hreferenceOdd : Odd ((i.val : Int) * reference + 1) := by
      rcases hiEven with ⟨d, hd⟩
      refine ⟨(d : Int) * reference, ?_⟩
      have hdInt : (i.val : Int) = (d : Int) + (d : Int) := by
        exact_mod_cast hd
      rw [hdInt]
      ring
    have hcomparisonOdd : Odd
        (c.orderSequence.prefixSum i.val) :=
      caseEight_odd_of_modEq_two_of_odd hcomparison hreferenceOdd
    have hlastAbove :=
      c.last_entry_ge_reference_add_one_of_even_prefix_odd
        i.val reference i.pos i.lt_large.le hiEven hcomparisonOdd
          hfirstLower
    rcases modEq_two_or_add_one
        (c.orderSequence.entryOrZero (i.val - 1)) reference with
      hfinalBase | hfinalNext
    · exact caseEight_gapOne_comparisonAlpha_evidence_of_prefix_odd
        b c i i.val reference i.pos i.lt_large.le hiEven hcomparisonOdd
        le_rfl hfirstLower hfinalBase
    · have hsub := hcomparison.sub hfinalNext
      rw [hcSucc] at hsub
      simp only [add_sub_cancel_right] at hsub
      have hright :
          (i.val : Int) * reference + 1 - (reference + 1) =
            ((i.val - 1 : Nat) : Int) * reference := by
        have hcastSub : ((i.val - 1 : Nat) : Int) =
            (i.val : Int) - 1 := by
          have hiPos := i.pos
          omega
        rw [hcastSub]
        ring
      rw [hright] at hsub
      have hsumMod := htarget.add hsub
      have hsumReferenceOdd : Odd
          ((((i.val + 1 : Nat) : Int) * reference + 1) +
            (((i.val - 1 : Nat) : Int) * reference)) := by
        refine ⟨(i.val : Int) * reference, ?_⟩
        have hcastSub : ((i.val - 1 : Nat) : Int) =
            (i.val : Int) - 1 := by
          have hiPos := i.pos
          omega
        have hcastAdd : ((i.val + 1 : Nat) : Int) =
            (i.val : Int) + 1 := by omega
        rw [hcastSub, hcastAdd]
        ring
      have hsumOdd := caseEight_odd_of_modEq_two_of_odd
        hsumMod hsumReferenceOdd
      have hproductOdd :=
        signed_shifted_prefixProduct_order_odd_of_sum_odd b c i hsumOdd
      have hcomparisonOrder : reference + 1 ≤
          c.order (evenTargetPreviousIndex i) := by
        rw [← c.orderSequence_entryOrZero_eq_order]
        simpa only [evenTargetPreviousIndex] using hlastAbove
      exact CaseEightGapOneBetaEvidence.primaryProduct
        hproductOdd hcomparisonOrder
  · have hlastAbove :=
      c.last_entry_ge_reference_add_one_of_odd_prefix_modEq
        i.val reference i.pos i.lt_large.le hiOdd hcomparison hfirstLower
    rcases Int.even_or_odd
        (c.orderSequence.prefixSum (i.val - 1)) with
      hpreviousEven | hpreviousOdd
    · have htargetReferenceOdd : Odd
          (((i.val + 1 : Nat) : Int) * reference + 1) := by
        rcases hiOdd with ⟨d, hd⟩
        refine ⟨((d : Int) + 1) * reference, ?_⟩
        have hdInt : (i.val : Int) = 2 * (d : Int) + 1 := by
          exact_mod_cast hd
        push_cast
        rw [hdInt]
        ring
      have htargetOdd : Odd
          (b.orderSequence.prefixSum (i.val + 1)) :=
        caseEight_odd_of_modEq_two_of_odd htarget htargetReferenceOdd
      have hsumOdd : Odd
          (b.orderSequence.prefixSum (i.val + 1) +
            c.orderSequence.prefixSum (i.val - 1)) :=
        htargetOdd.add_even hpreviousEven
      have hproductOdd :=
        signed_shifted_prefixProduct_order_odd_of_sum_odd b c i hsumOdd
      have hcomparisonOrder : reference + 1 ≤
          c.order (evenTargetPreviousIndex i) := by
        rw [← c.orderSequence_entryOrZero_eq_order]
        simpa only [evenTargetPreviousIndex] using hlastAbove
      exact CaseEightGapOneBetaEvidence.primaryProduct
        hproductOdd hcomparisonOrder
    · have hpreviousOne := modEq_two_one_of_odd hpreviousOdd
      have hfinalToMultiple := hcomparison.sub hpreviousOne
      rw [hcSucc] at hfinalToMultiple
      simp only [add_sub_cancel_left, add_sub_cancel_right] at hfinalToMultiple
      rcases hiOdd with ⟨d, hd⟩
      have hiMod : Int.ModEq 2 (i.val : Int) 1 := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-(d : Int), ?_⟩
        have hdInt : (i.val : Int) = 2 * (d : Int) + 1 := by
          exact_mod_cast hd
        omega
      have hmultipleBase : Int.ModEq 2
          ((i.val : Int) * reference) reference := by
        simpa only [one_mul] using hiMod.mul_right reference
      have hfinalBase : Int.ModEq 2
          (c.orderSequence.entryOrZero (i.val - 1)) reference :=
        hfinalToMultiple.trans hmultipleBase
      have hlengthEven : Even (i.val - 1) := by
        refine ⟨d, ?_⟩
        omega
      have hlengthPos : 0 < i.val - 1 := by
        by_contra hnot
        have hzero : i.val - 1 = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hzero, BeliOrderSequence.prefixSum_zero] at hpreviousOdd
        rcases hpreviousOdd with ⟨e, he⟩
        omega
      exact caseEight_gapOne_comparisonAlpha_evidence_of_prefix_odd
        b c i (i.val - 1) reference hlengthPos
        ((Nat.sub_le i.val 1).trans i.lt_large.le) hlengthEven
        hpreviousOdd (Nat.sub_le _ _) hfirstLower hfinalBase

end BONG.GoodBONG

end Bong
