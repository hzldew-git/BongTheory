/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddNonintegral
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddEquality

/-!
# Beli (2019), Lemma 7.9(ii), case 8: exclusion of odd type-III equality

Domination equality and Lemma 7.3(ii) propagate the low-witness prefix
class `R + 1` through the full comparison prefix.  The type-III target
prefix has class `R`; this contradicts the global prefix congruence.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The equality alternative in odd-index capped domination is impossible
in the nonoverlapping type-III branch. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_domination_equality_false
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat))
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val - 1)
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hjPair : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat))
    (hcoefficient :
      ((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) =
      ((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat)) :
    False := by
  let first : Fin (n + 1) := Fin.mk D.outer.last hlast
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  let reference : Int :=
    a.orderSequence.entryOrZero D.outer.transition.lastZero
  let centralQ : Rat :=
    ((b.order
          (Fin.mk D.outer.transition.lastZero (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) -
        a.order
          (Fin.mk (D.outer.transition.lastZero + 1) (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) : Int) : Rat)
  have hiTwo : 2 <= i.val := by
    have hlastOdd := beli2019Lemma79_typeIII_last_odd a b D hfirst
    rcases hlastOdd with ⟨d, hd⟩
    omega
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hreferenceLower : reference + 1 <=
      c.order (0 : Fin (n + 2)) := by
    change a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 <=
      c.order (0 : Fin (n + 2))
    rw [hsourceLeft,
      show a.orderSequence.entryOrZero 0 =
          a.order (0 : Fin (n + 2)) by
        simpa using a.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2))]
    exact hnormOrder
  have hzeroCurrentEntry := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) (by omega) hjEven
  have hzeroCurrent : c.order (0 : Fin (n + 2)) <=
      c.order j.castSucc := by
    have hzeroEntry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    have hjEntry : c.orderSequence.entryOrZero j.val =
        c.order j.castSucc := by
      simpa using c.orderSequence_entryOrZero_eq_order j.castSucc
    rw [hzeroEntry, hjEntry] at hzeroCurrentEntry
    exact hzeroCurrentEntry
  have hzeroOrder : c.order (0 : Fin (n + 2)) = reference + 1 := by
    have hjOrder' : c.order j.castSucc = reference + 1 := by
      simpa only [reference] using hjOrder
    omega
  let zero : Fin (n + 2) := 0
  let current : Fin (n + 2) := j.castSucc
  have hjParity : Even (current.val - zero.val) := by
    simpa only [current, zero, Fin.val_castSucc, Fin.val_zero,
      Nat.sub_zero] using hjEven
  have hendpointOrder : c.order zero = c.order current := by
    simpa only [zero, current, hzeroOrder, reference] using hjOrder.symm
  have h66 := c.beli2019Lemma66_i zero current (by
      change zero.val <= current.val
      simp only [zero, current, Fin.val_zero, Fin.val_castSucc]
      omega) hjParity hendpointOrder
  have hjPrefix : Int.ModEq 2
      (c.orderSequence.prefixSum (j.val + 1)) (reference + 1) := by
    have hsum := h66.closedSum_modEq
    simpa only [zero, current, Fin.val_zero, Fin.val_castSucc,
      BeliOrderSequence.closedSegmentSum, BeliOrderSequence.prefixSum,
      Nat.Ico_zero_eq_range, hzeroOrder] using hsum
  have hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) := by
    rw [hcomparison]
    simpa only [centralQ] using hjPair
  have hjOrderCurrent : c.order j.castSucc = (reference + 2) - 1 := by
    simp only [reference]
    omega
  have heq : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
      ((show Rat from
          (((reference + 2) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop Rat) := by
    calc
      c.truncatedPrefixDefect c
          ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
          (centralQ : WithTop Rat) := by
        simpa only [centralQ] using hcomparison
      _ = ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) := by
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        simpa only [centralQ] using hcoefficient.symm
      _ = ((show Rat from
          (((reference + 2) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
          WithTop Rat) := by
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        rw [hjOrderCurrent]
        push_cast
        ring
  have hendpoint := lemma79_odd_rightEndpoint_eq_of_domination_equality
    c i hiTwo j hjBefore (reference + 2) hjOrderCurrent hjDefect heq
  have hcomparisonPrefix :=
    lemma79_odd_comparisonPrefix_modEq_of_rightEndpoint_eq
      c i hiOdd j hjEven hjBefore (reference + 1) hjPrefix hendpoint
  have hfirstTail : first <= last := by
    change D.outer.last <= i.val - 1
    have hiPos := i.pos
    omega
  have htargetRaw :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefix_modEq_reference
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail hstrictLast
        i.val hafter (by
          rw [caseEightLastAlphaIndex_val]
          have hiPos := i.pos
          omega)
  have hiOddInt : Odd (i.val : Int) := by
    rcases hiOdd with ⟨d, hd⟩
    refine ⟨(d : Int), ?_⟩
    exact_mod_cast hd
  have hiMod : Int.ModEq 2 (i.val : Int) 1 :=
    modEq_two_one_of_odd hiOddInt
  have htarget : Int.ModEq 2
      (b.orderSequence.prefixSum i.val) reference :=
    htargetRaw.trans (by
      simpa only [one_mul] using hiMod.mul_right reference)
  have hbad : Int.ModEq 2 reference (reference + 1) :=
    htarget.symm.trans (hprefix.trans hcomparisonPrefix)
  rw [Int.modEq_iff_dvd] at hbad
  rcases hbad with ⟨z, hz⟩
  omega

end BONG.GoodBONG

end Bong
