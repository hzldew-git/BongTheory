/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapIndexPrefixes
import Bong.Bong.Beli2019Lemma72TypeIII
import Bong.Bong.Beli2019Lemma79RightTailGapOneComparison
import Bong.Bong.Beli2019Lemma79RightTailGapOnePrefix

/-!
# Beli (2019), Lemma 7.9(ii), case 8: type-III tail parity

This file formalizes lines 5794--5800.  The initial type-III prefix is
controlled by Lemma 7.2(iii), and every subsequent order in the strict
gap-one tail lies in the source reference class `R`.  Hence every target
prefix through the case-8 boundary has class `length * R`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The target order at the last changed coordinate is one above the
right source order of the adjacent type-III transition. -/
theorem beli2019Lemma79_typeIII_nonoverlap_tailBase_eq_rightSource_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hlast : D.outer.last < n + 1) :
    b.order (⟨D.outer.last, hlast⟩ : Fin (n + 1)).castSucc =
      a.orderSequence.entryOrZero
          (D.outer.transition.firstTwo - 1) + 1 := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  let right := D.outer.transition.firstTwo - 1
  have hrightEven := D.outer.right_even_distance
  have htargetLast := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl hrightEven
  have hrightBoundary : b.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [right] using D.outer.transition.rightBoundary
  have hentry : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero right + 1 :=
    htargetLast.trans hrightBoundary
  rw [← b.orderSequence_entryOrZero_eq_order first.castSucc]
  simpa only [first, right, Fin.val_castSucc] using hentry

/-- The local Lemma 7.8 coefficient is `R - S + 2` when written using
the source reference `R` and the strict-tail base `S`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_central_eq_reference_sub_base_add_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hlast : D.outer.last < n + 1) :
    ((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : Rat) =
      ((a.orderSequence.entryOrZero D.outer.transition.lastZero -
          b.order (⟨D.outer.last, hlast⟩ : Fin (n + 1)).castSucc +
          2 : Int) : Rat) := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftBoundary : b.orderSequence.entryOrZero left =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [left] using D.outer.transition.leftBoundary
  have hbase :=
    beli2019Lemma79_typeIII_nonoverlap_tailBase_eq_rightSource_add_one
      a b D hlast
  have hleftOrder : b.order
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = b.orderSequence.entryOrZero left := by
    symm
    simpa only [left] using b.orderSequence_entryOrZero_eq_order
      (⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ : Fin (n + 2))
  have hrightOrder : a.order
      ⟨D.outer.transition.lastZero + 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = a.orderSequence.entryOrZero right := by
    symm
    have hentry := a.orderSequence_entryOrZero_eq_order
      (⟨D.outer.transition.lastZero + 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ : Fin (n + 2))
    rw [hrightEq]
    simpa only [left] using hentry
  rw [hleftOrder, hrightOrder]
  have hbase' : b.order first.castSucc =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [first, right] using hbase
  exact_mod_cast (show
    b.orderSequence.entryOrZero left -
        a.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero left - b.order first.castSucc + 2 by
    omega)

/-- Every target prefix from the end of the type-III profile through one
coordinate beyond the strict alpha tail has the paper class `length * R`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_targetPrefix_modEq_reference
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hlast : D.outer.last < n + 1)
    {tailLast : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ tailLast)
    (hfirstTail : (⟨D.outer.last, hlast⟩ : Fin (n + 1)) ≤ tailLast)
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast)
    (length : Nat) (hstart : D.outer.last + 1 ≤ length)
    (hend : length ≤ tailLast.val + 2) :
    Int.ModEq 2 (b.orderSequence.prefixSum length)
      ((length : Int) *
        a.orderSequence.entryOrZero D.outer.transition.lastZero) := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let reference := a.orderSequence.entryOrZero right
  have hbase : b.order first.castSucc = reference + 1 := by
    simpa only [first, reference, right] using
      beli2019Lemma79_typeIII_nonoverlap_tailBase_eq_rightSource_add_one
        a b D hlast
  have hformulaData := beli2019Lemma79_typeIII_caseEight_gapOne_formula
    a b D tailLast (by
      change D.outer.last ≤ tailLast.val
      exact hfirstTail)
      (by simpa only [first] using H) hstrictTail
  have hformula : ∀ j : Fin (n + 1), first ≤ j → j ≤ tailLast →
      b.alphaValue j =
        ((b.order j.succ - b.order first.castSucc : Int) : Rat) := by
    intro j hjFirst hjLast
    simpa only [first] using hformulaData.2 j
      (by simpa only [first] using hjFirst) hjLast
  let P := a.beli2019Lemma72_iii_of_defect
    b D hfirst hdefect hnotOverlap
  have hinitialRaw := P.target (D.outer.last + 1) le_rfl
  have hrightBoundary : b.orderSequence.entryOrZero right =
      reference + 1 := by
    simpa only [reference, right] using D.outer.transition.rightBoundary
  rw [hrightBoundary] at hinitialRaw
  have hstartEven :=
    beli2019Lemma79_typeIII_last_succ_even a b D hfirst
  have hcountZero : Int.ModEq 2
      (((D.outer.last + 1 : Nat) : Int)) 0 := by
    rcases hstartEven with ⟨d, hd⟩
    have hstartEvenInt : Even
        (((D.outer.last + 1 : Nat) : Int)) := by
      refine ⟨(d : Int), ?_⟩
      exact_mod_cast hd
    apply int_modEq_two_of_even_sub
    simpa only [sub_zero] using hstartEvenInt
  have hinitialFormula : Int.ModEq 2
      (((D.outer.last + 1 : Nat) : Int) * (reference + 1))
      (((D.outer.last + 1 : Nat) : Int) * reference) := by
    have hsum :=
      (Int.ModEq.rfl : Int.ModEq 2
        (((D.outer.last + 1 : Nat) : Int) * reference)
        (((D.outer.last + 1 : Nat) : Int) * reference)).add hcountZero
    simpa only [mul_add, mul_one, add_zero] using hsum
  have hinitial : Int.ModEq 2
      (b.orderSequence.prefixSum (first.val + 1))
      (((first.val + 1 : Nat) : Int) * reference) := by
    simpa only [first] using hinitialRaw.trans hinitialFormula
  have htailEntry (k : Nat) (hkStart : first.val + 1 ≤ k)
      (hkEnd : k < length) :
      Int.ModEq 2 (b.orderSequence.entryOrZero k) reference := by
    apply H.tail_order_modEq_reference reference hbase hformula k hkStart
    omega
  have hraw := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    (((first.val + 1 : Nat) : Int) * reference) reference
      (by simpa only [first] using hstart) hinitial htailEntry
  have hcastSub :
      ((length - (first.val + 1) : Nat) : Int) =
        (length : Int) - (first.val + 1 : Nat) := by
    have hs : first.val + 1 ≤ length := by
      simpa only [first] using hstart
    omega
  have hformulaReference :
      ((first.val + 1 : Nat) : Int) * reference +
          ((length - (first.val + 1) : Nat) : Int) * reference =
        (length : Int) * reference := by
    rw [hcastSub]
    push_cast
    ring
  rw [hformulaReference] at hraw
  let C := a.lemma611TypeIII_of_defect
    (alphaV := inferInstance) (alphaW := inferInstance)
    b D hfirst hdefect hnotOverlap
  have href : Int.ModEq 2 reference
      (a.orderSequence.entryOrZero left) := by
    apply int_modEq_two_of_even_sub
    simpa only [reference, right, left] using C.central_gap_even
  have hrefMul : Int.ModEq 2 ((length : Int) * reference)
      ((length : Int) * a.orderSequence.entryOrZero left) := by
    simpa only [mul_comm] using href.mul_right (length : Int)
  exact hraw.trans (by simpa only [left] using hrefMul)

/-- The comparison prefix inherits the same `length * R` class from the
case-8 prefix congruence. -/
theorem beli2019Lemma79_typeIII_nonoverlap_comparisonPrefix_modEq_reference
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val)) :
    Int.ModEq 2 (c.orderSequence.prefixSum i.val)
      ((i.val : Int) *
        a.orderSequence.entryOrZero D.outer.transition.lastZero) := by
  have hfirstTail :
      (⟨D.outer.last, hlast⟩ : Fin (n + 1)) ≤
        caseEightLastAlphaIndex i := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have htarget :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefix_modEq_reference
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail hstrictLast
        i.val hafter (by
          simp only [caseEightLastAlphaIndex_val]
          have hiPos := i.pos
          omega)
  exact hprefix.symm.trans htarget

/-- At an odd case-8 index the final comparison order is at least `R + 2`,
as in lines 5840--5844. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_comparisonOrder_ge_reference_add_two
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hiOdd : Odd i.val) :
    a.orderSequence.entryOrZero D.outer.transition.lastZero + 2 ≤
      c.order (evenTargetPreviousIndex i) := by
  let reference :=
    a.orderSequence.entryOrZero D.outer.transition.lastZero
  have hcomparison :=
    beli2019Lemma79_typeIII_nonoverlap_comparisonPrefix_modEq_reference
      a b c D hfirst hdefect hnotOverlap hlast i hafter H hstrictLast
        hprefix
  have hparityShift : Int.ModEq 2
      ((i.val : Int) * reference)
      ((i.val : Int) * (reference + 1) + 1) := by
    rcases hiOdd with ⟨d, hd⟩
    have hzero : Int.ModEq 2 ((i.val : Int) + 1) 0 := by
      apply int_modEq_two_of_even_sub
      refine ⟨((d : Int) + 1), ?_⟩
      have hdInt : (i.val : Int) = 2 * (d : Int) + 1 := by
        exact_mod_cast hd
      omega
    have hsum :=
      (Int.ModEq.rfl : Int.ModEq 2
        ((i.val : Int) * reference) ((i.val : Int) * reference)).add hzero
    simpa only [mul_add, mul_one, add_assoc, add_zero] using hsum.symm
  have hcomparisonReference : Int.ModEq 2
      (c.orderSequence.prefixSum i.val) ((i.val : Int) * reference) := by
    simpa only [reference] using hcomparison
  have hcomparisonShift : Int.ModEq 2
      (c.orderSequence.prefixSum i.val)
      ((i.val : Int) * (reference + 1) + 1) :=
    hcomparisonReference.trans hparityShift
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : reference + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    change a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 ≤
      c.orderSequence.entryOrZero 0
    rw [hsourceLeft,
      show a.orderSequence.entryOrZero 0 = a.order (0 : Fin (n + 2)) by
        simpa using a.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2)),
      show c.orderSequence.entryOrZero 0 = c.order (0 : Fin (n + 2)) by
        simpa using c.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2))]
    exact hnormOrder
  have hlastAbove :=
    c.last_entry_ge_reference_add_one_of_odd_prefix_modEq
      i.val (reference + 1) i.pos i.lt_large.le hiOdd
        hcomparisonShift hfirstLower
  have hlastOrder : c.orderSequence.entryOrZero (i.val - 1) =
      c.order (evenTargetPreviousIndex i) := by
    simpa only [evenTargetPreviousIndex] using
      c.orderSequence_entryOrZero_eq_order (evenTargetPreviousIndex i)
  rw [hlastOrder] at hlastAbove
  simp only [reference] at hlastAbove
  omega

end BONG.GoodBONG

end Bong
