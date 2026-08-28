/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma78Local
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypes

/-!
# Beli (2019), Lemma 7.9(ii), case 8: nonoverlapping type-III base

The final unequal coordinate of a type-III profile is odd.  In the strict
gap-one tail, parity and two-step monotonicity then force the first beta to
dominate the central defect `R - S + 2`.  This is the numerical bridge from
the local form of Lemma 7.8 to the case-8 tail.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The last unequal coordinate in a type-III profile is odd. -/
theorem beli2019Lemma79_typeIII_last_odd
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0) :
    Odd D.outer.last := by
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hrightEven := D.outer.right_even_distance
  rcases hleftEven with ⟨d, hd⟩
  rcases hrightEven with ⟨e, he⟩
  have hrightEq : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  refine ⟨d + e, ?_⟩
  have hrightLast := D.outer.right_le_last
  rw [hrightEq] at he hrightLast
  omega

/-- Consequently, the first prefix beyond the last unequal coordinate has
even length. -/
theorem beli2019Lemma79_typeIII_last_succ_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0) :
    Even (D.outer.last + 1) := by
  rcases beli2019Lemma79_typeIII_last_odd a b D hfirst with ⟨d, hd⟩
  exact ⟨d + 1, by omega⟩

/-- In the nonoverlapping type-III branch, the first strict-tail beta is at
least the central mixed defect of Lemma 7.8. -/
theorem beli2019Lemma79_typeIII_nonoverlap_central_le_firstBeta
    [alpha : Beli2006AlphaLaws.{u, v} K]
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
    (hstrictTail : b.alphaValue tailLast < a.alphaValue tailLast) :
    ((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : Rat) ≤
      b.alphaValue ⟨D.outer.last, hlast⟩ := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hlastEvenDistance := D.outer.right_even_distance
  have hlastOdd := beli2019Lemma79_typeIII_last_odd a b D hfirst
  have hlastSuccEven :=
    beli2019Lemma79_typeIII_last_succ_even a b D hfirst
  have hlastSuccBound : D.outer.last + 1 < n + 2 := by omega
  have hleftBound : left < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    simp only [left]
    rw [D.adjacent] at hbound
    omega
  have hrightBound : right < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    omega
  let C := a.lemma611TypeIII_of_defect
    (alphaV := alpha) (alphaW := alpha)
    b D hfirst hdefect hnotOverlap
  have hcentralEven : Even
      (a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left) := by
    simpa only [C, right, left] using C.central_gap_even
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst left le_rfl hleftEven
  have htargetZero := D.outer.target_first_eq_source_add_one
    hfirst D.no_gap_two
  have htargetZeroEq : b.orderSequence.entryOrZero 0 =
      a.orderSequence.entryOrZero left + 1 := by
    omega
  have htargetLast := D.outer.target_rightEven_eq_boundary
    D.outer.last D.outer.right_le_last le_rfl hlastEvenDistance
  have hrightBoundary : b.orderSequence.entryOrZero right =
      a.orderSequence.entryOrZero right + 1 := by
    simpa only [right] using D.outer.transition.rightBoundary
  have htargetLastEq : b.orderSequence.entryOrZero D.outer.last =
      a.orderSequence.entryOrZero right + 1 := by
    exact htargetLast.trans hrightBoundary
  have htargetMonotone :=
    b.orderSequence.entryOrZero_le_of_evenGap 0 (D.outer.last + 1)
      (Nat.zero_le _) hlastSuccBound hlastSuccEven
  have hformulaData := beli2019Lemma79_typeIII_caseEight_gapOne_formula
    a b D tailLast (by
      change D.outer.last ≤ tailLast.val
      exact hfirstTail)
      (by simpa only [first] using H) hstrictTail
  have hformula := hformulaData.2 first le_rfl hfirstTail
  have hformulaEntry : b.alphaValue first =
      ((b.orderSequence.entryOrZero (D.outer.last + 1) -
        b.orderSequence.entryOrZero D.outer.last : Int) : Rat) := by
    rw [← b.orderSequence_entryOrZero_eq_order first.succ,
      ← b.orderSequence_entryOrZero_eq_order first.castSucc] at hformula
    simpa only [first, Fin.val_succ, Fin.val_castSucc] using hformula
  rcases H.alpha_odd first le_rfl hfirstTail with ⟨z, hzOdd, hz⟩
  have hzInt : z =
      b.orderSequence.entryOrZero (D.outer.last + 1) -
        b.orderSequence.entryOrZero D.outer.last := by
    exact_mod_cast hz.symm.trans hformulaEntry
  have htargetStrict : b.orderSequence.entryOrZero 0 <
      b.orderSequence.entryOrZero (D.outer.last + 1) := by
    apply lt_of_le_of_ne htargetMonotone
    intro heq
    rcases hcentralEven with ⟨d, hd⟩
    rcases hzOdd with ⟨e, he⟩
    omega
  have hnextLower : a.orderSequence.entryOrZero left + 2 ≤
      b.orderSequence.entryOrZero (D.outer.last + 1) := by
    omega
  have hcentralEntry :
      b.orderSequence.entryOrZero left -
          a.orderSequence.entryOrZero right ≤
        b.orderSequence.entryOrZero (D.outer.last + 1) -
          b.orderSequence.entryOrZero D.outer.last := by
    have hleftBoundary : b.orderSequence.entryOrZero left =
        a.orderSequence.entryOrZero left + 1 := by
      simpa only [left] using D.outer.transition.leftBoundary
    omega
  have hcentralOrder :
      b.order ⟨left, hleftBound⟩ - a.order ⟨right, hrightBound⟩ ≤
        b.order first.succ - b.order first.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order ⟨left, hleftBound⟩,
      ← a.orderSequence_entryOrZero_eq_order ⟨right, hrightBound⟩,
      ← b.orderSequence_entryOrZero_eq_order first.succ,
      ← b.orderSequence_entryOrZero_eq_order first.castSucc]
    simpa only [first, Fin.val_succ, Fin.val_castSucc] using hcentralEntry
  rw [hformula]
  have hrightIndex :
      (⟨D.outer.transition.lastZero + 1, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ : Fin (n + 2)) = ⟨right, hrightBound⟩ := by
    apply Fin.ext
    simp only [right]
    rw [D.adjacent]
    omega
  have hleftIndex :
      (⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ : Fin (n + 2)) = ⟨left, hleftBound⟩ := by
    apply Fin.ext
    rfl
  rw [hleftIndex, hrightIndex]
  exact_mod_cast hcentralOrder

end BONG.GoodBONG

end Bong
