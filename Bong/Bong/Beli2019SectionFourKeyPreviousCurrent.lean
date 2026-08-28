/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPreviousCandidates

/-!
# Beli (2019), Lemma 4.2: the preceding current candidate

In the branch `T_(i-2) ≤ S_i`, suppose the preceding middle invariant is
its current secondary candidate.  The strict failure of the source primary
candidate then identifies the defect in that candidate with the next
source-to-middle comparison defect.  This is the two-triangle calculation
on lines 2195--2206, expressed after the replacement of Lemma 2.7(ii).
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U} {n : Nat}

/-- If `B_(i-2)` is its current secondary candidate, its defect is
`d[a_(1,i)b_(1,i)]`.  The replacement form of Lemma 2.7(ii) makes the
two strict triangles in the paper a single capped-defect triangle. -/
theorem previousMiddleCurrentDefect_eq_sourceMiddleNextDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hj : 2 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      let previous := previousRepresentationIndex j hiTwo
      let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
        dsimp only [previous, previousRepresentationIndex]
        have := j.lt_large
        omega
      b.representationAlpha c previous =
        b.representationSecondaryCurrentDefect c previous hk) :
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
  have hjLt : j.val < n + 1 := j.lt_large
  let previous := previousRepresentationIndex j hiTwo
  let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
    dsimp only [previous, previousRepresentationIndex]
    have := j.lt_large
    omega
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let combinedShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hiTwo hcross hprimary
  have hstrict : (outerShift : WithTop ℚ) +
      b.representationAlpha c previous < a.representationAlpha c j := by
    exact hlower.trans_lt hprimary
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationSecondaryCurrentDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    congr 2
    omega
  have hshiftSum : outerShift + previousShift = combinedShift := by
    dsimp only [outerShift, previousShift, combinedShift]
    push_cast
    ring
  have hexpanded : (combinedShift : WithTop ℚ) + previousDefect <
      (targetShift : WithTop ℚ) + targetDefect := by
    calc
      (combinedShift : WithTop ℚ) + previousDefect =
          (outerShift : WithTop ℚ) + b.representationAlpha c previous := by
        rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, hshiftSum]
      _ < a.representationAlpha c j := hstrict
      _ ≤ (targetShift : WithTop ℚ) + targetDefect := by
        simpa only [targetShift, targetDefect, representationPrimaryDefect]
          using a.representationAlpha_le_primary c j
  have htargetLe : targetShift ≤ combinedShift := by
    have htwoStep :
        c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ ≤
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
      have h := c.orderSequence.twoStep (j.val - 3) (by omega)
      change c.order ⟨j.val - 3, by omega⟩ ≤
        c.order ⟨j.val - 3 + 2, by omega⟩ at h
      simpa only [show j.val - 3 + 2 = j.val - 1 by omega] using h
    dsimp only [targetShift, combinedShift]
    push_cast
    have hcrossQ :
        (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) ≤
          (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    have htwoStepQ :
        (c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ : ℚ) ≤
          (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast htwoStep
    linarith
  have hexpanded' : (combinedShift : WithTop ℚ) + previousDefect <
      (combinedShift : WithTop ℚ) + targetDefect :=
    hexpanded.trans_le (add_le_add (by exact_mod_cast htargetLe) le_rfl)
  have hdefect : previousDefect < targetDefect :=
    (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hexpanded'
  have hdefect' :
      c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) <
        c.truncatedPrefixDefect a (-1) (j.val - 1) (j.val + 1) := by
    simpa only [previousDefect, targetDefect,
      c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1),
      c.truncatedPrefixDefect_comm a (-1) (j.val - 1) (j.val + 1)]
      using hdefect
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    b a (j.val - 1) (j.val + 1) (j.val + 1) hdefect'
  calc
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
        c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) :=
      (c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1)).symm
    _ = b.truncatedPrefixDefect a 1 (j.val + 1) (j.val + 1) := htriangle
    _ = a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) :=
      b.truncatedPrefixDefect_comm a 1 (j.val + 1) (j.val + 1)

/-- Condition 2.1(ii) for the source-to-middle pair turns the preceding
triangle identity into the lower bound by `A_i` used on line 2206. -/
theorem nextSourceAlpha_le_previousMiddleCurrentDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hj : 2 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      let previous := previousRepresentationIndex j hi.1
      let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
        dsimp only [previous, previousRepresentationIndex]
        have := j.lt_large
        omega
      b.representationAlpha c previous =
        b.representationSecondaryCurrentDefect c previous hk) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) := by
  have htriangle := a.previousMiddleCurrentDefect_eq_sourceMiddleNextDefect
    b c hbcOrder hbcDefect j hi.1 hj hcross hprimary hprevious
  have hdefect := habDefect (nextRepresentationIndex j hi.2)
  rw [a.coe_representationAlphaValue b
    (nextRepresentationIndex j hi.2)] at hdefect
  rw [htriangle]
  simpa only [nextRepresentationIndex] using hdefect

/-- Shifted form of the preceding lower bound.  This is the common quantity
`R_i + S_i - T_(i-2) - T_(i-1) + A_i` reached in both alternatives for
`B_(i-2)` in the paper. -/
theorem shiftedNextSourceAlpha_le_sourcePrimary_of_previousCurrent
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hj : 2 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      let previous := previousRepresentationIndex j hi.1
      let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
        dsimp only [previous, previousRepresentationIndex]
        have := j.lt_large
        omega
      b.representationAlpha c previous =
        b.representationSecondaryCurrentDefect c previous hk) :
    (((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        a.representationPrimaryDefect b j := by
  let previous := previousRepresentationIndex j hi.1
  let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
    dsimp only [previous, previousRepresentationIndex]
    have := j.lt_large
    omega
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let desiredShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hi.1 hcross hprimary
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationSecondaryCurrentDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    congr 2
    omega
  have hnext := a.nextSourceAlpha_le_previousMiddleCurrentDefect
    b c habDefect hbcOrder hbcDefect j hi hj hcross hprimary hprevious
  have htwoStep :
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ ≤
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    have h := c.orderSequence.twoStep (j.val - 3) (by omega)
    change c.order ⟨j.val - 3, by omega⟩ ≤
      c.order ⟨j.val - 3 + 2, by omega⟩ at h
    simpa only [show j.val - 3 + 2 = j.val - 1 by omega] using h
  have hshift : desiredShift ≤ outerShift + previousShift := by
    dsimp only [desiredShift, outerShift, previousShift]
    push_cast
    have htwoStepQ :
        (c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ : ℚ) ≤
          (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast htwoStep
    linarith
  change (desiredShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤ _
  calc
    (desiredShift : WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      ((outerShift + previousShift : ℚ) : WithTop ℚ) +
        previousDefect :=
      add_le_add (by exact_mod_cast hshift) hnext
    _ = (outerShift : WithTop ℚ) +
        b.representationAlpha c previous := by
      rw [hpreviousExpanded]
      simp only [WithTop.coe_add, add_assoc]
    _ ≤ a.representationPrimaryDefect b j := by
      simpa only [outerShift, previous] using hlower

/-- The sharper form used in the final candidate contradiction: the common
shifted `A_i` is already bounded by the shifted preceding invariant itself. -/
theorem shiftedNextSourceAlpha_le_shift_previousMiddle_of_previousCurrent
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hj : 2 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      let previous := previousRepresentationIndex j hi.1
      let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
        dsimp only [previous, previousRepresentationIndex]
        have := j.lt_large
        omega
      b.representationAlpha c previous =
        b.representationSecondaryCurrentDefect c previous hk) :
    (((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        b.representationAlpha c (previousRepresentationIndex j hi.1) := by
  let previous := previousRepresentationIndex j hi.1
  let hk : 1 < previous.val ∧ previous.val + 1 < n + 1 := by
    dsimp only [previous, previousRepresentationIndex]
    have := j.lt_large
    omega
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let desiredShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationSecondaryCurrentDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    congr 2
    omega
  have hnext := a.nextSourceAlpha_le_previousMiddleCurrentDefect
    b c habDefect hbcOrder hbcDefect j hi hj hcross hprimary hprevious
  have htwoStep :
      c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ ≤
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
    have h := c.orderSequence.twoStep (j.val - 3) (by omega)
    change c.order ⟨j.val - 3, by omega⟩ ≤
      c.order ⟨j.val - 3 + 2, by omega⟩ at h
    simpa only [show j.val - 3 + 2 = j.val - 1 by omega] using h
  have hshift : desiredShift ≤ outerShift + previousShift := by
    dsimp only [desiredShift, outerShift, previousShift]
    push_cast
    have htwoStepQ :
        (c.order ⟨j.val - 3, by have := j.lt_large; omega⟩ : ℚ) ≤
          (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) := by
      exact_mod_cast htwoStep
    linarith
  change (desiredShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
    (outerShift : WithTop ℚ) + b.representationAlpha c previous
  calc
    (desiredShift : WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      ((outerShift + previousShift : ℚ) : WithTop ℚ) +
        previousDefect :=
      add_le_add (by exact_mod_cast hshift) hnext
    _ = (outerShift : WithTop ℚ) +
        b.representationAlpha c previous := by
      rw [hpreviousExpanded]
      simp only [WithTop.coe_add, add_assoc]

end BONG.GoodBONG

end Bong
