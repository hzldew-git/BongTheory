/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPreviousCurrent

/-!
# Beli (2019), Lemma 4.2: the preceding primary candidate

In the branch `T_(i-2) ≤ S_i`, suppose the preceding middle invariant is
its primary candidate.  The strict failure at the current source primary
candidate compares that candidate's defect with the capped adjacent defect
of `c_(i-2), c_(i-1)`.  The strict defect triangle then supplies the lower
bound by `B_(i-1)` used on lines 2207--2220.
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

/-- When `B_(i-2)` is its primary candidate, the defect occurring in that
candidate is bounded below by `B_(i-1)`.  This packages the two strict
triangles on lines 2207--2217 after applying condition 2.1(ii). -/
theorem middleTargetAlpha_le_previousMiddlePrimaryDefect
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hiTwo) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hiTwo)) :
    b.representationAlpha c j ≤
      b.truncatedPrefixDefect c (-1) j.val (j.val - 2) := by
  let previous := previousRepresentationIndex j hiTwo
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  let adjacentDefect :=
    c.truncatedPrefixDefect c (-1) (j.val - 2) j.val
  have hjLe : j.val ≤ n := by
    have := j.lt_large
    omega
  let targetPair : Fin n := ⟨j.val - 2, by omega⟩
  let adjacentLower : ℚ :=
    ((c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) +
        c.alphaValue targetPair
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hiTwo hcross hprimary
  have hstrict : (outerShift : WithTop ℚ) +
      b.representationAlpha c previous < a.representationAlpha c j := by
    exact hlower.trans_lt hprimary
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationPrimaryDefect
    simp only [previous, previousRepresentationIndex,
      Nat.sub_sub, Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    rfl
  have hshiftSum : outerShift + previousShift = baseShift := by
    dsimp only [outerShift, previousShift, baseShift]
    push_cast
    ring
  have hstrictExpanded : (baseShift : WithTop ℚ) + previousDefect <
      a.representationAlpha c j := by
    calc
      (baseShift : WithTop ℚ) + previousDefect =
          (outerShift : WithTop ℚ) +
            b.representationAlpha c previous := by
        rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, hshiftSum]
      _ < a.representationAlpha c j := hstrict
  have htargetCap : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + (c.alphaValue targetPair : WithTop ℚ) := by
    have hcandidate := a.representationAlpha_le_primary c j
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    have hcap' :
        a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) ≤
          (c.alphaValue targetPair : WithTop ℚ) := by
      rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      simpa only [targetPair, show j.val - 1 - 1 = j.val - 2 by omega]
        using hcap
    unfold representationPrimaryDefect at hcandidate
    exact hcandidate.trans (add_le_add le_rfl hcap')
  have hadjacentLower : (adjacentLower : WithTop ℚ) ≤ adjacentDefect := by
    have hraw := c.order_sub_add_alpha_le_cappedAdjacent targetPair
    have hcast : targetPair.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hsucc : targetPair.succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetPair, Fin.val_succ]
      omega
    rw [hcast, hsucc] at hraw
    simpa only [adjacentLower, adjacentDefect, targetPair,
      show j.val - 2 + 2 = j.val by omega] using hraw
  have htargetUpper : a.representationAlpha c j ≤
      (baseShift : WithTop ℚ) + adjacentDefect := by
    calc
      a.representationAlpha c j ≤
          (((a.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) + (c.alphaValue targetPair : WithTop ℚ) :=
        htargetCap
      _ = (baseShift : WithTop ℚ) + (adjacentLower : WithTop ℚ) := by
        exact_mod_cast (show
          ((a.order ⟨j.val, j.lt_large⟩ -
              c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) +
                c.alphaValue targetPair = baseShift + adjacentLower by
          dsimp only [baseShift, adjacentLower]
          push_cast
          ring)
      _ ≤ (baseShift : WithTop ℚ) + adjacentDefect :=
        add_le_add_right hadjacentLower _
  have hdefect : previousDefect < adjacentDefect := by
    have hshifted := hstrictExpanded.trans_le htargetUpper
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted
  have hdefect' :
      c.truncatedPrefixDefect b (-1) (j.val - 2) j.val <
        c.truncatedPrefixDefect c (-1) (j.val - 2) j.val := by
    rw [c.truncatedPrefixDefect_comm b (-1) (j.val - 2) j.val]
    simpa only [previousDefect, adjacentDefect] using hdefect
  have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
    b c (j.val - 2) j.val j.val hdefect'
  have hcondition := hbcDefect j
  rw [b.coe_representationAlphaValue c j] at hcondition
  calc
    b.representationAlpha c j ≤
        b.truncatedPrefixDefect c 1 j.val j.val := hcondition
    _ = c.truncatedPrefixDefect b (-1) (j.val - 2) j.val := htriangle.symm
    _ = b.truncatedPrefixDefect c (-1) j.val (j.val - 2) :=
      c.truncatedPrefixDefect_comm b (-1) (j.val - 2) j.val

/-- In the preceding-primary branch, the reduced three-candidate formula
for `B_(i-1)` can attain neither its half-gap nor its target-alpha term.
Consequently it attains its primary term, as on lines 2213--2223. -/
theorem middleTargetAlpha_eq_primary_of_previousPrimary
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hi.1) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hi.1)) :
    b.representationAlpha c j = b.representationPrimaryDefect c j := by
  let previous := previousRepresentationIndex j hi.1
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  let targetPair : Fin n := ⟨j.val - 2, by omega⟩
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hi.1 hcross hprimary
  have hstrict : (outerShift : WithTop ℚ) +
      b.representationAlpha c previous < a.representationAlpha c j :=
    hlower.trans_lt hprimary
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationPrimaryDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    rfl
  have hshiftSum : outerShift + previousShift = baseShift := by
    dsimp only [outerShift, previousShift, baseShift]
    push_cast
    ring
  have hbaseStrict : (baseShift : WithTop ℚ) + previousDefect <
      a.representationAlpha c j := by
    calc
      (baseShift : WithTop ℚ) + previousDefect =
          (outerShift : WithTop ℚ) +
            b.representationAlpha c previous := by
        rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, hshiftSum]
      _ < a.representationAlpha c j := hstrict
  have hmiddleLe : b.representationAlpha c j ≤ previousDefect :=
    a.middleTargetAlpha_le_previousMiddlePrimaryDefect
      b c hbcOrder hbcDefect j hi.1 hcross hprimary hprevious
  have hmiddleStrict : (baseShift : WithTop ℚ) +
      b.representationAlpha c j < a.representationAlpha c j :=
    (add_le_add_right hmiddleLe _).trans_lt hbaseStrict
  have hnormal := a.middleTargetAlpha_eq_reduced_of_leftDirect
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcDefect j hi hessential hdirect
  have hnormal' : b.representationAlpha c j =
      min (b.representationHalfGap c j)
        (min (b.representationPrimaryDefect c j)
          (b.representationSecondaryTargetAlpha c j hi j.lt_large)) := by
    rw [hnormal,
      b.representationAlphaReduced_eq_min_halfGap_primary_target_of_cross
        c j hi j.lt_large hcross]
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have hhalfUpper : a.representationAlpha c j ≤
      (baseShift : WithTop ℚ) + b.representationHalfGap c j := by
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap c j hi.1)
    calc
      a.representationAlpha c j ≤
          (((a.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            (c.halfGapValue targetPair : WithTop ℚ) := hraw
      _ ≤ (baseShift : WithTop ℚ) + b.representationHalfGap c j := by
        unfold representationHalfGap halfGapValue orderGap
        rw [htargetCast, htargetSucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        have hcrossQ :
            (c.order ⟨j.val - 2, by omega⟩ : ℚ) ≤
              (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
          exact_mod_cast hcross
        dsimp only [baseShift]
        push_cast
        linarith
  have hpair := a.keyLemmaLeftDirect_middlePair_lt b c hab j
    hi.1 hi.2 hessential hdirect
  have htargetCap : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (c.alphaValue targetPair : WithTop ℚ) := by
    have hcandidate := a.representationAlpha_le_primary c j
    have hcap := a.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    have hcap' :
        a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) ≤
          (c.alphaValue targetPair : WithTop ℚ) := by
      rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
      simpa only [targetPair, show j.val - 1 - 1 = j.val - 2 by omega]
        using hcap
    unfold representationPrimaryDefect at hcandidate
    exact hcandidate.trans (add_le_add le_rfl hcap')
  have htargetUpper : a.representationAlpha c j <
      (baseShift : WithTop ℚ) +
        b.representationSecondaryTargetAlpha c j hi j.lt_large := by
    apply htargetCap.trans_lt
    unfold representationSecondaryTargetAlpha
    norm_cast
    have hpairQ :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
            c.order ⟨j.val - 1, by omega⟩ <
          b.order ⟨j.val, j.lt_large⟩ +
            b.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hpair
    dsimp only [baseShift, targetPair]
    push_cast
    linarith
  rcases min_choice (b.representationHalfGap c j)
      (min (b.representationPrimaryDefect c j)
        (b.representationSecondaryTargetAlpha c j hi j.lt_large)) with
    hhalf | hrest
  · have heq : b.representationAlpha c j =
        b.representationHalfGap c j := hnormal'.trans hhalf
    exact False.elim ((not_lt_of_ge hhalfUpper) (heq ▸ hmiddleStrict))
  · rcases min_choice (b.representationPrimaryDefect c j)
        (b.representationSecondaryTargetAlpha c j hi j.lt_large) with
      hprimary' | htarget
    · exact hnormal'.trans (hrest.trans hprimary')
    · have heq : b.representationAlpha c j =
          b.representationSecondaryTargetAlpha c j hi j.lt_large :=
        hnormal'.trans (hrest.trans htarget)
      exact False.elim
        ((not_lt_of_ge htargetUpper.le) (heq ▸ hmiddleStrict))

/-- With `B_(i-1)` identified as primary, its defect is the source-middle
same-prefix defect at the next boundary.  This is the strict triangle on
lines 2223--2227. -/
theorem middleTargetPrimaryDefect_eq_sourceMiddleNextDefect_of_previousPrimary
    [Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hiTwo) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hiTwo))
    (hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j) :
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
  let previous := previousRepresentationIndex j hiTwo
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  let middleDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let targetDefect :=
    a.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hiTwo hcross hprimary
  have hstrict : (outerShift : WithTop ℚ) +
      b.representationAlpha c previous < a.representationAlpha c j :=
    hlower.trans_lt hprimary
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationPrimaryDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    rfl
  have hshiftSum : outerShift + previousShift = baseShift := by
    dsimp only [outerShift, previousShift, baseShift]
    push_cast
    ring
  have hbaseStrict : (baseShift : WithTop ℚ) + previousDefect <
      a.representationAlpha c j := by
    calc
      (baseShift : WithTop ℚ) + previousDefect =
          (outerShift : WithTop ℚ) +
            b.representationAlpha c previous := by
        rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, hshiftSum]
      _ < a.representationAlpha c j := hstrict
  have hmiddleLe : b.representationAlpha c j ≤ previousDefect :=
    a.middleTargetAlpha_le_previousMiddlePrimaryDefect
      b c hbcOrder hbcDefect j hiTwo hcross hprimary hprevious
  have hmiddleStrict : (baseShift : WithTop ℚ) +
      b.representationAlpha c j < a.representationAlpha c j :=
    (add_le_add_right hmiddleLe _).trans_lt hbaseStrict
  have hshifted : ((baseShift + middleShift : ℚ) : WithTop ℚ) +
      middleDefect < (targetShift : WithTop ℚ) + targetDefect := by
    calc
      ((baseShift + middleShift : ℚ) : WithTop ℚ) + middleDefect =
          (baseShift : WithTop ℚ) + b.representationAlpha c j := by
        rw [hmiddlePrimary]
        unfold representationPrimaryDefect
        simp only [WithTop.coe_add, add_assoc, middleShift, middleDefect]
      _ < a.representationAlpha c j := hmiddleStrict
      _ ≤ (targetShift : WithTop ℚ) + targetDefect := by
        simpa only [targetShift, targetDefect, representationPrimaryDefect]
          using a.representationAlpha_le_primary c j
  have hjLt : j.val < n + 1 := j.lt_large
  have hshiftLe : targetShift ≤ baseShift + middleShift := by
    dsimp only [targetShift, baseShift, middleShift]
    push_cast
    have hcrossQ :
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) ≤
          (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  have hshifted' : ((baseShift + middleShift : ℚ) : WithTop ℚ) +
      middleDefect < ((baseShift + middleShift : ℚ) : WithTop ℚ) +
        targetDefect :=
    hshifted.trans_le (add_le_add (by exact_mod_cast hshiftLe) le_rfl)
  have hdefect : middleDefect < targetDefect :=
    (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted'
  have hdefect' :
      c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) <
        c.truncatedPrefixDefect a (-1) (j.val - 1) (j.val + 1) := by
    simpa only [middleDefect, targetDefect,
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

/-- The preceding-primary alternative reaches the same common shifted
`A_i` bound as the preceding-current alternative. -/
theorem shiftedNextSourceAlpha_le_shift_previousMiddle_of_previousPrimary
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hi.1) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hi.1)) :
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
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let desiredShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect :=
    b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  let middleDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have hmiddlePrimary := a.middleTargetAlpha_eq_primary_of_previousPrimary
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hcross hprimary
      hprevious
  have htriangle :=
    a.middleTargetPrimaryDefect_eq_sourceMiddleNextDefect_of_previousPrimary
      b c hbcOrder hbcDefect j hi.1 hcross hprimary hprevious hmiddlePrimary
  have hnext : a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      middleDefect := by
    have hcondition := habDefect (nextRepresentationIndex j hi.2)
    rw [a.coe_representationAlphaValue b
      (nextRepresentationIndex j hi.2)] at hcondition
    change a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
    rw [htriangle]
    simpa only [nextRepresentationIndex] using hcondition
  have hmiddleLe : b.representationAlpha c j ≤ previousDefect :=
    a.middleTargetAlpha_le_previousMiddlePrimaryDefect
      b c hbcOrder hbcDefect j hi.1 hcross hprimary hprevious
  have hpreviousExpanded : b.representationAlpha c previous =
      (previousShift : WithTop ℚ) + previousDefect := by
    rw [hprevious]
    unfold representationPrimaryDefect
    simp only [previousRepresentationIndex, Nat.sub_sub,
      Nat.sub_add_cancel (show 1 ≤ j.val by omega)]
    rfl
  have hmiddleExpanded : b.representationAlpha c j =
      (middleShift : WithTop ℚ) + middleDefect := by
    rw [hmiddlePrimary]
    rfl
  have hdesired : desiredShift = baseShift + middleShift := by
    dsimp only [desiredShift, baseShift, middleShift]
    push_cast
    ring
  have houter : outerShift + previousShift = baseShift := by
    dsimp only [outerShift, previousShift, baseShift]
    push_cast
    ring
  change (desiredShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
    (outerShift : WithTop ℚ) + b.representationAlpha c previous
  calc
    (desiredShift : WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
      (desiredShift : WithTop ℚ) + middleDefect :=
        add_le_add_right hnext _
    _ = (baseShift : WithTop ℚ) + b.representationAlpha c j := by
      rw [hmiddleExpanded, hdesired, WithTop.coe_add]
      ac_rfl
    _ ≤ (baseShift : WithTop ℚ) + previousDefect :=
      add_le_add_right hmiddleLe _
    _ = (outerShift : WithTop ℚ) + b.representationAlpha c previous := by
      rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, houter]

/-- Both surviving values of `B_(i-2)` give the same shifted lower bound
by `A_i`.  This is the common conclusion at line 2230. -/
theorem shiftedNextSourceAlpha_le_shift_previousMiddle_of_cross_failure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j) :
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
  rcases a.previousMiddleAlpha_eq_primary_or_current_of_cross_failure
      b c hbcOrder hbcDefect j hi.1 hcross hprimary with
    hprevious | ⟨hj, hprevious⟩
  · exact a.shiftedNextSourceAlpha_le_shift_previousMiddle_of_previousPrimary
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
        hcross hprimary hprevious
  · exact a.shiftedNextSourceAlpha_le_shift_previousMiddle_of_previousCurrent
      b c habDefect hbcOrder hbcDefect j hi hj hcross hprimary hprevious

end BONG.GoodBONG

end Bong
