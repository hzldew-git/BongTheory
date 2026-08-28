/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyDirectNonterminal
import Bong.Bong.Beli2019FullRankDefect

/-!
# Beli (2019), Lemma 4.2: the terminal left endpoint

At `i = n` the secondary candidates are absent.  The complete source prefixes
have the same square class; this first supplies the middle-target conclusion.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

set_option maxHeartbeats 800000

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- At `i = n`, the middle-to-target alpha has only its half-gap and primary
candidates.  Its primary defect is bounded by the corresponding target
primary defect after replacing the complete middle prefix. -/
theorem representationAlpha_le_leftDirect_middlePrimary_of_last
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hlast : j.val + 1 = n + 1) :
    a.representationAlpha c j ≤ b.representationPrimaryDefect c j := by
  have hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩ := by
    rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, hiNext, _⟩
    · exact hcurrent
    · change j.val + 1 < n + 1 at hiNext
      omega
  calc
    a.representationAlpha c j ≤ a.representationPrimaryDefect c j :=
      a.representationAlpha_le_primary c j
    _ ≤ b.representationPrimaryDefect c j := by
      unfold representationPrimaryDefect
      have hdefect : a.truncatedPrefixDefect c (-1) (j.val + 1)
          (j.val - 1) = b.truncatedPrefixDefect c (-1) (j.val + 1)
            (j.val - 1) := by
        rw [hlast]
        exact (a.truncatedPrefixDefect_fullLeft_invariant b c (-1)
          (j.val - 1)).symm
      rw [hdefect]
      gcongr
      norm_cast
      exact sub_le_sub_right hsourceCurrent
        (c.order ⟨j.val - 1, by omega⟩)

/-- Lemma 4.2(i)'s second direct conclusion at `i = n`. -/
theorem representationAlpha_le_leftDirect_middleAlpha_of_last
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbc : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j ≤ b.representationAlpha c j := by
  have hsourceCurrent : a.order ⟨j.val, j.lt_large⟩ ≤
      b.order ⟨j.val, j.lt_large⟩ := by
    rcases hab ⟨j.val, j.lt_large⟩ with hcurrent | ⟨_, hiNext, _⟩
    · exact hcurrent
    · change j.val + 1 < n + 1 at hiNext
      omega
  rw [b.representationAlpha_eq_min_halfGap_prime c j,
    b.representationAlphaPrime_eq_primary_of_not_interior c j (by omega)]
  exact le_min
    (a.representationAlpha_le_middleHalfGap_of_sourceCurrent_le
      b c j hsourceCurrent)
    (a.representationAlpha_le_leftDirect_middlePrimary_of_last
      b c hab j hlast)

/-- At the terminal boundary the reverse-order branch forces the middle
alpha to be its primary candidate.  After replacing the complete left
prefix, the shifted middle primary is exactly the target primary. -/
theorem representationAlpha_le_leftDirect_sourcePrimary_of_last_of_reverse
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
    (hreverse : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    a.representationAlpha c j ≤ a.representationPrimaryDefect b j := by
  let shift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1)
    (j.val + 1) (j.val - 1)
  let middleDefect := b.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  let targetDefect := a.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  have hmiddlePrime := b.middleTargetAlpha_eq_prime_of_current_lt_previous
    c hbcOrder hbcDefect j hiTwo hreverse
  have hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j := by
    rw [hmiddlePrime,
      b.representationAlphaPrime_eq_primary_of_not_interior c j (by omega)]
  have hmiddleAlpha := b.representationAlpha_le_leftAlpha c hbcDefect j
  let previous : Fin n := ⟨j.val - 1, by
    have := j.lt_large
    omega⟩
  have hadjacentRaw := b.order_sub_add_alpha_le_cappedAdjacent previous
  have hpreviousCast : previous.castSucc =
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ =
      (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  rw [hpreviousCast, hpreviousSucc] at hadjacentRaw
  have hsourceDefectReplace : sourceDefect =
      b.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) := by
    dsimp only [sourceDefect]
    rw [hlast]
    exact (a.truncatedPrefixDefect_fullLeft_invariant b b (-1)
      (j.val - 1)).symm
  have hadjacent :
      (((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          (b.alphaValue previous : WithTop ℚ) ≤ sourceDefect := by
    rw [hsourceDefectReplace]
    have hcoerce :
        ((((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            (b.alphaValue previous : WithTop ℚ)) =
          (((((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) +
              b.alphaValue previous : ℚ)) : WithTop ℚ) := by
      rw [WithTop.coe_add]
    rw [hcoerce]
    calc
      (((((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) +
            b.alphaValue previous : ℚ)) : WithTop ℚ) ≤
          b.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) := by
        simpa only [previous, show j.val - 1 + 2 = j.val + 1 by omega]
          using hadjacentRaw
      _ = b.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) :=
        b.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1)
  have hshiftedMiddle : (shift : WithTop ℚ) +
      b.representationAlpha c j ≤ a.representationPrimaryDefect b j := by
    unfold representationPrimaryDefect
    change (shift : WithTop ℚ) + b.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + sourceDefect
    calc
      (shift : WithTop ℚ) + b.representationAlpha c j ≤
          (shift : WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) :=
        add_le_add_right hmiddleAlpha _
      _ = (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          ((((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
            (b.alphaValue previous : WithTop ℚ)) := by
        rw [← add_assoc]
        congr 1
        norm_cast
        dsimp only [shift]
        push_cast
        ring
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + sourceDefect := by
        let outer : WithTop ℚ :=
          (((a.order ⟨j.val, j.lt_large⟩ -
            b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ)
        let inner : WithTop ℚ :=
          (((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
              (b.alphaValue previous : WithTop ℚ)
        change outer + inner ≤ outer + sourceDefect
        exact add_le_add_right hadjacent outer
  have hmiddleDefectReplace : middleDefect = targetDefect := by
    dsimp only [middleDefect, targetDefect]
    rw [hlast]
    exact (b.truncatedPrefixDefect_fullLeft_invariant a c (-1)
      (j.val - 1)).symm
  have htargetPrimary : a.representationPrimaryDefect c j =
      (shift : WithTop ℚ) + b.representationAlpha c j := by
    rw [hmiddlePrimary]
    unfold representationPrimaryDefect
    change
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + targetDefect =
        (shift : WithTop ℚ) +
          ((((b.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) + middleDefect)
    rw [hmiddleDefectReplace, ← add_assoc]
    congr 1
    norm_cast
    dsimp only [shift]
    push_cast
    ring
  exact (a.representationAlpha_le_primary c j).trans
    (htargetPrimary.trans_le hshiftedMiddle)

/-- In the crossed terminal branch, the preceding-current candidate would
identify a finite capped defect with the full-rank positive defect. -/
theorem previousMiddleCurrent_impossible_of_last_cross_failure
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
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
        b.representationSecondaryCurrentDefect c previous hk) : False := by
  have heq := a.previousMiddleCurrentDefect_eq_sourceMiddleNextDefect
    b c hbcOrder hbcDefect j hiTwo hj hcross hprimary hprevious
  have htop : a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) = ⊤ := by
    simpa only [hlast] using a.truncatedPrefixDefect_full_eq_top b
  have hfinite : b.truncatedPrefixDefect c (-1) (j.val + 1)
      (j.val - 1) ≠ ⊤ := by
    intro htopLeft
    have hcap := b.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    rw [htopLeft, c.prefixAlphaCap_of_internal (by omega) (by omega)]
      at hcap
    exact (not_le_of_gt (WithTop.coe_lt_top
      (c.alphaValue ⟨j.val - 2, by
        have := j.lt_large
        omega⟩))) hcap
  exact hfinite (heq.trans htop)

/-- If the preceding crossed candidate is primary, the terminal middle
alpha cannot attain its half-gap candidate and hence is primary. -/
theorem middleTargetAlpha_eq_primary_of_previousPrimary_of_last
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hiTwo) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hiTwo)) :
    b.representationAlpha c j = b.representationPrimaryDefect c j := by
  let previous := previousRepresentationIndex j hiTwo
  let outerShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let baseShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousShift : ℚ := ((b.order
    ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let previousDefect := b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  let targetPair : Fin n := ⟨j.val - 2, by
    have := j.lt_large
    omega⟩
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
          (outerShift : WithTop ℚ) + b.representationAlpha c previous := by
        rw [hpreviousExpanded, ← add_assoc, ← WithTop.coe_add, hshiftSum]
      _ < a.representationAlpha c j := hstrict
  have hmiddleLe : b.representationAlpha c j ≤ previousDefect :=
    a.middleTargetAlpha_le_previousMiddlePrimaryDefect
      b c hbcOrder hbcDefect j hiTwo hcross hprimary hprevious
  have hmiddleStrict : (baseShift : WithTop ℚ) +
      b.representationAlpha c j < a.representationAlpha c j :=
    (add_le_add_right hmiddleLe _).trans_lt hbaseStrict
  have hnormal : b.representationAlpha c j =
      min (b.representationHalfGap c j)
        (b.representationPrimaryDefect c j) := by
    rw [b.representationAlpha_eq_min_halfGap_prime c j,
      b.representationAlphaPrime_eq_primary_of_not_interior c j (by omega)]
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have hhalfUpper : a.representationAlpha c j ≤
      (baseShift : WithTop ℚ) + b.representationHalfGap c j := by
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap c j hiTwo)
    calc
      a.representationAlpha c j ≤
          (((a.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
              WithTop ℚ) + (c.halfGapValue targetPair : WithTop ℚ) := hraw
      _ ≤ (baseShift : WithTop ℚ) + b.representationHalfGap c j := by
        unfold representationHalfGap halfGapValue orderGap
        rw [htargetCast, htargetSucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        have hcrossQ :
            (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) ≤
              (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
          exact_mod_cast hcross
        dsimp only [baseShift]
        push_cast
        linarith
  rcases min_choice (b.representationHalfGap c j)
      (b.representationPrimaryDefect c j) with hhalf | hprimaryChoice
  · have heq : b.representationAlpha c j =
        b.representationHalfGap c j := hnormal.trans hhalf
    exact False.elim ((not_lt_of_ge hhalfUpper) (heq ▸ hmiddleStrict))
  · exact hnormal.trans hprimaryChoice

/-- The same terminal contradiction in the preceding-primary branch. -/
theorem previousMiddlePrimary_impossible_of_last_cross_failure
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hprevious :
      b.representationAlpha c (previousRepresentationIndex j hiTwo) =
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hiTwo))
    (hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j) : False := by
  have heq :=
    a.middleTargetPrimaryDefect_eq_sourceMiddleNextDefect_of_previousPrimary
      b c hbcOrder hbcDefect j hiTwo hcross hprimary hprevious hmiddlePrimary
  have htop : a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) = ⊤ := by
    simpa only [hlast] using a.truncatedPrefixDefect_full_eq_top b
  have hfinite : b.truncatedPrefixDefect c (-1) (j.val + 1)
      (j.val - 1) ≠ ⊤ := by
    intro htopLeft
    have hcap := b.truncatedPrefixDefect_le_rightCap c (-1)
      (j.val + 1) (j.val - 1)
    rw [htopLeft, c.prefixAlphaCap_of_internal (by omega) (by omega)]
      at hcap
    exact (not_le_of_gt (WithTop.coe_lt_top
      (c.alphaValue ⟨j.val - 2, by
        have := j.lt_large
        omega⟩))) hcap
  exact hfinite (heq.trans htop)

/-- A failing source primary candidate is impossible in the crossed
terminal branch, after splitting the preceding middle candidate. -/
theorem representationAlpha_le_leftDirect_sourcePrimary_of_last_of_cross
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1)
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    a.representationAlpha c j ≤ a.representationPrimaryDefect b j := by
  by_contra hfailure
  have hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j := lt_of_not_ge hfailure
  rcases a.previousMiddleAlpha_eq_primary_or_current_of_cross_failure
      b c hbcOrder hbcDefect j hiTwo hcross hprimary with
    hprevious | ⟨hj, hprevious⟩
  · have hmiddlePrimary :=
      a.middleTargetAlpha_eq_primary_of_previousPrimary_of_last
        b c hbcOrder hbcDefect j hiTwo hlast hcross hprimary hprevious
    exact a.previousMiddlePrimary_impossible_of_last_cross_failure
      b c hbcOrder hbcDefect j hiTwo hlast hcross hprimary hprevious
        hmiddlePrimary
  · exact a.previousMiddleCurrent_impossible_of_last_cross_failure
      b c hbcOrder hbcDefect j hiTwo hlast hj hcross hprimary hprevious

/-- Lemma 4.2(i)'s first direct conclusion at the terminal boundary. -/
theorem representationAlpha_le_leftDirect_sourceAlpha_of_last
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) (hlast : j.val + 1 = n + 1) :
    a.representationAlpha c j ≤ a.representationAlpha b j := by
  rw [a.representationAlpha_eq_min_halfGap_prime b j,
    a.representationAlphaPrime_eq_primary_of_not_interior b j (by omega)]
  apply le_min
  · exact a.representationAlpha_le_leftDirect_sourceHalfGap_of_last
      b c hab hbcOrder j hiTwo hlast
  · by_cases hcross : c.order
        ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
          b.order ⟨j.val, j.lt_large⟩
    · exact a.representationAlpha_le_leftDirect_sourcePrimary_of_last_of_cross
        b c hbcOrder hbcDefect j hiTwo hlast hcross
    · exact a.representationAlpha_le_leftDirect_sourcePrimary_of_last_of_reverse
        b c hbcOrder hbcDefect j hiTwo hlast (lt_of_not_ge hcross)

/-- Lemma 4.2(i)'s two direct inequalities, uniformly at every boundary. -/
theorem leftDirect_bounds
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationAlpha b j ∧
      a.representationAlpha c j ≤ b.representationAlpha c j := by
  by_cases hlast : j.val + 1 = n + 1
  · by_cases hfirst : j.val = 1
    · exact ⟨a.representationAlpha_le_leftDirect_sourceAlpha_of_eq_one
        b c hbcOrder j hfirst,
        a.representationAlpha_le_leftDirect_middleAlpha_of_eq_one_of_last
          b c hab hbcOrder j hfirst hlast hessential⟩
    · have hiTwo : 1 < j.val := by
        have := j.pos
        omega
      exact ⟨a.representationAlpha_le_leftDirect_sourceAlpha_of_last
        b c hab hbcOrder hbcDefect j hiTwo hlast,
        a.representationAlpha_le_leftDirect_middleAlpha_of_last
          b c hab hbcOrder j hiTwo hlast hessential⟩
  · have hnext : j.val + 1 < n + 1 := by
      have := j.lt_large
      omega
    exact a.leftDirect_bounds_of_not_last
      b c hab habDefect hbcOrder hbcDefect j hnext hessential hdirect

end BONG.GoodBONG

end Bong
