/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossNextPrimary

/-!
# Beli (2019), Lemma 4.2: closing the noncrossed left-direct subcase

This file completes lines 2287--2296.  Lemma 2.7(ii) replaces the
positive defect with the shortened target prefix by the negative defect
with the current target prefix.  The strict capped-defect triangle then
identifies the next source primary defect with the defect which bounds
`B_(i-1)`, contradicting the second common bound.
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

/-- Lemma 2.7(ii), in the form used on lines 2287--2290: essentiality
supplies the crossing needed to replace the target secondary defect by
the current-prefix negative defect. -/
theorem middleTargetAlpha_le_secondaryCurrent_of_nextEssential
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j) :
    a.representationAlpha c j ≤
      a.representationSecondaryCurrentDefect c j hi := by
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hi.2
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hcross : c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
      a.order ⟨j.val + 1, hi.2⟩ := hessentialRaw.le
  calc
    a.representationAlpha c j ≤ a.representationAlphaPrime c j :=
      a.representationAlpha_le_prime c j
    _ = min (a.representationPrimaryDefect c j)
        (a.representationSecondaryCurrentDefect c j hi) :=
      a.representationAlphaPrime_eq_min_primary_current c j hi hcross
    _ ≤ a.representationSecondaryCurrentDefect c j hi := min_le_right _ _

/-- Lines 2287--2293: strict comparison with the replaced target
secondary candidate identifies
`d[-a_(1,i+1)b_(1,i-1)]` with `d[b_(1,i-1)c_(1,i-1)]`. -/
theorem nextSourcePrimaryDefect_eq_currentMiddleTargetDefect_of_noncross
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hnextPrimary : a.representationAlpha b (nextRepresentationIndex j hi.2) =
      a.representationPrimaryDefect b (nextRepresentationIndex j hi.2))
    (hstrict :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) <
          a.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c 1 j.val j.val := by
  let commonShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sharedShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let targetDefect := a.truncatedPrefixDefect c (-1) (j.val + 2) j.val
  have hsource : (commonShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) =
        (sharedShift : WithTop ℚ) + sourceDefect := by
    rw [hnextPrimary]
    unfold representationPrimaryDefect
    simp only [nextRepresentationIndex, Nat.add_sub_cancel,
      commonShift, sharedShift, sourceDefect]
    rw [show j.val + 1 + 1 = j.val + 2 by omega]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have htarget : a.representationAlpha c j ≤
      (sharedShift : WithTop ℚ) + targetDefect := by
    simpa only [sharedShift, targetDefect,
      representationSecondaryCurrentDefect] using
        a.middleTargetAlpha_le_secondaryCurrent_of_nextEssential c j hi hessential
  have hdefect : sourceDefect < targetDefect := by
    have hshifted : (sharedShift : WithTop ℚ) + sourceDefect <
        (sharedShift : WithTop ℚ) + targetDefect :=
      (hsource ▸ hstrict).trans_le htarget
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted
  exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
    (j.val + 2) j.val j.val hdefect

/-- Lines 2293--2296: condition 2.1(ii) for the middle--target pair and
the direct pair inequality turn the preceding defect identity into the
strict reverse of the second common bound. -/
theorem shiftedMiddleAlpha_lt_shiftedNextSourcePrimary_of_noncross
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hdefect : a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c 1 j.val j.val) :
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j <
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let commonShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sharedShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  have hmiddle : b.representationAlpha c j ≤ sourceDefect := by
    have h := hbcDefect j
    rw [b.coe_representationAlphaValue c j] at h
    simpa only [sourceDefect, hdefect] using h
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hshift : outerShift < sharedShift := by
    dsimp only [outerShift, sharedShift]
    push_cast
    have hdirectQ :
        (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) +
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
          a.order ⟨j.val + 1, hi.2⟩ +
            b.order ⟨j.val, j.lt_large⟩ := by
      exact_mod_cast hdirectRaw
    linarith
  calc
    (outerShift : WithTop ℚ) + b.representationAlpha c j ≤
        (outerShift : WithTop ℚ) + sourceDefect :=
      add_le_add_right hmiddle _
    _ < (sharedShift : WithTop ℚ) + sourceDefect :=
      WithTop.add_lt_add_right (by
        intro htop
        have hcap := a.truncatedPrefixDefect_le_rightCap b
          (-1) (j.val + 2) j.val
        dsimp only [sourceDefect] at htop
        rw [htop] at hcap
        rw [b.prefixAlphaCap_of_internal j.pos j.lt_large] at hcap
        exact WithTop.coe_ne_top (le_antisymm le_top hcap))
        (by exact_mod_cast hshift)
    _ = (commonShift : WithTop ℚ) +
        a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
      unfold representationPrimaryDefect
      simp only [nextRepresentationIndex, Nat.add_sub_cancel,
        commonShift, sharedShift, sourceDefect]
      rw [show j.val + 1 + 1 = j.val + 2 by omega]
      rw [← add_assoc]
      congr 1
      norm_cast
      push_cast
      ring

/-- Lemma 4.2(i), first inequality, in the noncrossed interior subcase. -/
theorem leftDirect_sourceBound_of_noncross
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
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
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    a.representationAlpha c j ≤ a.representationAlpha b j := by
  by_contra hfailure
  obtain ⟨_, hprimary⟩ := a.leftDirect_sourceFailure_eq_primary
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hcommon := a.commonNextSourceAlpha_bounds_of_noncross_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
      hnoncross hfailure
  have hnextPrimary := a.nextSourceAlpha_eq_primary_of_noncross_failure
    (sourceLaws := sourceLaws) (middleLaws := middleLaws)
    (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
      hnoncross hfailure
  have hstrict :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) <
          a.representationAlpha c j := hcommon.1.trans_lt hprimary
  have hdefect :=
    a.nextSourcePrimaryDefect_eq_currentMiddleTargetDefect_of_noncross
      (targetLaws := targetLaws) b c j hi hessential hnextPrimary hstrict
  have hreverse :=
    a.shiftedMiddleAlpha_lt_shiftedNextSourcePrimary_of_noncross
      b c hbcDefect j hi hdirect hdefect
  rw [hnextPrimary] at hcommon
  exact (not_lt_of_ge hcommon.2) hreverse

/-- Lemma 4.2(i)'s first direct inequality at every interior boundary.
The order at `S_i` splits exhaustively into the crossed and noncrossed
subcases treated in the preceding files. -/
theorem leftDirect_sourceBound_of_interior
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
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
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.representationAlpha b j := by
  by_cases hcross :
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
        b.order ⟨j.val, j.lt_large⟩
  · exact a.leftDirect_sourceBound_of_cross
      (sourceLaws := sourceLaws) (middleLaws := middleLaws)
      (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hcross
  · have hnoncross : b.order ⟨j.val, j.lt_large⟩ <
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ :=
      lt_of_not_ge hcross
    exact a.leftDirect_sourceBound_of_noncross
      (sourceLaws := sourceLaws) (middleLaws := middleLaws)
      (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hnoncross

end BONG.GoodBONG

end Bong
