/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyPreviousPrimary

/-!
# Beli (2019), Lemma 4.2: candidates at the next source boundary

After both alternatives for `B_(i-2)` reach the common shifted `A_i`
bound, the half-gap and secondary-previous candidates of `A_i` are too
large.  Thus `A_i` is its primary candidate.  This is lines 2230--2244.
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

/-- In the common shifted bound, the next source invariant cannot attain
its half-gap candidate.  The contradiction is the direct pair inequality
`S_i+S_(i+1)>T_(i-2)+T_(i-1)`. -/
theorem nextSourceAlpha_ne_halfGap_of_commonBound
    [Beli2006AlphaLaws.{u, z} K]
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
    (hcommon :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.representationAlpha c (previousRepresentationIndex j hi.1)) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) ≠
      a.representationHalfGap b (nextRepresentationIndex j hi.2) := by
  intro hhalf
  let commonShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let outerShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hstrict : (commonShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) <
        a.representationAlpha c j := by
    have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
      b c hbcOrder hbcDefect j hi.1 hcross hprimary
    exact hcommon.trans_lt (by
      simpa only [outerShift] using hlower.trans_lt hprimary)
  have htargetHalf : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    let targetPair : Fin n := ⟨j.val - 2, by omega⟩
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryRightHalfGap c j hi.1)
    have hcast : targetPair.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hsucc : targetPair.succ =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [targetPair, Fin.val_succ]
      omega
    calc
      a.representationAlpha c j ≤
          (((a.order ⟨j.val, j.lt_large⟩ -
            c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            (c.halfGapValue targetPair : WithTop ℚ) := hraw
      _ = _ := by
        unfold halfGapValue orderGap
        rw [hcast, hsucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        ring
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hcontradiction := hstrict.trans_le htargetHalf
  rw [hhalf] at hcontradiction
  unfold representationHalfGap at hcontradiction
  norm_cast at hcontradiction
  simp only [nextRepresentationIndex, Rat.divInt_eq_div] at hcontradiction
  push_cast at hcontradiction
  have hdirectQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ + b.order ⟨j.val, j.lt_large⟩ := by
    exact_mod_cast hdirectRaw
  dsimp only [commonShift] at hcontradiction
  push_cast at hcontradiction
  linarith

/-- If the next boundary is interior, its secondary-previous candidate is
strictly larger than the preceding source alpha.  This is the second
deletion on lines 2236--2239. -/
theorem sourceAlpha_lt_shifted_nextSecondaryPrevious
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hnext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsource : a.representationAlpha b j =
      a.representationPrimaryDefect b j) :
    a.representationAlpha b j <
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationSecondaryPreviousDefect b
          (nextRepresentationIndex j hi.2) (by
            simp only [nextRepresentationIndex]
            omega) := by
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.2 hi.1 hnext
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have halphaNe := a.representationAlpha_ne_top b j
  have hdefectNe :
      a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) ≠ ⊤ := by
    intro htop
    have halphaTop := hsource
    unfold representationPrimaryDefect at halphaTop
    rw [htop, add_top] at halphaTop
    exact halphaNe halphaTop
  rw [hsource]
  unfold representationPrimaryDefect representationSecondaryPreviousDefect
  norm_cast
  simp only [nextRepresentationIndex, Nat.add_sub_cancel]
  push_cast
  have hessentialQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ + a.order ⟨j.val + 2, hnext⟩ := by
    exact_mod_cast hessentialRaw
  have hshiftQ :
      (a.order ⟨j.val, j.lt_large⟩ : ℚ) -
          b.order ⟨j.val - 1, by omega⟩ <
        (a.order ⟨j.val, j.lt_large⟩ : ℚ) +
          b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ +
          (a.order ⟨j.val + 1, hi.2⟩ +
            a.order ⟨j.val + 2, hnext⟩ -
            b.order ⟨j.val - 1, by omega⟩ -
            b.order ⟨j.val, j.lt_large⟩) := by
    linarith
  rw [← add_assoc]
  apply (WithTop.add_lt_add_iff_right hdefectNe).mpr
  exact WithTop.coe_lt_coe.mpr hshiftQ

/-- Once the half-gap and (when present) secondary-previous candidates have
been excluded, the next source invariant is its primary candidate. -/
theorem nextSourceAlpha_eq_primary_of_commonBound
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
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
    (hsource : a.representationAlpha b j =
      a.representationPrimaryDefect b j)
    (hprimary : a.representationPrimaryDefect b j <
      a.representationAlpha c j)
    (hcommon :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.representationAlpha c (previousRepresentationIndex j hi.1)) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) =
      a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
  let next := nextRepresentationIndex j hi.2
  have hhalf := a.nextSourceAlpha_ne_halfGap_of_commonBound b c hab hbcOrder
    hbcDefect j hi hessential hdirect hcross hprimary hcommon
  have hcrossNext : b.order ⟨next.val - 2, by
      have := next.le_small
      omega⟩ ≤ a.order ⟨next.val, next.lt_large⟩ := by
    have hlt := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
      b c hbcOrder j hi.1 hi.2 hessential hdirect
    dsimp only [next, nextRepresentationIndex]
    exact hlt.le
  have hbound :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + a.representationAlpha b next ≤
        a.representationAlpha b j := by
    have hlower := a.shift_previousMiddleAlpha_le_sourcePrimary
      b c hbcOrder hbcDefect j hi.1 hcross hprimary
    calc
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.representationAlpha c (previousRepresentationIndex j hi.1) := by
        simpa only [next] using hcommon
      _ ≤ a.representationPrimaryDefect b j := hlower
      _ = a.representationAlpha b j := hsource.symm
  by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
  · letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hnormal : a.representationAlpha b next =
        min (a.representationHalfGap b next)
          (min (a.representationPrimaryDefect b next)
            (a.representationSecondaryPreviousDefect b next hinterior)) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b next,
        a.representationAlphaPrime_eq_min_primary_previous
          b next hinterior hcrossNext]
    have hsecondary : a.representationAlpha b next ≠
        a.representationSecondaryPreviousDefect b next hinterior := by
      intro heq
      have hlarge : j.val + 2 < n + 1 := by
        dsimp only [next, nextRepresentationIndex] at hinterior
        omega
      have hlower := by
        letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
        exact a.sourceAlpha_lt_shifted_nextSecondaryPrevious
          b c j hi hlarge hessential hsource
      have heq' := congrArg (fun x =>
        (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + x) heq
      exact (not_lt_of_ge (heq' ▸ hbound)) hlower
    rcases min_choice (a.representationHalfGap b next)
        (min (a.representationPrimaryDefect b next)
          (a.representationSecondaryPreviousDefect b next hinterior)) with
      hgap | hprime
    · exact False.elim (hhalf (by simpa only [next] using hnormal.trans hgap))
    · rcases min_choice (a.representationPrimaryDefect b next)
          (a.representationSecondaryPreviousDefect b next hinterior) with
        hprimary' | hsecondary'
      · exact hnormal.trans (hprime.trans hprimary')
      · exact False.elim (hsecondary (hnormal.trans (hprime.trans hsecondary')))
  · have hnormal : a.representationAlpha b next =
        min (a.representationHalfGap b next)
          (a.representationPrimaryDefect b next) := by
      rw [a.representationAlpha_eq_min_halfGap_prime b next,
        a.representationAlphaPrime_eq_primary_of_not_interior b next hinterior]
    rcases min_choice (a.representationHalfGap b next)
        (a.representationPrimaryDefect b next) with hgap | hprimary'
    · exact False.elim (hhalf (by simpa only [next] using hnormal.trans hgap))
    · exact hnormal.trans hprimary'

/-- The strict comparison at lines 2241--2245 identifies the next source
primary defect with the preceding middle-target defect. -/
theorem nextSourcePrimaryDefect_eq_previousMiddleDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
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
      b.truncatedPrefixDefect c (-1) j.val (j.val - 2) := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ +
      a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let targetDefect := a.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2)
  have hsource :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) =
        (sourceShift : WithTop ℚ) + sourceDefect := by
    rw [hnextPrimary]
    unfold representationPrimaryDefect
    simp only [nextRepresentationIndex, Nat.add_sub_cancel, sourceShift, sourceDefect]
    rw [show j.val + 1 + 1 = j.val + 2 by omega]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have htarget : a.representationAlpha c j ≤
      (sourceShift : WithTop ℚ) + targetDefect := by
    simpa only [sourceShift, targetDefect, representationSecondaryDefect]
      using a.representationAlpha_le_secondary c j hi
  have hdefect : sourceDefect < targetDefect := by
    have hshifted : (sourceShift : WithTop ℚ) + sourceDefect <
        (sourceShift : WithTop ℚ) + targetDefect :=
      (hsource ▸ hstrict).trans_le htarget
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hshifted
  exact a.truncatedPrefixDefect_neg_eq_neg_of_lt_pos b c
    (j.val + 2) j.val (j.val - 2) hdefect

/-- The identified defect makes the shifted next primary candidate strictly
larger than the preceding shifted middle alpha, contradicting the common
bound.  This is lines 2245--2249. -/
theorem shift_previousMiddleAlpha_lt_shiftedNextSourcePrimary
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdefect : a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c (-1) j.val (j.val - 2)) :
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
        b.representationAlpha c (previousRepresentationIndex j hi.1) <
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
  let middleDefect := b.truncatedPrefixDefect c (-1) j.val (j.val - 2)
  have hmiddleUpper :=
    b.representationAlpha_le_primary c (previousRepresentationIndex j hi.1)
  have hessentialRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hi.2
  simp only [orderSequence_at, nextEssentialIndex] at hessentialRaw
  have hessentialQ : (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
      a.order ⟨j.val + 1, hi.2⟩ := by
    exact_mod_cast hessentialRaw
  calc
    _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        b.representationPrimaryDefect c
          (previousRepresentationIndex j hi.1) := add_le_add_right hmiddleUpper _
    _ < (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
      unfold representationPrimaryDefect
      simp only [previousRepresentationIndex, nextRepresentationIndex,
        Nat.sub_sub, Nat.add_sub_cancel]
      rw [show j.val - 1 + 1 = j.val by omega,
        show j.val + 1 + 1 = j.val + 2 by omega, hdefect]
      rw [← add_assoc, ← add_assoc]
      apply (WithTop.add_lt_add_iff_right (by
        intro htop
        have hcap := b.truncatedPrefixDefect_le_leftCap c (-1) j.val (j.val - 2)
        rw [htop] at hcap
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
        exact WithTop.coe_ne_top (le_antisymm le_top hcap))).mpr
      norm_cast
      push_cast
      linarith

end BONG.GoodBONG

end Bong
