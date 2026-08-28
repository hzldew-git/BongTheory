/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleFailureHalfGap

/-!
# Beli (2019), Lemma 4.2: the shifted next prime invariant

This file formalizes the first half of lines 2325--2335.  The two offsets
in the lower bound for `B_(i-1)` are strictly larger than
`S_i-R_(i+1)`.  After `A_i=A'_i`, this gives a strict upper bound for the
shifted prime invariant.  Its Lemma 2.7(i) normal form then reduces to the
next source prefix defect; the endpoint case is handled separately, exactly
as prescribed by the paper's convention of omitting nonexistent terms.
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

/-- Lines 2325--2327: both offsets in the lower minimum for `B_(i-1)`
strictly dominate `S_i-R_(i+1)`. -/
theorem shiftedNextSourcePrime_lt_middleTargetAlpha_of_failure
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
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    (((b.order ⟨j.val, j.lt_large⟩ -
      a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationAlphaPrime b (nextRepresentationIndex j hi.2) <
      b.representationAlpha c j := by
  let next := nextRepresentationIndex j hi.2
  let base : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let firstShift : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let secondShift : ℚ := ((2 * b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hprime := a.nextSourceAlpha_eq_prime_of_middleTarget_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hlowerRaw :=
    a.min_shifted_nextSourceAlpha_le_middleTargetAlpha_of_leftDirect_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hlower :
      min ((firstShift : WithTop ℚ) + a.representationAlphaPrime b next)
          ((secondShift : WithTop ℚ) + a.representationAlphaPrime b next) ≤
        b.representationAlpha c j := by
    simpa only [firstShift, secondShift, next, hprime] using hlowerRaw
  have hfinite : a.representationAlphaPrime b next ≠ ⊤ := by
    intro htop
    have halphaTop : a.representationAlpha b next = ⊤ := hprime.trans htop
    exact a.representationAlpha_ne_top b next halphaTop
  have hpreviousRaw := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    exact hessential.1 j.pos hi.2
  simp only [orderSequence_at, nextEssentialIndex] at hpreviousRaw
  have hbaseFirst : base < firstShift := by
    dsimp only [base, firstShift]
    push_cast
    have hpreviousQ :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          a.order ⟨j.val + 1, hi.2⟩ := by
      exact_mod_cast hpreviousRaw
    linarith
  have hdirectRaw := hdirect hi.1 hi.2
  simp only [nextEssentialIndex] at hdirectRaw
  have hbaseSecond : base < secondShift := by
    dsimp only [base, secondShift]
    push_cast
    have hdirectQ :
        (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) +
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
          a.order ⟨j.val + 1, hi.2⟩ +
            b.order ⟨j.val, j.lt_large⟩ := by
      exact_mod_cast hdirectRaw
    linarith
  have hstrict : (base : WithTop ℚ) +
      a.representationAlphaPrime b next <
        min ((firstShift : WithTop ℚ) + a.representationAlphaPrime b next)
          ((secondShift : WithTop ℚ) + a.representationAlphaPrime b next) :=
    lt_min
      (WithTop.add_lt_add_right hfinite (by exact_mod_cast hbaseFirst))
      (WithTop.add_lt_add_right hfinite (by exact_mod_cast hbaseSecond))
  simpa only [base, next] using hstrict.trans_le hlower

/-- Lines 2327--2335: the shifted prime invariant is exactly the next
source prefix defect.  At an interior next boundary the other Lemma 2.7(i)
candidate is too large; at the terminal boundary it is absent. -/
theorem shiftedNextSourcePrime_eq_nextSourceDefect_of_failure
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
    (hsourceBound : a.representationAlpha c j ≤
      a.representationAlpha b j)
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    (((b.order ⟨j.val, j.lt_large⟩ -
      a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationAlphaPrime b (nextRepresentationIndex j hi.2) =
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val := by
  let next := nextRepresentationIndex j hi.2
  let base : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  have hsmall := a.shiftedNextSourcePrime_lt_middleTargetAlpha_of_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hmiddleSource : b.representationAlpha c j <
      a.representationAlpha b j :=
    (lt_of_not_ge hfailure).trans_le hsourceBound
  have hcrossNext : b.order ⟨next.val - 2, by
      have := next.le_small
      omega⟩ ≤ a.order ⟨next.val, next.lt_large⟩ := by
    have hlt := a.keyLemmaLeftDirect_middlePrevious_lt_sourceNext
      b c hbcOrder j hi.1 hi.2 hessential hdirect
    dsimp only [next, nextRepresentationIndex]
    exact hlt.le
  let opposite : ℚ := ((a.order ⟨j.val + 1, hi.2⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  have hprimaryFormula : a.representationPrimaryDefect b next =
      (opposite : WithTop ℚ) + sourceDefect := by
    unfold representationPrimaryDefect
    simp only [next, nextRepresentationIndex, Nat.add_sub_cancel,
      opposite, sourceDefect]
  have hcancel : base + opposite = 0 := by
    dsimp only [base, opposite]
    push_cast
    ring
  have hprimaryShift : (base : WithTop ℚ) +
      a.representationPrimaryDefect b next = sourceDefect := by
    rw [hprimaryFormula, ← add_assoc, ← WithTop.coe_add, hcancel]
    simp
  by_cases hinterior : 1 < next.val ∧ next.val + 1 < n + 1
  · let secondTerm : WithTop ℚ := (base : WithTop ℚ) +
      a.representationSecondaryPreviousDefect b next hinterior
    have htwoStepRaw := a.orderSequence.twoStep j.val (by
      dsimp only [next, nextRepresentationIndex] at hinterior
      omega)
    have htwoStep : a.order ⟨j.val, j.lt_large⟩ ≤
        a.order ⟨j.val + 2, by
          dsimp only [next, nextRepresentationIndex] at hinterior
          omega⟩ := by
      change a.orderSequence.entry j.val j.lt_large ≤
        a.orderSequence.entry (j.val + 2) (by
          dsimp only [next, nextRepresentationIndex] at hinterior
          omega)
      exact htwoStepRaw
    let primaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
    let primaryDefect :=
      a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)
    let secondaryShift : ℚ := ((a.order ⟨next.val, next.lt_large⟩ +
      a.order ⟨next.val + 1, hinterior.2⟩ -
      b.order ⟨next.val - 2, by have := next.le_small; omega⟩ -
      b.order ⟨next.val - 1, by have := next.le_small; omega⟩ : Int) : ℚ)
    let secondaryDefect :=
      a.truncatedPrefixDefect b (-1) next.val (next.val - 2)
    have hnextCurrent : (⟨next.val, next.lt_large⟩ : Fin (n + 1)) =
        ⟨j.val + 1, hi.2⟩ := by
      apply Fin.ext
      simp only [next, nextRepresentationIndex]
    have hnextNext : (⟨next.val + 1, hinterior.2⟩ : Fin (n + 1)) =
        ⟨j.val + 2, by
          dsimp only [next, nextRepresentationIndex] at hinterior
          omega⟩ := by
      apply Fin.ext
      simp only [next, nextRepresentationIndex]
    have hmiddlePrevious :
        (⟨next.val - 2, by have := next.le_small; omega⟩ : Fin (n + 1)) =
          ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
      apply Fin.ext
      simp only [next, nextRepresentationIndex]
      omega
    have hmiddleCurrent :
        (⟨next.val - 1, by have := next.le_small; omega⟩ : Fin (n + 1)) =
          ⟨j.val, j.lt_large⟩ := by
      apply Fin.ext
      simp only [next, nextRepresentationIndex, Nat.add_sub_cancel]
    have hdefect : secondaryDefect = primaryDefect := by
      dsimp only [secondaryDefect, primaryDefect]
      have hfirst : next.val = j.val + 1 := by
        simp only [next, nextRepresentationIndex]
      rw [hfirst]
      congr 1
    have hshift : primaryShift ≤ base + secondaryShift := by
      dsimp only [primaryShift, base, secondaryShift]
      rw [hnextCurrent, hnextNext, hmiddlePrevious, hmiddleCurrent]
      push_cast
      have htwoStepQ :
          (a.order ⟨j.val, j.lt_large⟩ : ℚ) ≤
            a.order ⟨j.val + 2, by
              dsimp only [next, nextRepresentationIndex] at hinterior
              omega⟩ := by
        exact_mod_cast htwoStep
      linarith
    have hprimarySecond : a.representationPrimaryDefect b j ≤
        secondTerm := by
      change (primaryShift : WithTop ℚ) + primaryDefect ≤
        (base : WithTop ℚ) +
          ((secondaryShift : WithTop ℚ) + secondaryDefect)
      rw [hdefect, ← add_assoc]
      have hshiftTop : (primaryShift : WithTop ℚ) ≤
          ((base + secondaryShift : ℚ) : WithTop ℚ) := by
        exact_mod_cast hshift
      exact add_le_add hshiftTop le_rfl
    have hsecondLarge : b.representationAlpha c j < secondTerm := by
      exact hmiddleSource.trans_le
        ((a.representationAlpha_le_primary b j).trans hprimarySecond)
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hnormalPrime := a.representationAlphaPrime_eq_min_primary_previous
      b next hinterior hcrossNext
    have hnormal : (base : WithTop ℚ) +
        a.representationAlphaPrime b next = min sourceDefect secondTerm := by
      rw [hnormalPrime, add_min]
      rw [hprimaryShift]
    rcases min_choice sourceDefect secondTerm with hsource | hsecond
    · simpa only [base, next, sourceDefect] using hnormal.trans hsource
    · have heq : (base : WithTop ℚ) +
          a.representationAlphaPrime b next = secondTerm :=
        hnormal.trans hsecond
      have hsmall' : (base : WithTop ℚ) +
          a.representationAlphaPrime b next < b.representationAlpha c j := by
        simpa only [base, next] using hsmall
      exact False.elim ((not_lt_of_ge hsecondLarge.le) (heq ▸ hsmall'))
  · have hnormal := a.representationAlphaPrime_eq_primary_of_not_interior
      b next hinterior
    rw [hnormal, hprimaryShift]

end BONG.GoodBONG

end Bong
