/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackFinalTriangles

/-!
# Beli (2019), Lemma 4.2: closing the left fallback branch

This file assembles lines 2351--2415.  Assuming failure of the fallback
bound forces `A_i` to be primary and `B_(i-1)` to be secondary.  Two strict
triangles then give a shifted lower bound by `A_(i+1)`.  Expanding that
alpha produces only candidates which the final bounds and triangles place
strictly above the failed bound, a contradiction.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- Lemma 4.2(i)'s fallback conclusion at every possible fallback index. -/
theorem leftFallback_bound_of_interior
    [alphaLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2 := by
  by_contra hboundFailure
  let nextNextIndex (h : j.val + 2 < n + 1) :
      RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, h, by omega⟩
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    b.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  have hnextPrimary := a.nextSourceAlpha_eq_primary_of_fallback_failure
    (sourceLaws := alphaLaws) (middleLaws := alphaLaws)
    (targetLaws := alphaLaws) b c habDefect hbcOrder j hi hessential
      htriggerFailure hboundFailure
  obtain ⟨hmiddleInterior, hmiddleSecondary⟩ :=
    a.middleTargetAlpha_eq_secondary_of_fallback_failure
      (targetLaws := alphaLaws) b c habDefect hbcDefect j hi hessential
        htriggerFailure hnextPrimary hboundFailure
  have hshiftMiddle :=
    a.shiftedMiddleAlpha_le_nextFallback_of_fallback
      (targetLaws := alphaLaws) b c hbcDefect j hi hessential
        htriggerFailure hnextPrimary hboundFailure
  have hstrictMiddle :
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          b.representationAlpha c j < a.representationAlpha c j :=
    hshiftMiddle.trans_lt (lt_of_not_ge hboundFailure)
  by_cases hnextNext : j.val + 2 < n + 1
  · let nextNext := nextNextIndex hnextNext
    have hlower :=
      a.shiftedNextNextSourceAlpha_le_shiftedMiddle_of_fallback
        (targetLaws := alphaLaws) b c hab habDefect hbcDefect j hi
          hnextNext hessential htriggerFailure hnextPrimary
          hmiddleSecondary hboundFailure
    have hstrict : (commonShift : WithTop ℚ) +
        a.representationAlpha b nextNext < a.representationAlpha c j :=
      hlower.trans_lt hstrictMiddle
    have hlowerFallback : (commonShift : WithTop ℚ) +
        a.representationAlpha b nextNext ≤ a.nextFallbackBound b j hi.2 :=
      hlower.trans hshiftMiddle
    have hhalfStrict :=
      a.targetAlpha_lt_shiftedNextNextHalfGap_of_fallback
        (targetLaws := alphaLaws) b c hab j hi hnextNext hessential
          htriggerFailure
    have hnotHalf : a.representationAlpha b nextNext ≠
        a.representationHalfGap b nextNext := by
      intro hhalf
      have hbelow : (commonShift : WithTop ℚ) +
          a.representationHalfGap b nextNext < a.representationAlpha c j := by
        simpa only [hhalf, commonShift, nextNext, nextNextIndex] using hstrict
      exact (not_lt_of_ge hhalfStrict.le) hbelow
    have hnormal := a.representationAlpha_eq_min_halfGap_prime b nextNext
    rcases min_choice (a.representationHalfGap b nextNext)
        (a.representationAlphaPrime b nextNext) with hhalf | hprime
    · exact False.elim (hnotHalf (hnormal.trans hhalf))
    · by_cases hinterior : 1 < nextNext.val ∧
          nextNext.val + 1 < n + 1
      · have hprimeNormal :=
          a.representationAlphaPrime_eq_min_primary_secondary
            b nextNext hinterior
        rcases min_choice (a.representationPrimaryDefect b nextNext)
            (a.representationSecondaryDefect b nextNext hinterior) with
          hprimary | hsecondary
        · have hnextNextPrimary : a.representationAlpha b nextNext =
              a.representationPrimaryDefect b nextNext :=
            hnormal.trans (hprime.trans (hprimeNormal.trans hprimary))
          have hreplace :=
            a.nextNextPrimaryDefect_eq_currentSourceDefect_of_fallback
              (sourceLaws := alphaLaws) (targetLaws := alphaLaws)
              b c j hi hnextNext hnextNextPrimary (by
                simpa only [commonShift, nextNext, nextNextIndex] using hstrict)
          have hreverse :=
            a.nextFallback_lt_shiftedNextNextPrimary_of_fallback
              b c habDefect j hi hnextNext hessential hnextNextPrimary hreplace
          exact (not_lt_of_ge hlowerFallback) (by
            simpa only [commonShift, nextNext, nextNextIndex] using hreverse)
        · have hnextNextSecondary : a.representationAlpha b nextNext =
              a.representationSecondaryDefect b nextNext hinterior :=
            hnormal.trans (hprime.trans (hprimeNormal.trans hsecondary))
          have hnextNextNext : j.val + 3 < n + 1 := by
            dsimp only [nextNext, nextNextIndex] at hinterior
            omega
          have hreplace :=
            a.nextNextSecondaryDefect_eq_previousSourceDefect_of_fallback
              (sourceLaws := alphaLaws) (targetLaws := alphaLaws)
              b c j hi hnextNext hnextNextNext hessential htriggerFailure
                (by
                  simpa only [nextNext, nextNextIndex] using hnextNextSecondary)
                (by simpa only [commonShift, nextNext, nextNextIndex] using hstrict)
          have hreverse :=
            a.nextFallback_lt_shiftedNextNextSecondary_of_fallback
              b c j hi hnextNext hnextNextNext hessential hnextPrimary
                (by
                  simpa only [nextNext, nextNextIndex] using hnextNextSecondary)
                hreplace
          exact (not_lt_of_ge hlowerFallback) (by
            simpa only [commonShift, nextNext, nextNextIndex] using hreverse)
      · have hendpoint :=
          a.representationAlphaPrime_eq_primary_of_not_interior
            b nextNext hinterior
        have hnextNextPrimary : a.representationAlpha b nextNext =
            a.representationPrimaryDefect b nextNext :=
          hnormal.trans (hprime.trans hendpoint)
        have hreplace :=
          a.nextNextPrimaryDefect_eq_currentSourceDefect_of_fallback
            (sourceLaws := alphaLaws) (targetLaws := alphaLaws)
            b c j hi hnextNext hnextNextPrimary (by
              simpa only [commonShift, nextNext, nextNextIndex] using hstrict)
        have hreverse :=
          a.nextFallback_lt_shiftedNextNextPrimary_of_fallback
            b c habDefect j hi hnextNext hessential hnextNextPrimary hreplace
        exact (not_lt_of_ge hlowerFallback) (by
          simpa only [commonShift, nextNext, nextNextIndex] using hreverse)
  · have hnextNext' :=
      a.nextNext_exists_of_fallback_failure
        (targetLaws := alphaLaws) b c hab hbcDefect j hi hessential
          htriggerFailure hnextPrimary hmiddleSecondary hboundFailure
    exact (hnextNext hnextNext').elim

end BONG.GoodBONG

end Bong
