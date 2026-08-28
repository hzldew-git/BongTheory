/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyCross

/-!
# Beli (2019), Lemma 4.2: the crossed left-direct bound

This file composes the candidate calculations from lines 2181--2249.  In the
branch `T_(i-2) ≤ S_i`, a strict failure of `C_(i-1) ≤ A_(i-1)` forces the
source primary candidate, and the two shifted comparisons then contradict one
another.
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

/-- Lemma 4.2(i), first inequality, in the crossed interior subcase. -/
theorem leftDirect_sourceBound_of_cross
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
    (hcross : c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
      b.order ⟨j.val, j.lt_large⟩) :
    a.representationAlpha c j ≤ a.representationAlpha b j := by
  by_contra hfailure
  obtain ⟨hsource, hprimary⟩ := a.leftDirect_sourceFailure_eq_primary
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hcommon :=
    a.shiftedNextSourceAlpha_le_shift_previousMiddle_of_cross_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hcross hprimary
  have hnextPrimary := a.nextSourceAlpha_eq_primary_of_commonBound
    (sourceLaws := sourceLaws) (targetLaws := targetLaws)
    b c hab hbcOrder hbcDefect j hi hessential hdirect hcross
      hsource hprimary hcommon
  have hpreviousLower := a.shift_previousMiddleAlpha_le_sourcePrimary
    b c hbcOrder hbcDefect j hi.1 hcross hprimary
  have hstrict :
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2) <
          a.representationAlpha c j :=
    hcommon.trans_lt (hpreviousLower.trans_lt hprimary)
  have hdefect := a.nextSourcePrimaryDefect_eq_previousMiddleDefect
    b c j hi hnextPrimary hstrict
  have hreverse := a.shift_previousMiddleAlpha_lt_shiftedNextSourcePrimary
    b c j hi hessential hdefect
  exact a.leftDirect_sourceBound_of_cross_of_certificates
    b c j hi hcommon hnextPrimary hreverse

end BONG.GoodBONG

end Bong
