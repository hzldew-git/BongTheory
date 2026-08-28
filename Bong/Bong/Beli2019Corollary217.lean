/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Corollary 2.17

The revised v2 trigger (iii') makes the weaker form of Corollary 2.17
transparent: if either of the two capped mixed defects is already larger
than the central threshold, their sum is larger because the other defect is
nonnegative.  Lemma 2.16 then converts this defect trigger back to the
original alpha trigger used by condition (iii).
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Corollary 2.17 using the preceding mixed defect
`d[-a_(1,i)b_(1,i-2)]`. -/
theorem beli2019Corollary217_of_previousDefect
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hcross : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩)
    (hlarge :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        a.centralPreviousDefect b i) :
    a.centralAlphaTrigger b i := by
  apply (a.beli2019Lemma216 (sourceLaws := sourceLaws)
    (targetLaws := targetLaws) b hRank horder hdefect i).mpr
  refine ⟨hcross, ?_⟩
  have hnonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := sourceLaws) (alphaW := targetLaws) b (-1)
    (i.val + 1) (i.val - 1)
  change (0 : WithTop ℚ) ≤ a.centralCurrentDefect b i at hnonnegative
  exact hlarge.trans_le (le_add_of_nonneg_right hnonnegative)

/-- Corollary 2.17 using the following mixed defect
`d[-a_(1,i+1)b_(1,i-1)]`. -/
theorem beli2019Corollary217_of_currentDefect
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n ≤ m) (horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (hcross : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ < a.order ⟨i.val, i.lt_large⟩)
    (hlarge :
      (((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, i.lt_large⟩ : ℚ) : ℚ)) : WithTop ℚ) <
        a.centralCurrentDefect b i) :
    a.centralAlphaTrigger b i := by
  apply (a.beli2019Lemma216 (sourceLaws := sourceLaws)
    (targetLaws := targetLaws) b hRank horder hdefect i).mpr
  refine ⟨hcross, ?_⟩
  have hnonnegative := a.truncatedPrefixDefect_nonneg
    (alphaV := sourceLaws) (alphaW := targetLaws) b (-1)
    i.val (i.val - 2)
  change (0 : WithTop ℚ) ≤ a.centralPreviousDefect b i at hnonnegative
  exact hlarge.trans_le (le_add_of_nonneg_left hnonnegative)

end BONG.GoodBONG

end Bong
