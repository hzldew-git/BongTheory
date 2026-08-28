/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackFirstTriangle
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 4.2: the middle fallback candidate

After the first fallback triangle, the paper expands `B_(i-1)`.  Its
half-gap candidate lies strictly above `C_(i-1)`, while its primary
candidate lies strictly above the desired fallback bound.  Consequently a
putative failure of that bound forces the remaining secondary candidate.
The endpoint distinction for the following source alpha is handled in the
next step; the middle alpha here is still at an interior boundary.
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

/-- The target half-gap estimate used to delete the half-gap candidate of
`B_(i-1)` in the fallback paragraph. -/
theorem targetAlpha_le_previousTargetPairHalfBound
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hiTwo : 1 < j.val) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
        (c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) / 2 -
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
  let targetPair : Fin n := ⟨j.val - 2, by have := j.lt_large; omega⟩
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  calc
    a.representationAlpha c j ≤ a.representationAlphaPrime c j :=
      a.representationAlpha_le_prime c j
    _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          (c.halfGapValue targetPair : WithTop ℚ) :=
      a.representationAlphaPrime_le_primaryRightHalfGap c j hiTwo
    _ = _ := by
      unfold halfGapValue orderGap
      rw [htargetCast, htargetSucc]
      norm_cast
      simp only [Rat.divInt_eq_div]
      push_cast
      ring

/-- Under failure of the fallback bound, `B_(i-1)` can only be its
secondary candidate. -/
theorem middleTargetAlpha_eq_secondary_of_fallback_failure
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnextPrimary : a.representationAlpha b
      (nextRepresentationIndex j hi.2) =
        a.representationPrimaryDefect b
          (nextRepresentationIndex j hi.2))
    (hboundFailure :
      ¬a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2) :
    ∃ hinterior : 1 < j.val ∧ j.val + 1 < n + 1,
      b.representationAlpha c j =
        b.representationSecondaryDefect c j hinterior := by
  let next := nextRepresentationIndex j hi.2
  let outerShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let fallbackShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let primaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let middleDefect := b.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  let targetDefect := a.truncatedPrefixDefect c (-1)
    (j.val + 1) (j.val - 1)
  have hshiftMiddle :=
    a.shiftedMiddleAlpha_le_nextFallback_of_fallback
      (targetLaws := targetLaws) b c hbcDefect j hi hessential
        htriggerFailure hnextPrimary hboundFailure
  have hstrictMiddle : (outerShift : WithTop ℚ) +
      b.representationAlpha c j < a.representationAlpha c j := by
    exact hshiftMiddle.trans_lt (lt_of_not_ge hboundFailure)
  have hhalfStrict : a.representationAlpha c j <
      (outerShift : WithTop ℚ) + b.representationHalfGap c j := by
    have htargetHalf := a.targetAlpha_le_previousTargetPairHalfBound c j hi.1
    apply htargetHalf.trans_lt
    unfold representationHalfGap
    dsimp only [outerShift]
    norm_cast
    simp only [Rat.divInt_eq_div]
    push_cast
    have horder :=
      a.keyLemmaLeftFallback_middleCurrent_lt_targetPreviousPrevious
        b c j hi.1 hi.2 hessential htriggerFailure
    have horderQ :
        (b.order ⟨j.val, j.lt_large⟩ : ℚ) <
          (c.order ⟨j.val - 2, by omega⟩ : ℚ) := by
      exact_mod_cast horder
    linarith
  have hnotHalf : b.representationAlpha c j ≠
      b.representationHalfGap c j := by
    intro hhalf
    have hbelow : (outerShift : WithTop ℚ) +
        b.representationHalfGap c j < a.representationAlpha c j := by
      simpa only [hhalf] using hstrictMiddle
    exact (not_lt_of_ge hhalfStrict.le) hbelow
  have hnotPrimary : b.representationAlpha c j ≠
      b.representationPrimaryDefect c j := by
    intro hprimary
    have htargetPrimary : a.representationAlpha c j ≤
        (primaryShift : WithTop ℚ) + targetDefect := by
      simpa only [primaryShift, targetDefect, representationPrimaryDefect]
        using a.representationAlpha_le_primary c j
    have hstrictShifted : (primaryShift : WithTop ℚ) + middleDefect <
        (primaryShift : WithTop ℚ) + targetDefect := by
      calc
        (primaryShift : WithTop ℚ) + middleDefect =
            (outerShift : WithTop ℚ) + b.representationAlpha c j := by
          rw [hprimary]
          unfold representationPrimaryDefect
          dsimp only [primaryShift, outerShift, middleDefect]
          rw [← add_assoc]
          congr 1
          norm_cast
          push_cast
          ring
        _ < a.representationAlpha c j := hstrictMiddle
        _ ≤ (primaryShift : WithTop ℚ) + targetDefect := htargetPrimary
    have hdefectStrict : middleDefect < targetDefect :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrictShifted
    have hdefectStrict' :
        c.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) <
          c.truncatedPrefixDefect a (-1) (j.val - 1) (j.val + 1) := by
      simpa only [middleDefect, targetDefect,
        c.truncatedPrefixDefect_comm b (-1) (j.val - 1) (j.val + 1),
        c.truncatedPrefixDefect_comm a (-1) (j.val - 1) (j.val + 1)]
        using hdefectStrict
    have htriangle := c.truncatedPrefixDefect_neg_eq_pos_of_lt_neg
      b a (j.val - 1) (j.val + 1) (j.val + 1) hdefectStrict'
    have hreplace : middleDefect =
        a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
      calc
        middleDefect = c.truncatedPrefixDefect b (-1)
            (j.val - 1) (j.val + 1) := by
          exact (c.truncatedPrefixDefect_comm b (-1)
            (j.val - 1) (j.val + 1)).symm
        _ = b.truncatedPrefixDefect a 1
            (j.val + 1) (j.val + 1) := htriangle
        _ = a.truncatedPrefixDefect b 1
            (j.val + 1) (j.val + 1) :=
          b.truncatedPrefixDefect_comm a 1 (j.val + 1) (j.val + 1)
    have hnextDefect : a.representationAlpha b next ≤
        a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := by
      have hcondition := habDefect next
      rw [a.coe_representationAlphaValue b next] at hcondition
      simpa only [next, nextRepresentationIndex] using hcondition
    have hshiftStrict : fallbackShift < primaryShift := by
      dsimp only [fallbackShift, primaryShift]
      push_cast
      have hessentialOrder :=
        a.keyLemmaLeftFallback_targetPrevious_lt_sourceNext
          c j hi.2 hessential
      have hessentialOrderQ :
          (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
            (a.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
        exact_mod_cast hessentialOrder
      linarith
    have hnextFinite : a.representationAlpha b next ≠ ⊤ :=
      a.representationAlpha_ne_top b next
    have hfallbackStrict : a.nextFallbackBound b j hi.2 <
        (outerShift : WithTop ℚ) + b.representationAlpha c j := by
      calc
        a.nextFallbackBound b j hi.2 =
            (fallbackShift : WithTop ℚ) + a.representationAlpha b next := by
          rfl
        _ < (primaryShift : WithTop ℚ) +
            a.representationAlpha b next :=
          WithTop.add_lt_add_right hnextFinite (by exact_mod_cast hshiftStrict)
        _ ≤ (primaryShift : WithTop ℚ) + middleDefect := by
          rw [hreplace]
          exact add_le_add le_rfl hnextDefect
        _ = (outerShift : WithTop ℚ) + b.representationAlpha c j := by
          rw [hprimary]
          unfold representationPrimaryDefect
          dsimp only [primaryShift, outerShift, middleDefect]
          rw [← add_assoc]
          congr 1
          norm_cast
          push_cast
          ring
    exact (not_lt_of_ge hshiftMiddle) hfallbackStrict
  have hnormal := b.representationAlpha_eq_min_halfGap_prime c j
  rcases min_choice (b.representationHalfGap c j)
      (b.representationAlphaPrime c j) with hhalf | hprime
  · exact False.elim (hnotHalf (hnormal.trans hhalf))
  · by_cases hinterior : 1 < j.val ∧ j.val + 1 < n + 1
    · have hprimeNormal :=
        b.representationAlphaPrime_eq_min_primary_secondary c j hinterior
      rcases min_choice (b.representationPrimaryDefect c j)
          (b.representationSecondaryDefect c j hinterior) with
        hprimary | hsecondary
      · exact False.elim
          (hnotPrimary (hnormal.trans (hprime.trans
            (hprimeNormal.trans hprimary))))
      · exact ⟨hinterior,
          hnormal.trans (hprime.trans (hprimeNormal.trans hsecondary))⟩
    · have hendpoint :=
        b.representationAlphaPrime_eq_primary_of_not_interior c j hinterior
      exact False.elim
        (hnotPrimary (hnormal.trans (hprime.trans hendpoint)))

end BONG.GoodBONG

end Bong
