/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackMiddleCandidates
import Bong.Bong.Beli2019FullRankDefect

/-!
# Beli (2019), Lemma 4.2: second fallback defect triangle

The secondary formula for `B_(i-1)` compares a middle-to-target positive
defect with the corresponding source-to-target defect.  Failure of the
fallback bound makes that comparison strict, so the strict triangle replaces
the former by the source-to-middle defect.  At the last possible fallback
index this is a full-rank defect and hence infinite, which is impossible;
otherwise condition 2.1(ii) supplies the lower bound by `A_(i+1)`.
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

/-- The second strict triangle in the fallback paragraph. -/
theorem middleTargetSecondaryDefect_eq_nextSourceDefect_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
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
    (hmiddleSecondary : b.representationAlpha c j =
      b.representationSecondaryDefect c j hi)
    (hboundFailure :
      ¬a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2) :
    b.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2) =
      a.truncatedPrefixDefect b 1 (j.val + 2) (j.val + 2) := by
  let outerShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let commonShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    b.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let targetShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let middleDefect := b.truncatedPrefixDefect c 1
    (j.val + 2) (j.val - 2)
  let targetDefect := a.truncatedPrefixDefect c 1
    (j.val + 2) (j.val - 2)
  have hshiftMiddle :=
    a.shiftedMiddleAlpha_le_nextFallback_of_fallback
      (targetLaws := targetLaws) b c hbcDefect j hi hessential
        htriggerFailure hnextPrimary hboundFailure
  have hstrictMiddle : (outerShift : WithTop ℚ) +
      b.representationAlpha c j < a.representationAlpha c j :=
    hshiftMiddle.trans_lt (lt_of_not_ge hboundFailure)
  have hmiddleExpanded : (outerShift : WithTop ℚ) +
      b.representationAlpha c j =
        (commonShift : WithTop ℚ) + middleDefect := by
    rw [hmiddleSecondary]
    unfold representationSecondaryDefect
    dsimp only [outerShift, commonShift, middleDefect]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have hsourceNext :=
    a.keyLemmaLeftFallback_sourceNext_le_middleNext
      b c hab j hi.1 hi.2 hessential htriggerFailure
  have hshift : targetShift ≤ commonShift := by
    dsimp only [targetShift, commonShift]
    norm_cast
    omega
  have htarget : a.representationAlpha c j ≤
      (commonShift : WithTop ℚ) + targetDefect := by
    have hraw := a.representationAlpha_le_secondary c j hi
    have hraw' : a.representationAlpha c j ≤
        (targetShift : WithTop ℚ) + targetDefect := by
      simpa only [targetShift, targetDefect, representationSecondaryDefect]
        using hraw
    exact hraw'.trans (add_le_add (by exact_mod_cast hshift) le_rfl)
  have hdefect : middleDefect < targetDefect := by
    have hstrict : (commonShift : WithTop ℚ) + middleDefect <
        (commonShift : WithTop ℚ) + targetDefect := by
      rw [← hmiddleExpanded]
      exact hstrictMiddle.trans_le htarget
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrict
  have hdefect' :
      c.truncatedPrefixDefect b 1 (j.val - 2) (j.val + 2) <
        c.truncatedPrefixDefect a 1 (j.val - 2) (j.val + 2) := by
    simpa only [middleDefect, targetDefect,
      c.truncatedPrefixDefect_comm b 1 (j.val - 2) (j.val + 2),
      c.truncatedPrefixDefect_comm a 1 (j.val - 2) (j.val + 2)]
      using hdefect
  have htriangle := c.truncatedPrefixDefect_eq_middle_of_lt_composite
    b a 1 1 (by simp) (by simp) (j.val - 2) (j.val + 2)
      (j.val + 2) (by simpa only [one_mul] using hdefect')
  calc
    b.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2) =
        c.truncatedPrefixDefect b 1 (j.val - 2) (j.val + 2) :=
      (c.truncatedPrefixDefect_comm b 1
        (j.val - 2) (j.val + 2)).symm
    _ = b.truncatedPrefixDefect a 1 (j.val + 2) (j.val + 2) :=
      htriangle
    _ = a.truncatedPrefixDefect b 1 (j.val + 2) (j.val + 2) :=
      b.truncatedPrefixDefect_comm a 1 (j.val + 2) (j.val + 2)

/-- At a common-space endpoint, failure would make the secondary middle
candidate contain the infinite full-rank source-to-middle defect. -/
theorem nextNext_exists_of_fallback_failure
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    {L' M' N' : Lattice K V}
    (a : GoodBONG q L' (n + 1))
    (b : GoodBONG q M' (n + 1))
    (c : GoodBONG q N' (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
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
    (hmiddleSecondary : b.representationAlpha c j =
      b.representationSecondaryDefect c j hi)
    (hboundFailure :
      ¬a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2) :
    j.val + 2 < n + 1 := by
  by_contra hnot
  have hlast : j.val + 2 = n + 1 := by omega
  have hreplace :=
    a.middleTargetSecondaryDefect_eq_nextSourceDefect_of_fallback
      (targetLaws := targetLaws) b c hab hbcDefect j hi hessential
        htriggerFailure hnextPrimary hmiddleSecondary hboundFailure
  have hsourceTop : a.truncatedPrefixDefect b 1
      (j.val + 2) (j.val + 2) = ⊤ := by
    rw [hlast]
    exact a.truncatedPrefixDefect_full_eq_top b
  have hmiddleTop : b.truncatedPrefixDefect c 1
      (j.val + 2) (j.val - 2) = ⊤ := hreplace.trans hsourceTop
  have halphaTop : b.representationAlpha c j = ⊤ := by
    rw [hmiddleSecondary]
    unfold representationSecondaryDefect
    rw [hmiddleTop]
    simp
  exact b.representationAlpha_ne_top c j halphaTop

/-- The second triangle and condition 2.1(ii) give the paper's lower bound
by the following source alpha `A_(i+1)`. -/
theorem shiftedNextNextSourceAlpha_le_shiftedMiddle_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (habDefect : a.RepresentationDefectCondition b)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnextPrimary : a.representationAlpha b
      (nextRepresentationIndex j hi.2) =
        a.representationPrimaryDefect b
          (nextRepresentationIndex j hi.2))
    (hmiddleSecondary : b.representationAlpha c j =
      b.representationSecondaryDefect c j hi)
    (hboundFailure :
      ¬a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2) :
    let nextNext : RepresentationIndex (n + 1) (n + 1) :=
      ⟨j.val + 2, by omega, hiNextNext, by omega⟩
    (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationAlpha b nextNext ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j := by
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  have hreplace :=
    a.middleTargetSecondaryDefect_eq_nextSourceDefect_of_fallback
      (targetLaws := targetLaws) b c hab hbcDefect j hi hessential
        htriggerFailure hnextPrimary hmiddleSecondary hboundFailure
  have hnextDefect : a.representationAlpha b nextNext ≤
      a.truncatedPrefixDefect b 1 (j.val + 2) (j.val + 2) := by
    have hcondition := habDefect nextNext
    rw [a.coe_representationAlphaValue b nextNext] at hcondition
    simpa only [nextNext] using hcondition
  dsimp only
  calc
    (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.representationAlpha b nextNext ≤
        (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b 1 (j.val + 2) (j.val + 2) :=
      add_le_add_right hnextDefect _
    _ = (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val + 1, hi.2⟩ -
          c.order ⟨j.val - 2, by omega⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          b.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2) := by
      rw [hreplace]
    _ = (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          b.representationAlpha c j := by
      rw [hmiddleSecondary]
      unfold representationSecondaryDefect
      rw [← add_assoc]
      congr 1
      norm_cast
      push_cast
      ring

end BONG.GoodBONG

end Bong
