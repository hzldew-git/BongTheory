/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackCandidates
import Bong.Bong.Beli2019SectionFourKeyNoncrossComplete

/-!
# Beli (2019), Lemma 4.2: first fallback defect triangle

Once `A_i` is its primary candidate, failure of the fallback bound gives a
strict comparison of two negative capped defects.  The strict triangle
identifies the source-to-middle defect with the middle-to-target comparison
defect, hence condition 2.1(ii) supplies the shifted `B_(i-1)` lower bound.
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

/-- The first strict triangle in the fallback paragraph. -/
theorem nextSourcePrimaryDefect_eq_middleTargetCurrentDefect_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
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
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
      b.truncatedPrefixDefect c 1 j.val j.val := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by omega⟩ -
      c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let targetDefect := a.truncatedPrefixDefect c (-1) (j.val + 2) j.val
  have hsource : a.nextFallbackBound b j hi.2 =
      (sourceShift : WithTop ℚ) + sourceDefect := by
    unfold nextFallbackBound
    rw [hnextPrimary]
    unfold representationPrimaryDefect
    simp only [nextRepresentationIndex, Nat.add_sub_cancel,
      sourceShift, sourceDefect]
    rw [show j.val + 1 + 1 = j.val + 2 by omega]
    rw [← add_assoc]
    congr 1
    norm_cast
    push_cast
    ring
  have htarget : a.representationAlpha c j ≤
      (targetShift : WithTop ℚ) + targetDefect := by
    simpa only [targetShift, targetDefect,
      representationSecondaryCurrentDefect] using
        a.middleTargetAlpha_le_secondaryCurrent_of_nextEssential
          (targetLaws := targetLaws) c j hi hessential
  have hweak :=
    a.keyLemmaLeftFallback_sourceNext_add_middleCurrent_le_targetPreviousPair
      b c j hi.1 hi.2 htriggerFailure
  have hshift : targetShift ≤ sourceShift := by
    dsimp only [targetShift, sourceShift]
    norm_cast
    omega
  have hdefect : sourceDefect < targetDefect := by
    have hstrict : (sourceShift : WithTop ℚ) + sourceDefect <
        (targetShift : WithTop ℚ) + targetDefect := by
      rw [← hsource]
      exact (lt_of_not_ge hboundFailure).trans_le htarget
    have hstrict' : (sourceShift : WithTop ℚ) + sourceDefect <
        (sourceShift : WithTop ℚ) + targetDefect :=
      hstrict.trans_le (add_le_add (by exact_mod_cast hshift) le_rfl)
    exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrict'
  exact a.truncatedPrefixDefect_neg_eq_pos_of_lt_neg b c
    (j.val + 2) j.val j.val (by
      simpa only [sourceDefect, targetDefect] using hdefect)

/-- The first triangle and condition 2.1(ii) give the paper's inequality
`R_i - S_i + B_(i-1) <= R_i - R_(i+1) + A_i`. -/
theorem shiftedMiddleAlpha_le_nextFallback_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
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
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j ≤ a.nextFallbackBound b j hi.2 := by
  have htriangle :=
    a.nextSourcePrimaryDefect_eq_middleTargetCurrentDefect_of_fallback
      (targetLaws := targetLaws) b c j hi hessential htriggerFailure
        hnextPrimary hboundFailure
  have hmiddle : b.representationAlpha c j ≤
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val := by
    have h := hbcDefect j
    rw [b.coe_representationAlphaValue c j] at h
    rw [htriangle]
    exact h
  unfold nextFallbackBound
  rw [hnextPrimary]
  unfold representationPrimaryDefect
  simp only [nextRepresentationIndex, Nat.add_sub_cancel]
  rw [show j.val + 1 + 1 = j.val + 2 by omega]
  calc
    (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) (j.val + 2) j.val :=
      add_le_add_right hmiddle _
    _ = (((a.order ⟨j.val, j.lt_large⟩ -
          a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        ((((a.order ⟨j.val + 1, hi.2⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) (j.val + 2) j.val) := by
      rw [← add_assoc]
      congr 1
      norm_cast
      push_cast
      ring

end BONG.GoodBONG

end Bong
