/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackNormalForm
import Bong.Bong.Beli2019Lemma214Bounds

/-!
# Beli (2019), Lemma 4.2: candidate deletion in the left fallback branch

The first two estimates in the fallback paragraph show that the shifted
half-gap and source-alpha candidates are at least `C_(i-1)`.  Therefore a
failure of the desired fallback bound forces `A_i` to be its primary
defect candidate.
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

/-- The first displayed candidate in the fallback paragraph is at least
`C_(i-1)` after adding the outer shift `R_i - R_(i+1)`. -/
theorem targetAlpha_le_shifted_nextHalfGap_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationHalfGap b (nextRepresentationIndex j hi.2) := by
  let targetPair : Fin n := ⟨j.val - 2, by omega⟩
  have htargetCast : targetPair.castSucc =
      (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have htargetSucc : targetPair.succ =
      (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [targetPair, Fin.val_succ]
    omega
  have htarget : a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
        (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
        (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
        (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    calc
      a.representationAlpha c j ≤ a.representationAlphaPrime c j :=
        a.representationAlpha_le_prime c j
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          (c.halfGapValue targetPair : WithTop ℚ) :=
        a.representationAlphaPrime_le_primaryRightHalfGap c j hi.1
      _ = _ := by
        unfold halfGapValue orderGap
        rw [htargetCast, htargetSucc]
        norm_cast
        simp only [Rat.divInt_eq_div]
        push_cast
        ring
  have hweak :=
    a.keyLemmaLeftFallback_sourceNext_add_middleCurrent_le_targetPreviousPair
      b c j hi.1 hi.2 hfailure
  calc
    a.representationAlpha c j ≤
        (((a.order ⟨j.val, j.lt_large⟩ : ℚ) -
          (c.order ⟨j.val - 2, by omega⟩ : ℚ) / 2 -
          (c.order ⟨j.val - 1, by omega⟩ : ℚ) / 2 +
          (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := htarget
    _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationHalfGap b (nextRepresentationIndex j hi.2) := by
      unfold representationHalfGap
      norm_cast
      simp only [nextRepresentationIndex, Nat.add_sub_cancel,
        Rat.divInt_eq_div]
      push_cast
      have hweakQ :
          (a.order ⟨j.val + 1, hi.2⟩ : ℚ) +
              b.order ⟨j.val, j.lt_large⟩ ≤
            c.order ⟨j.val - 2, by omega⟩ +
              c.order ⟨j.val - 1, by omega⟩ := by
        exact_mod_cast hweak
      linarith

/-- At an interior following boundary, the third displayed candidate in
the fallback paragraph is also at least `C_(i-1)` after the outer shift. -/
theorem targetAlpha_le_shifted_nextSourceAlpha_of_fallback
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hfailure : ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hinterior :
      1 < (nextRepresentationIndex j hi.2).val ∧
        (nextRepresentationIndex j hi.2).val + 1 < n + 1) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ -
        a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationSecondarySourceAlpha b
          (nextRepresentationIndex j hi.2) hinterior := by
  let next := nextRepresentationIndex j hi.2
  let sourceAlpha : Fin n := ⟨j.val + 1, by
    dsimp only [next, nextRepresentationIndex] at hinterior
    omega⟩
  let targetShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      c.order ⟨j.val - 2, by omega⟩ -
      c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 1, by omega⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  have htarget : a.representationAlpha c j ≤
      (targetShift : WithTop ℚ) + (a.alphaValue sourceAlpha : WithTop ℚ) := by
    have hcandidate := a.representationAlpha_le_secondary c j hi
    have hcap := a.truncatedPrefixDefect_le_leftCap c 1
      (j.val + 2) (j.val - 2)
    have hcap' :
        a.truncatedPrefixDefect c 1 (j.val + 2) (j.val - 2) ≤
          (a.alphaValue sourceAlpha : WithTop ℚ) := by
      rw [a.prefixAlphaCap_of_internal (by omega) (by
        dsimp only [sourceAlpha, next, nextRepresentationIndex] at hinterior ⊢
        omega)] at hcap
      simpa only [sourceAlpha, show j.val + 2 - 1 = j.val + 1 by omega]
        using hcap
    unfold representationSecondaryDefect at hcandidate
    exact hcandidate.trans (by
      simpa only [targetShift] using add_le_add_right hcap' _)
  have hpair :=
    a.keyLemmaLeftFallback_middlePreviousPair_le_targetPreviousPair
      b c hbcOrder j hi.1 hi.2 hessential hfailure
  have hshift : targetShift ≤ sourceShift := by
    dsimp only [targetShift, sourceShift]
    norm_cast
    omega
  calc
    a.representationAlpha c j ≤
        (targetShift : WithTop ℚ) + (a.alphaValue sourceAlpha : WithTop ℚ) :=
      htarget
    _ ≤ (sourceShift : WithTop ℚ) +
        (a.alphaValue sourceAlpha : WithTop ℚ) :=
      add_le_add (by exact_mod_cast hshift) le_rfl
    _ = (((a.order ⟨j.val, j.lt_large⟩ -
          a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationSecondarySourceAlpha b next hinterior := by
      unfold representationSecondarySourceAlpha
      simp only [next, nextRepresentationIndex, Nat.add_sub_cancel,
        show j.val + 1 - 2 = j.val - 1 by omega]
      rw [← add_assoc]
      congr 1
      norm_cast
      dsimp only [sourceShift, sourceAlpha]
      push_cast
      ring

/-- After deleting the first and third candidates, failure of the desired
fallback bound forces `A_i` to equal its primary defect candidate. -/
theorem nextSourceAlpha_eq_primary_of_fallback_failure
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hboundFailure :
      ¬a.representationAlpha c j ≤ a.nextFallbackBound b j hi.2) :
    a.representationAlpha b (nextRepresentationIndex j hi.2) =
      a.representationPrimaryDefect b (nextRepresentationIndex j hi.2) := by
  have hhalf := a.targetAlpha_le_shifted_nextHalfGap_of_fallback
    (targetLaws := targetLaws) b c j hi htriggerFailure
  rcases a.nextSourceAlpha_fallback_candidates
      (sourceLaws := sourceLaws) (middleLaws := middleLaws)
      b c habDefect hbcOrder j hi hessential htriggerFailure with
    hhalf' | hprimary | ⟨hinterior, hsource⟩
  · apply False.elim
    apply hboundFailure
    unfold nextFallbackBound
    rw [hhalf']
    exact hhalf
  · exact hprimary
  · apply False.elim
    apply hboundFailure
    unfold nextFallbackBound
    rw [hsource]
    exact a.targetAlpha_le_shifted_nextSourceAlpha_of_fallback
      b c hbcOrder j hi hessential htriggerFailure hinterior

end BONG.GoodBONG

end Bong
