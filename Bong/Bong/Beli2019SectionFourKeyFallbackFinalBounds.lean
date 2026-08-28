/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyFallbackSecondTriangle
import Bong.Bong.Beli2019AdjacentCappedDefect

/-!
# Beli (2019), Lemma 4.2: final fallback candidate bounds

The last part of the fallback proof expands `A_(i+1)`.  This file isolates
the common target lower bound and the estimates which delete its half-gap
candidate and compare its two defect candidates with adjacent source
defects.
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

/-- The common lower bound
`C_(i-1) <= R_i + R_(i+1) - T_(i-2) - T_(i-1) + alpha_(i+1)`
used three times in the final fallback paragraph. -/
theorem targetAlpha_le_nextSourceAlphaCore
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ +
        a.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        (a.alphaValue ⟨j.val + 1, by omega⟩ : WithTop ℚ) := by
  let sourceAlpha : Fin n := ⟨j.val + 1, by omega⟩
  have hcandidate := a.representationAlpha_le_secondary c j hi
  have hcap := a.truncatedPrefixDefect_le_leftCap c 1
    (j.val + 2) (j.val - 2)
  have hcap' : a.truncatedPrefixDefect c 1
      (j.val + 2) (j.val - 2) ≤
        (a.alphaValue sourceAlpha : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) hiNextNext] at hcap
    simpa only [sourceAlpha, show j.val + 2 - 1 = j.val + 1 by omega]
      using hcap
  unfold representationSecondaryDefect at hcandidate
  exact hcandidate.trans (by
    simpa only [sourceAlpha] using add_le_add_right hcap' _)

/-- The shifted half-gap candidate of `A_(i+1)` is strictly above
`C_(i-1)`. -/
theorem targetAlpha_lt_shiftedNextNextHalfGap_of_fallback
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    let nextNext : RepresentationIndex (n + 1) (n + 1) :=
      ⟨j.val + 2, by omega, hiNextNext, by omega⟩
    a.representationAlpha c j <
      (((a.order ⟨j.val, j.lt_large⟩ +
        b.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.representationHalfGap b nextNext := by
  let nextNext : RepresentationIndex (n + 1) (n + 1) :=
    ⟨j.val + 2, by omega, hiNextNext, by omega⟩
  have htargetHalf :=
    a.targetAlpha_le_previousTargetPairHalfBound c j hi.1
  have hsourceNext :=
    a.keyLemmaLeftFallback_sourceNext_le_middleNext
      b c hab j hi.1 hi.2 hessential htriggerFailure
  unfold IsNextEssential IsEssentialFor
    BeliOrderSequence.IsEssentialFor at hessential
  have hpairRaw := hessential.2 hi.1 hiNextNext
  have hpair :
      c.order ⟨j.val - 2, by omega⟩ +
          c.order ⟨j.val - 1, by omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ +
          a.order ⟨j.val + 2, hiNextNext⟩ := by
    simpa only [orderSequence_at, nextEssentialIndex] using hpairRaw
  dsimp only
  apply htargetHalf.trans_lt
  unfold representationHalfGap
  norm_cast
  simp only [nextNext, Rat.divInt_eq_div]
  push_cast
  have hsourceNextQ :
      (a.order ⟨j.val + 1, hi.2⟩ : ℚ) ≤
        (b.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
    exact_mod_cast hsourceNext
  have hpairQ :
      (c.order ⟨j.val - 2, by omega⟩ : ℚ) +
          (c.order ⟨j.val - 1, by omega⟩ : ℚ) <
        (a.order ⟨j.val + 1, hi.2⟩ : ℚ) +
          (a.order ⟨j.val + 2, hiNextNext⟩ : ℚ) := by
    exact_mod_cast hpair
  linarith

/-- The source adjacent defect at `(i+1,i+2)` gives a shifted upper
comparison for the primary candidate of `A_(i+1)`. -/
theorem targetAlpha_le_shiftedNextNextPrimaryAdjacent
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1) :
    a.representationAlpha c j ≤
      (((a.order ⟨j.val, j.lt_large⟩ +
        a.order ⟨j.val + 2, hiNextNext⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 1) (j.val + 3) := by
  let adjacent : Fin n := ⟨j.val + 1, by omega⟩
  let targetShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let adjacentShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  have htarget := a.targetAlpha_le_nextSourceAlphaCore
    (targetLaws := targetLaws) c j hi hiNextNext
  have hadjacent := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact a.order_sub_add_alpha_le_cappedAdjacent adjacent
  have hadjacentCast : adjacent.castSucc =
      (⟨j.val + 1, hi.2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hadjacentSucc : adjacent.succ =
      (⟨j.val + 2, hiNextNext⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  calc
    a.representationAlpha c j ≤
        (targetShift : WithTop ℚ) +
          (a.alphaValue adjacent : WithTop ℚ) := by
      simpa only [targetShift, adjacent] using htarget
    _ = (adjacentShift : WithTop ℚ) +
        (((((a.order adjacent.castSucc - a.order adjacent.succ : Int) : ℚ) +
          a.alphaValue adjacent : ℚ)) : WithTop ℚ) := by
      rw [hadjacentCast, hadjacentSucc]
      dsimp only [targetShift, adjacentShift, adjacent]
      norm_cast
      push_cast
      ring
    _ ≤ (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 1) (j.val + 3) := by
      simpa only [adjacent] using add_le_add_right hadjacent _

/-- At an interior following boundary, the source adjacent defect at
`(i+2,i+3)` gives a strict shifted upper comparison for the secondary
candidate of `A_(i+1)`. -/
theorem targetAlpha_lt_shiftedNextNextSecondaryAdjacent_of_fallback
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hiNextNext : j.val + 2 < n + 1)
    (hiNextNextNext : j.val + 3 < n + 1)
    (hessential : a.IsNextEssential c j)
    (htriggerFailure :
      ¬a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j <
      (((a.order ⟨j.val, j.lt_large⟩ +
        a.order ⟨j.val + 2, hiNextNext⟩ +
        a.order ⟨j.val + 3, hiNextNextNext⟩ -
        b.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 2, by omega⟩ -
        c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 2) (j.val + 4) := by
  let previousAlpha : Fin n := ⟨j.val + 1, by omega⟩
  let currentAlpha : Fin n := ⟨j.val + 2, by omega⟩
  let targetShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  let adjacentShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 2, hiNextNext⟩ +
    a.order ⟨j.val + 3, hiNextNextNext⟩ -
    b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by omega⟩ -
    c.order ⟨j.val - 1, by omega⟩ : Int) : ℚ)
  have htarget := a.targetAlpha_le_nextSourceAlphaCore
    (targetLaws := targetLaws) c j hi hiNextNext
  have hadjacent := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact a.order_sub_add_alpha_le_cappedAdjacent currentAlpha
  have hpreviousNext : previousAlpha.val + 1 < n := by
    dsimp only [previousAlpha]
    omega
  have hleft := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    exact (a.alpha_p1 previousAlpha hpreviousNext).1
  unfold alphaLeftEndpoint at hleft
  have hpreviousCast : previousAlpha.castSucc =
      (⟨j.val + 1, hi.2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hpreviousNextIndex :
      (⟨previousAlpha.val + 1, hpreviousNext⟩ : Fin n) = currentAlpha := by
    apply Fin.ext
    rfl
  have hcurrentCast : currentAlpha.castSucc =
      (⟨j.val + 2, hiNextNext⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hcurrentSucc : currentAlpha.succ =
      (⟨j.val + 3, hiNextNextNext⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hpreviousCast, hpreviousNextIndex, hcurrentCast] at hleft
  have hcross :=
    a.keyLemmaLeftFallback_middleCurrent_lt_sourceNextNext
      b c j hi.1 hi.2 hiNextNext hessential htriggerFailure
  have hstrictQ : targetShift + a.alphaValue previousAlpha <
      adjacentShift +
        (((a.order currentAlpha.castSucc - a.order currentAlpha.succ :
          Int) : ℚ) + a.alphaValue currentAlpha) := by
    dsimp only [targetShift, adjacentShift, previousAlpha, currentAlpha]
    rw [hcurrentCast, hcurrentSucc]
    push_cast
    have hcrossQ :
        (b.order ⟨j.val, j.lt_large⟩ : ℚ) <
          (a.order ⟨j.val + 2, hiNextNext⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  calc
    a.representationAlpha c j ≤
        (targetShift : WithTop ℚ) +
          (a.alphaValue previousAlpha : WithTop ℚ) := by
      simpa only [targetShift, previousAlpha] using htarget
    _ < (adjacentShift : WithTop ℚ) +
        (((((a.order currentAlpha.castSucc - a.order currentAlpha.succ :
          Int) : ℚ) + a.alphaValue currentAlpha : ℚ)) : WithTop ℚ) := by
      exact_mod_cast hstrictQ
    _ ≤ (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 2) (j.val + 4) := by
      simpa only [currentAlpha] using add_le_add_right hadjacent _

end BONG.GoodBONG

end Bong
