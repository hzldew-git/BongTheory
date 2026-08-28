/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyReducedCandidates

/-!
# Beli (2019), Lemma 4.2: excluding the secondary source candidate

This file completes lines 2171--2179 of the proof of Lemma 4.2(i).  The
primary form already obtained for the middle-to-target invariant gives a
strict defect triangle.  The resulting adjacent middle defect, together
with P1, contradicts the upper bound on the source invariant.
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

/-- In the secondary source branch, the source primary defect is strictly
larger than the primary defect occurring in `B_(i-1)`.  This is the strict
comparison on lines 2171--2174. -/
theorem middleTargetPrimaryDefect_lt_sourcePrimaryDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsourceEq : a.representationAlpha b j =
      a.representationSecondaryCurrentDefect b j hi)
    (hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j)
    (hlower :
      (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
        b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c j ≤
        a.representationSecondaryCurrentDefect b j hi) :
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) <
      a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) := by
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let commonShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let primaryShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)
  have htwoStep :
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ ≤
        b.order ⟨j.val, j.lt_large⟩ := by
    have h := b.orderSequence.twoStep (j.val - 2) (by omega)
    change b.order ⟨j.val - 2, by omega⟩ ≤
      b.order ⟨j.val - 2 + 2, by omega⟩ at h
    simpa only [Nat.sub_add_cancel (show 2 ≤ j.val by omega)] using h
  have hshiftLe : commonShift ≤ sourceShift + middleShift := by
    dsimp only [commonShift, sourceShift, middleShift]
    push_cast
    have htwoStepQ :
        (b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ : ℚ) ≤
          (b.order ⟨j.val, j.lt_large⟩ : ℚ) := by
      exact_mod_cast htwoStep
    linarith
  have hmiddleLower : (commonShift : WithTop ℚ) + middleDefect ≤
      a.representationAlpha b j := by
    calc
      (commonShift : WithTop ℚ) + middleDefect ≤
          ((sourceShift + middleShift : ℚ) : WithTop ℚ) + middleDefect :=
        add_le_add (WithTop.coe_le_coe.mpr hshiftLe) le_rfl
      _ = (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) := by
        simp only [WithTop.coe_add, add_assoc]
      _ = (sourceShift : WithTop ℚ) + b.representationAlpha c j := by
        rw [hmiddlePrimary]
        rfl
      _ ≤ a.representationSecondaryCurrentDefect b j hi := by
        simpa only [sourceShift] using hlower
      _ = a.representationAlpha b j := hsourceEq.symm
  have hprimaryUpper : a.representationAlpha b j ≤
      (primaryShift : WithTop ℚ) + sourceDefect := by
    simpa only [primaryShift, sourceDefect, representationPrimaryDefect] using
      a.representationAlpha_le_primary b j
  have hcross :
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hraw := hessential.1 (by
      simp only [nextEssentialIndex]
      omega) (by simpa only [nextEssentialIndex] using hi.2)
    simpa only [orderSequence_at, nextEssentialIndex] using hraw
  have hshiftLt : primaryShift < commonShift := by
    dsimp only [primaryShift, commonShift]
    push_cast
    have hcrossQ :
        (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
          (a.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
      exact_mod_cast hcross
    linarith
  have hmiddleNeTop : middleDefect ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hmiddleLower
    exact a.representationAlpha_ne_top b j (top_unique hmiddleLower)
  have hstrict :
      (primaryShift : WithTop ℚ) + middleDefect <
        (primaryShift : WithTop ℚ) + sourceDefect := by
    calc
      (primaryShift : WithTop ℚ) + middleDefect <
          (commonShift : WithTop ℚ) + middleDefect :=
        (WithTop.add_lt_add_iff_right hmiddleNeTop).mpr
          (WithTop.coe_lt_coe.mpr hshiftLt)
      _ ≤ a.representationAlpha b j := hmiddleLower
      _ ≤ (primaryShift : WithTop ℚ) + sourceDefect := hprimaryUpper
  exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hstrict

/-- The two strict triangles on lines 2170--2175 identify the middle-target
defect with the adjacent capped defect `d[-b_(i-1,i)]`. -/
theorem middleTargetPrimaryDefect_eq_middleAdjacentDefect
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hcurrent : b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1))
    (hstrict : b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) <
      a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)) :
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      b.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) := by
  have hstrict' :
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) <
        a.truncatedPrefixDefect b (1 * (-1)) (j.val + 1) (j.val - 1) := by
    simpa only [one_mul, ← hcurrent] using hstrict
  have htriangle := a.truncatedPrefixDefect_eq_middle_of_lt_composite
    b b 1 (-1) (by simp) (by simp) (j.val + 1) (j.val + 1)
      (j.val - 1) hstrict'
  calc
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
        a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1) := hcurrent
    _ = b.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1) := htriangle
    _ = b.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) :=
      b.truncatedPrefixDefect_comm b (-1) (j.val + 1) (j.val - 1)

/-- The secondary candidate for `A_(i-1)` cannot be the failing candidate.
This is the final contradiction on lines 2175--2179. -/
theorem sourceSecondaryCandidate_impossible_of_leftDirectFailure
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hsourceEq : a.representationAlpha b j =
      a.representationSecondaryCurrentDefect b j hi)
    (hmiddlePrimary : b.representationAlpha c j =
      b.representationPrimaryDefect c j)
    (hcurrent : b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1) =
      a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1))
    (hlower :
      (((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
        b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) + b.representationAlpha c j ≤
        a.representationSecondaryCurrentDefect b j hi) : False := by
  let previous : Fin n := ⟨j.val - 2, by omega⟩
  let middle : Fin n := ⟨j.val - 1, by omega⟩
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
      b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let middleShift : ℚ :=
    ((b.order ⟨j.val, j.lt_large⟩ -
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let capShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let adjacentLower : ℚ :=
    ((b.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) +
        b.alphaValue previous
  let middleDefect :=
    b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1)
  have hstrict := a.middleTargetPrimaryDefect_lt_sourcePrimaryDefect
    b c j hi hessential hsourceEq hmiddlePrimary hlower
  have hadjacentEq := a.middleTargetPrimaryDefect_eq_middleAdjacentDefect
    b c j hcurrent hstrict
  have hp1 := (b.alpha_p1 previous (by
    simp only [previous]
    omega)).1
  have hmono :
      (b.order ⟨j.val - 2, by omega⟩ : ℚ) + b.alphaValue previous ≤
        (b.order ⟨j.val - 1, by omega⟩ : ℚ) + b.alphaValue middle := by
    unfold alphaLeftEndpoint at hp1
    have hpreviousCast : previous.castSucc =
        (⟨j.val - 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hmiddleCast : middle.castSucc =
        (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hpreviousNext : previous.val + 1 < n := by
      change j.val - 2 + 1 < n
      omega
    have hnext : (⟨previous.val + 1, hpreviousNext⟩ : Fin n) = middle := by
      apply Fin.ext
      change j.val - 2 + 1 = j.val - 1
      omega
    rw [hpreviousCast, hnext, hmiddleCast] at hp1
    exact hp1
  have hadjacentRaw := b.order_sub_add_alpha_le_cappedAdjacent middle
  have hmiddleCast : middle.castSucc =
      (⟨j.val - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hmiddleSucc : middle.succ =
      (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [middle, Fin.val_succ]
    omega
  have hadjacent : (adjacentLower : WithTop ℚ) ≤ middleDefect := by
    have hlowerQ : adjacentLower ≤
        ((b.order ⟨j.val - 1, by omega⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) +
            b.alphaValue middle := by
      dsimp only [adjacentLower]
      push_cast
      linarith
    calc
      (adjacentLower : WithTop ℚ) ≤
          (((b.order ⟨j.val - 1, by omega⟩ -
            b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) +
              b.alphaValue middle : ℚ) := WithTop.coe_le_coe.mpr hlowerQ
      _ ≤ b.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1) := by
        simpa only [middle, hmiddleCast, hmiddleSucc,
          show j.val - 1 + 2 = j.val + 1 by omega] using hadjacentRaw
      _ = middleDefect := hadjacentEq.symm
  have hcap : a.representationAlpha b j ≤
      (capShift : WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) := by
    calc
      a.representationAlpha b j ≤ a.representationAlphaPrime b j :=
        a.representationAlpha_le_prime b j
      _ ≤ (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) + b.prefixAlphaCap (j.val - 1) :=
        a.representationAlphaPrime_le_primaryRightCap b j
      _ = (capShift : WithTop ℚ) +
          (b.alphaValue previous : WithTop ℚ) := by
        rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
        simp only [capShift, previous,
          show j.val - 1 - 1 = j.val - 2 by omega]
  have hcross :
      c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ <
        a.order ⟨j.val + 1, hi.2⟩ := by
    unfold IsNextEssential IsEssentialFor
      BeliOrderSequence.IsEssentialFor at hessential
    have hraw := hessential.1 (by
      simp only [nextEssentialIndex]
      omega) (by simpa only [nextEssentialIndex] using hi.2)
    simpa only [orderSequence_at, nextEssentialIndex] using hraw
  have hcapStrict :
      (capShift : WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) <
        (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) := by
    calc
      (capShift : WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) <
          (sourceShift : WithTop ℚ) +
            ((middleShift : WithTop ℚ) + (adjacentLower : WithTop ℚ)) := by
        norm_cast
        dsimp only [capShift, sourceShift, middleShift, adjacentLower]
        push_cast
        have hcrossQ :
            (c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : ℚ) <
              (a.order ⟨j.val + 1, hi.2⟩ : ℚ) := by
          exact_mod_cast hcross
        linarith
      _ ≤ (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) :=
        add_le_add le_rfl (add_le_add le_rfl hadjacent)
  have hcycle : a.representationAlpha b j <
      a.representationSecondaryCurrentDefect b j hi := by
    calc
      a.representationAlpha b j ≤
          (capShift : WithTop ℚ) + (b.alphaValue previous : WithTop ℚ) := hcap
      _ < (sourceShift : WithTop ℚ) +
          ((middleShift : WithTop ℚ) + middleDefect) := hcapStrict
      _ = (sourceShift : WithTop ℚ) + b.representationAlpha c j := by
        rw [hmiddlePrimary]
        rfl
      _ ≤ a.representationSecondaryCurrentDefect b j hi := by
        simpa only [sourceShift] using hlower
  exact (not_lt_of_ge hsourceEq.ge) hcycle

end BONG.GoodBONG

end Bong
