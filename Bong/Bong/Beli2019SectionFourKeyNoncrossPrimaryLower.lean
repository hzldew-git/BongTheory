/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyNoncrossNextCandidates

/-!
# Beli (2019), Lemma 4.2: the first noncrossed primary lower bound

This file formalizes lines 2263--2266.  Capped-defect domination splits the
source primary defect through the adjacent middle pair.  Remark 1.1 and the
two source defect conditions then replace the resulting defects by
`B_(i-1)` and `A_i`.
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

/-- Lines 2263--2266, with all order shifts written explicitly. -/
theorem min_shifted_middle_next_le_sourcePrimary
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (habDefect : a.RepresentationDefectCondition b)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1) :
    min
        ((((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
          b.representationAlpha c j)
        ((((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          a.representationAlpha b (nextRepresentationIndex j hi.2)) ≤
      a.representationPrimaryDefect b j := by
  let previous : Fin n := ⟨j.val - 1, by omega⟩
  let sourceShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let currentShift : ℚ :=
    ((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let middleGap : ℚ :=
    ((b.order ⟨j.val - 1, by have := j.lt_large; omega⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  let adjacent :=
    b.truncatedPrefixDefect b (-1) (j.val - 1) (j.val + 1)
  let samePrefix :=
    a.truncatedPrefixDefect b 1 (j.val + 1) (j.val + 1)
  let sourceDefect :=
    a.truncatedPrefixDefect b (-1) (j.val + 1) (j.val - 1)
  have hdomination : min adjacent samePrefix ≤ sourceDefect := by
    have hdom := b.truncatedPrefixDefect_domination b a
      (-1) 1 (j.val - 1) (j.val + 1) (j.val + 1)
    simp only [mul_one] at hdom
    rw [b.truncatedPrefixDefect_comm a 1
      (j.val + 1) (j.val + 1),
      b.truncatedPrefixDefect_comm a (-1)
        (j.val - 1) (j.val + 1)] at hdom
    simpa only [adjacent, samePrefix, sourceDefect] using hdom
  have hmiddleAlpha := b.representationAlpha_le_leftAlpha c hbcDefect j
  have hadjacentRaw := b.order_sub_add_alpha_le_cappedAdjacent previous
  have hpreviousCast : previous.castSucc =
      (⟨j.val - 1, by have := j.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hpreviousSucc : previous.succ =
      (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [previous, Fin.val_succ]
    omega
  rw [hpreviousCast, hpreviousSucc] at hadjacentRaw
  have hadjacent : (middleGap : WithTop ℚ) +
      (b.alphaValue previous : WithTop ℚ) ≤ adjacent := by
    simpa only [middleGap, adjacent, previous, WithTop.coe_add,
      show j.val - 1 + 2 = j.val + 1 by omega] using hadjacentRaw
  have hshift : sourceShift + middleGap = currentShift := by
    dsimp only [sourceShift, middleGap, currentShift]
    push_cast
    ring
  have hmiddle : (currentShift : WithTop ℚ) +
      b.representationAlpha c j ≤
        (sourceShift : WithTop ℚ) + adjacent := by
    calc
      (currentShift : WithTop ℚ) + b.representationAlpha c j =
          ((sourceShift + middleGap : ℚ) : WithTop ℚ) +
            b.representationAlpha c j := by rw [hshift]
      _ = (sourceShift : WithTop ℚ) +
          ((middleGap : WithTop ℚ) + b.representationAlpha c j) := by
        norm_num [add_assoc]
      _ ≤ (sourceShift : WithTop ℚ) +
          ((middleGap : WithTop ℚ) +
            (b.alphaValue previous : WithTop ℚ)) := by
        gcongr
      _ ≤ (sourceShift : WithTop ℚ) + adjacent :=
        add_le_add_right hadjacent _
  have hnextDefect :
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        samePrefix := by
    have hcondition := habDefect (nextRepresentationIndex j hi.2)
    rw [a.coe_representationAlphaValue b
      (nextRepresentationIndex j hi.2)] at hcondition
    simpa only [nextRepresentationIndex, samePrefix] using hcondition
  have hnext : (sourceShift : WithTop ℚ) +
      a.representationAlpha b (nextRepresentationIndex j hi.2) ≤
        (sourceShift : WithTop ℚ) + samePrefix :=
    add_le_add_right hnextDefect _
  change min ((currentShift : WithTop ℚ) + b.representationAlpha c j)
      ((sourceShift : WithTop ℚ) +
        a.representationAlpha b (nextRepresentationIndex j hi.2)) ≤
    (sourceShift : WithTop ℚ) + sourceDefect
  calc
    min ((currentShift : WithTop ℚ) + b.representationAlpha c j)
        ((sourceShift : WithTop ℚ) +
          a.representationAlpha b (nextRepresentationIndex j hi.2)) ≤
      min ((sourceShift : WithTop ℚ) + adjacent)
        ((sourceShift : WithTop ℚ) + samePrefix) :=
      min_le_min hmiddle hnext
    _ = (sourceShift : WithTop ℚ) + min adjacent samePrefix := by
      rw [add_min]
    _ ≤ (sourceShift : WithTop ℚ) + sourceDefect :=
      add_le_add_right hdomination _

/-- Lines 2258--2261 in the shifted form used at line 2266.  The second
candidate is the reduced source-alpha term containing `beta_i`, as in the
paper's primed formula for `B_(i-1)`. -/
theorem shiftedMiddleAlpha_eq_min_primary_sourceAlpha_of_noncross
    [middleLaws : Beli2006AlphaLaws.{u, w} K]
    [targetLaws : Beli2006AlphaLaws.{u, z} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hbcOrder : b.RepresentationOrderCondition c le_rfl)
    (hbcDefect : b.RepresentationDefectCondition c)
    (j : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < j.val ∧ j.val + 1 < n + 1)
    (hessential : a.IsNextEssential c j)
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j))
    (hnoncross : b.order ⟨j.val, j.lt_large⟩ <
      c.order ⟨j.val - 2, by have := j.lt_large; omega⟩) :
    (((a.order ⟨j.val, j.lt_large⟩ -
      b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        b.representationAlpha c j =
      min
        ((((a.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          b.truncatedPrefixDefect c (-1) (j.val + 1) (j.val - 1))
        ((((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          (b.alphaValue ⟨j.val, by omega⟩ : WithTop ℚ)) := by
  have hpair := a.keyLemmaLeftDirect_middlePair_lt
    b c hab j hi.1 hi.2 hessential hdirect
  have hnormal := b.middleTargetAlpha_eq_min_primary_sourceAlpha_of_current_lt_previous
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    c hbcOrder hbcDefect j hi hpair hnoncross
  have hprimaryShift :
      (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        (((b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
      (((a.order ⟨j.val, j.lt_large⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) := by
    norm_cast
    push_cast
    ring
  have hsecondaryShift :
      (((a.order ⟨j.val, j.lt_large⟩ -
          b.order ⟨j.val, j.lt_large⟩ : Int) : ℚ) : WithTop ℚ) +
        (((2 * b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) =
      (((a.order ⟨j.val, j.lt_large⟩ +
          b.order ⟨j.val, j.lt_large⟩ -
          c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
          c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
            WithTop ℚ) := by
    norm_cast
    push_cast
    ring
  rw [hnormal, add_min]
  unfold representationPrimaryDefect representationSecondarySourceAlpha
  rw [← add_assoc, hprimaryShift, ← add_assoc, hsecondaryShift]

end BONG.GoodBONG

end Bong
