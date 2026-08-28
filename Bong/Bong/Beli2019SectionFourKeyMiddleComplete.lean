/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleFailureDefects

/-!
# Beli (2019), Lemma 4.2: completion of the second direct bound

This file completes lines 2341--2348.  The two defect identifications from
the failure branch make both terms in the lower minimum at least the target
invariant.  This contradicts the assumed strict failure and proves the
second conclusion of Lemma 4.2(i) at an interior essential index.
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

/-- Lemma 4.2(i), second inequality, in the interior direct branch. -/
theorem leftDirect_middleBound_of_interior
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
    (hdirect : a.KeyLemmaLeftDirectTrigger b c (nextEssentialIndex j)) :
    a.representationAlpha c j ≤ b.representationAlpha c j := by
  have hsourceBound := a.leftDirect_sourceBound_of_interior
    (sourceLaws := sourceLaws) (middleLaws := middleLaws)
    (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
  by_contra hfailure
  let next := nextRepresentationIndex j hi.2
  let base : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    a.order ⟨j.val + 1, hi.2⟩ : Int) : ℚ)
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  let firstShift : ℚ := ((b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let secondShift : ℚ := ((2 * b.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let firstDefectShift : ℚ := ((a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let secondDefectShift : ℚ := ((b.order ⟨j.val, j.lt_large⟩ +
    a.order ⟨j.val + 1, hi.2⟩ -
    c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  have hprime := a.nextSourceAlpha_eq_prime_of_middleTarget_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hshifted := a.shiftedNextSourcePrime_eq_nextSourceDefect_of_failure
    (sourceLaws := sourceLaws) (middleLaws := middleLaws)
    (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
      hsourceBound hfailure
  have hshifted' : (base : WithTop ℚ) +
      a.representationAlphaPrime b next = sourceDefect := by
    simpa only [base, next, sourceDefect] using hshifted
  have hdefects :=
    a.nextSourceDefect_eq_self_and_target_of_middleTarget_failure
      (sourceLaws := sourceLaws) (middleLaws := middleLaws)
      (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
        hsourceBound hfailure
  have hfirstIdentity :
      (firstShift : WithTop ℚ) + a.representationAlpha b next =
        (firstDefectShift : WithTop ℚ) + sourceDefect := by
    rw [hprime, ← hshifted']
    rw [← add_assoc, ← WithTop.coe_add]
    congr 1
    norm_cast
    dsimp only [firstShift, firstDefectShift, base]
    push_cast
    simp only [Nat.add_comm j.val 1]
    ring_nf
  have hsecondIdentity :
      (secondShift : WithTop ℚ) + a.representationAlpha b next =
        (secondDefectShift : WithTop ℚ) + sourceDefect := by
    rw [hprime, ← hshifted']
    rw [← add_assoc, ← WithTop.coe_add]
    congr 1
    norm_cast
    dsimp only [secondShift, secondDefectShift, base]
    push_cast
    simp only [Nat.add_comm j.val 1]
    ring_nf
  let p : Fin n := ⟨j.val, by omega⟩
  let primaryShift : ℚ := ((a.order ⟨j.val, j.lt_large⟩ -
    c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ)
  let adjacentShift : ℚ := ((a.order ⟨j.val + 1, hi.2⟩ -
    a.order ⟨j.val, j.lt_large⟩ : Int) : ℚ)
  have hprimaryCap : a.representationAlpha c j ≤
      (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) := by
    have hraw := (a.representationAlpha_le_prime c j).trans
      (a.representationAlphaPrime_le_primaryLeftCap c j)
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hraw
    simpa only [primaryShift, p, Nat.add_sub_cancel] using hraw
  have hadjacent : (a.alphaValue p : WithTop ℚ) ≤
      (adjacentShift : WithTop ℚ) +
        a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := by
    letI : Beli2006AlphaLaws K := sourceLaws
    have hraw := a.alpha_le_orderGap_add_cappedAdjacent p
    rw [a.truncatedPrefixDefect_comm a (-1) p.val (p.val + 2)] at hraw
    have hpCast : p.castSucc =
        (⟨j.val, j.lt_large⟩ : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    have hpSucc : p.succ =
        (⟨j.val + 1, hi.2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [p, Fin.val_succ]
    rw [hpCast, hpSucc] at hraw
    simpa only [p, adjacentShift] using hraw
  have hprimaryAdjacent :
      (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) ≤
        (primaryShift : WithTop ℚ) +
          ((adjacentShift : WithTop ℚ) +
            a.truncatedPrefixDefect a (-1) (j.val + 2) j.val) :=
    add_le_add le_rfl hadjacent
  have hfirstLower : a.representationAlpha c j ≤
      (firstShift : WithTop ℚ) + a.representationAlpha b next := by
    calc
      a.representationAlpha c j ≤
          (primaryShift : WithTop ℚ) + (a.alphaValue p : WithTop ℚ) :=
        hprimaryCap
      _ ≤ (primaryShift : WithTop ℚ) +
          ((adjacentShift : WithTop ℚ) +
            a.truncatedPrefixDefect a (-1) (j.val + 2) j.val) :=
        hprimaryAdjacent
      _ = (firstDefectShift : WithTop ℚ) + sourceDefect := by
        dsimp only [sourceDefect]
        rw [← add_assoc, hdefects.1]
        congr 1
        norm_cast
        dsimp only [primaryShift, adjacentShift, firstDefectShift]
        push_cast
        ring
      _ = (firstShift : WithTop ℚ) + a.representationAlpha b next :=
        hfirstIdentity.symm
  have hcurrent := a.keyLemmaLeftDirect_sourceCurrent_le_middleCurrent
    b c hab hbcOrder j hi.1 hi.2 hessential hdirect
  have hsecondShift :
      (((a.order ⟨j.val, j.lt_large⟩ +
        a.order ⟨j.val + 1, hi.2⟩ -
        c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
        c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ : Int) : ℚ) :
          WithTop ℚ) ≤ (secondDefectShift : WithTop ℚ) := by
    have hsecondShiftInt :
        a.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
            c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ ≤
          b.order ⟨j.val, j.lt_large⟩ + a.order ⟨j.val + 1, hi.2⟩ -
            c.order ⟨j.val - 2, by have := j.lt_large; omega⟩ -
            c.order ⟨j.val - 1, by have := j.lt_large; omega⟩ := by
      omega
    dsimp only [secondDefectShift]
    exact_mod_cast hsecondShiftInt
  have hsecondary :=
    a.middleTargetAlpha_le_secondaryCurrent_of_nextEssential c j hi hessential
  have hsecondLower : a.representationAlpha c j ≤
      (secondShift : WithTop ℚ) + a.representationAlpha b next := by
    calc
      a.representationAlpha c j ≤
          a.representationSecondaryCurrentDefect c j hi := hsecondary
      _ ≤ (secondDefectShift : WithTop ℚ) +
          a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := by
        unfold representationSecondaryCurrentDefect
        exact add_le_add hsecondShift le_rfl
      _ = (secondDefectShift : WithTop ℚ) + sourceDefect := by
        dsimp only [sourceDefect]
        rw [hdefects.2]
      _ = (secondShift : WithTop ℚ) + a.representationAlpha b next :=
        hsecondIdentity.symm
  have hlowerRaw :=
    a.min_shifted_nextSourceAlpha_le_middleTargetAlpha_of_leftDirect_failure
      (middleLaws := middleLaws) (targetLaws := targetLaws)
      b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hlower :
      min ((firstShift : WithTop ℚ) + a.representationAlpha b next)
          ((secondShift : WithTop ℚ) + a.representationAlpha b next) ≤
        b.representationAlpha c j := by
    simpa only [firstShift, secondShift, next] using hlowerRaw
  have htargetMin : a.representationAlpha c j ≤
      min ((firstShift : WithTop ℚ) + a.representationAlpha b next)
        ((secondShift : WithTop ℚ) + a.representationAlpha b next) :=
    le_min hfirstLower hsecondLower
  exact hfailure (htargetMin.trans hlower)

end BONG.GoodBONG

end Bong
