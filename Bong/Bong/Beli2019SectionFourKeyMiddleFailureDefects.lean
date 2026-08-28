/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourKeyMiddleFailurePrime

/-!
# Beli (2019), Lemma 4.2: defect identifications in the failure branch

This file formalizes lines 2335--2341.  Condition 2.1(ii) for the
source--middle and middle--target pairs makes two positive prefix defects
strictly larger than the next source defect.  The strict capped-defect
triangle then identifies that defect first with the adjacent source defect
and then with the source--target prefix defect.
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

/-- Lines 2335--2341: under failure of the desired middle bound, the next
source defect is both the adjacent source defect and the corresponding
source--target defect. -/
theorem nextSourceDefect_eq_self_and_target_of_middleTarget_failure
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
    (hsourceBound : a.representationAlpha c j ≤
      a.representationAlpha b j)
    (hfailure : ¬a.representationAlpha c j ≤
      b.representationAlpha c j) :
    a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
        a.truncatedPrefixDefect a (-1) (j.val + 2) j.val ∧
      a.truncatedPrefixDefect b (-1) (j.val + 2) j.val =
        a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := by
  let sourceDefect := a.truncatedPrefixDefect b (-1) (j.val + 2) j.val
  have hshifted := a.shiftedNextSourcePrime_eq_nextSourceDefect_of_failure
    (sourceLaws := sourceLaws) (middleLaws := middleLaws)
    (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect
      hsourceBound hfailure
  have hsmall := a.shiftedNextSourcePrime_lt_middleTargetAlpha_of_failure
    (middleLaws := middleLaws) (targetLaws := targetLaws)
    b c hab habDefect hbcOrder hbcDefect j hi hessential hdirect hfailure
  have hdefectMiddle : sourceDefect < b.representationAlpha c j := by
    simpa only [sourceDefect, hshifted] using hsmall
  have hmiddleTarget : b.representationAlpha c j <
      a.representationAlpha c j := lt_of_not_ge hfailure
  have habPositive : a.representationAlpha b j ≤
      a.truncatedPrefixDefect b 1 j.val j.val := by
    simpa only [← a.coe_representationAlphaValue b j] using habDefect j
  have hstrictSource : sourceDefect <
      a.truncatedPrefixDefect b 1 j.val j.val :=
    hdefectMiddle.trans
      (hmiddleTarget.trans_le (hsourceBound.trans habPositive))
  have hstrictSource' :
      b.truncatedPrefixDefect a (-1) j.val (j.val + 2) <
        b.truncatedPrefixDefect a 1 j.val j.val := by
    simpa only [sourceDefect,
      a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val,
      a.truncatedPrefixDefect_comm b 1 j.val j.val] using hstrictSource
  have hselfTriangle := b.truncatedPrefixDefect_neg_eq_neg_of_lt_pos
    a a j.val (j.val + 2) j.val hstrictSource'
  have hself : sourceDefect =
      a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := by
    calc
      sourceDefect = b.truncatedPrefixDefect a (-1) j.val (j.val + 2) := by
        exact a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val
      _ = a.truncatedPrefixDefect a (-1) (j.val + 2) j.val := hselfTriangle
  have hbcPositive : b.representationAlpha c j ≤
      b.truncatedPrefixDefect c 1 j.val j.val := by
    simpa only [← b.coe_representationAlphaValue c j] using hbcDefect j
  have hstrictTarget : sourceDefect <
      b.truncatedPrefixDefect c 1 j.val j.val :=
    hdefectMiddle.trans_le hbcPositive
  have hstrictTarget' :
      b.truncatedPrefixDefect a (-1) j.val (j.val + 2) <
        b.truncatedPrefixDefect c 1 j.val j.val := by
    rw [← a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val]
    exact hstrictTarget
  have htargetTriangle := b.truncatedPrefixDefect_neg_eq_neg_of_lt_pos
    a c j.val (j.val + 2) j.val hstrictTarget'
  have htarget : sourceDefect =
      a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := by
    calc
      sourceDefect = b.truncatedPrefixDefect a (-1) j.val (j.val + 2) := by
        exact a.truncatedPrefixDefect_comm b (-1) (j.val + 2) j.val
      _ = a.truncatedPrefixDefect c (-1) (j.val + 2) j.val := htargetTriangle
  exact ⟨hself, htarget⟩

end BONG.GoodBONG

end Bong
