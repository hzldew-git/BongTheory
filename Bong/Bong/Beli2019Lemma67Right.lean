/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Seed

/-!
# Beli (2019), Lemma 6.7: the right end of the type-II interval

After the middle interval is constant, Lemma 6.5 at its last prefix gives
`S - 1 ≤ R + 1`.  If the inequality were strict, the final source and
target gaps would both be nonpositive but would have opposite parity.
Lemma 6.6 excludes this, proving `S - R = 2`.
-/

namespace Bong

open Dyadic

universe u v w

theorem nat_sub_one_sub_one (k : Nat) : (k - 1) - 1 = k - 2 := by
  omega

theorem nat_sub_one_sub_two (k : Nat) : (k - 1) - 2 = k - 3 := by
  omega

theorem nat_sub_one_add_one_of_pos {k : Nat} (hk : 0 < k) :
    (k - 1) + 1 = k := by
  omega

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The identity `S - 1 = R + 1`, equivalent to `S - R = 2`, at the
right end of the long type-II interval. -/
theorem rightBoundarySource_eq_leftTarget
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hnoTwo : ∀ k, k < n + 1 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hlong : O.transition.lastZero + 2 <
      O.transition.firstTwo) :
    a.orderSequence.entryOrZero
        (O.transition.firstTwo - 1) =
      b.orderSequence.entryOrZero O.transition.lastZero := by
  have hfirstBound := O.transition.firstTwo_le_rank
  have hfirstPositive : 0 < O.transition.firstTwo := by omega
  have hrightBound : O.transition.firstTwo - 1 < n + 1 := by
    omega
  have hpreviousBound : O.transition.firstTwo - 2 < n + 1 := by
    omega
  have hpreviousTwoBound :
      O.transition.firstTwo - 3 < n + 1 := by
    omega
  have hgapBound : O.transition.firstTwo - 2 < n := by
    omega
  have hplateau := a.middle_order_eq_leftTarget
    (alphaV := alphaV) (alphaW := alphaW)
    b hdefect O hnoTwo hlong
  have hxPrevious :
      a.orderSequence.entryOrZero
          (O.transition.firstTwo - 2) =
        b.orderSequence.entryOrZero O.transition.lastZero :=
    hplateau (O.transition.firstTwo - 2) (by omega) (by omega)
  have hcommonPrevious := O.transition.middle
    (O.transition.firstTwo - 2) (by omega) (by omega)
  have hyPrevious :
      b.orderSequence.entryOrZero
          (O.transition.firstTwo - 2) =
        b.orderSequence.entryOrZero O.transition.lastZero := by
    rw [← hcommonPrevious]
    exact hxPrevious
  have hyPreviousTwo :
      b.orderSequence.entryOrZero
          (O.transition.firstTwo - 3) =
        b.orderSequence.entryOrZero O.transition.lastZero := by
    by_cases heq :
        O.transition.firstTwo - 3 = O.transition.lastZero
    · rw [heq]
    · have hlast :
          O.transition.lastZero <
            O.transition.firstTwo - 3 := by
        omega
      have hfirst :
          (O.transition.firstTwo - 3) + 1 <
            O.transition.firstTwo := by
        omega
      have hx := hplateau
        (O.transition.firstTwo - 3) hlast hfirst
      have hcommon := O.transition.middle
        (O.transition.firstTwo - 3) hlast hfirst
      rw [← hcommon]
      exact hx
  let i : RepresentationIndex (n + 1) (n + 1) := {
    val := O.transition.firstTwo - 1
    pos := by omega
    lt_large := hrightBound
    le_small := hrightBound.le }
  have hprefixGap := O.transition.gap_between i.val
    (by simp only [i]; omega) (by simp only [i]; omega)
  have hparity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val + 1) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    unfold BeliOrderSequence.prefixGap at hprefixGap
    omega
  have hupper :
      a.orderSequence.entryOrZero
          (O.transition.firstTwo - 1) ≤
        b.orderSequence.entryOrZero O.transition.lastZero := by
    rcases a.beli2019Lemma65
        (alphaV := alphaV) (alphaW := alphaW)
        b hdefect i hparity with hdirect | ⟨hi, hpair⟩
    · have hdirectEntry :
          a.orderSequence.entryOrZero i.val ≤
            b.orderSequence.entryOrZero (i.val - 1) := by
        have htargetBound : i.val - 1 < n + 1 :=
          (Nat.sub_le i.val 1).trans_lt i.lt_large
        rw [BeliOrderSequence.entryOrZero_of_lt
            a.orderSequence i.lt_large,
          BeliOrderSequence.entryOrZero_of_lt
            b.orderSequence htargetBound]
        simpa only [BeliOrderSequence.entry, orderSequence]
          using hdirect
      have hminusOne :
          i.val - 1 = O.transition.firstTwo - 2 := by
        simpa only [i] using
          nat_sub_one_sub_one O.transition.firstTwo
      have hcurrent :
          i.val = O.transition.firstTwo - 1 := by
        rfl
      rw [hminusOne, hcurrent] at hdirectEntry
      exact hdirectEntry.trans_eq hyPrevious
    · have hpairEntry :
          a.orderSequence.entryOrZero i.val +
              a.orderSequence.entryOrZero (i.val + 1) ≤
            b.orderSequence.entryOrZero (i.val - 2) +
              b.orderSequence.entryOrZero (i.val - 1) := by
        have hminusTwoBound : i.val - 2 < n + 1 :=
          (Nat.sub_le i.val 2).trans_lt i.lt_large
        have hminusOneBound : i.val - 1 < n + 1 :=
          (Nat.sub_le i.val 1).trans_lt i.lt_large
        rw [BeliOrderSequence.entryOrZero_of_lt
            a.orderSequence i.lt_large,
          BeliOrderSequence.entryOrZero_of_lt
            a.orderSequence hi.2,
          BeliOrderSequence.entryOrZero_of_lt
            b.orderSequence hminusTwoBound,
          BeliOrderSequence.entryOrZero_of_lt
            b.orderSequence hminusOneBound]
        simpa only [BeliOrderSequence.entry, orderSequence]
          using hpair
      have hminusTwo :
          i.val - 2 = O.transition.firstTwo - 3 := by
        simpa only [i] using
          nat_sub_one_sub_two O.transition.firstTwo
      have hminusOne :
          i.val - 1 = O.transition.firstTwo - 2 := by
        simpa only [i] using
          nat_sub_one_sub_one O.transition.firstTwo
      have hplusOne : i.val + 1 = O.transition.firstTwo := by
        simpa only [i] using
          nat_sub_one_add_one_of_pos hfirstPositive
      have hcurrent :
          i.val = O.transition.firstTwo - 1 := by
        rfl
      rw [hminusTwo, hminusOne, hplusOne, hcurrent] at hpairEntry
      have hxMonotone :=
        a.orderSequence.entryOrZero_le_of_evenGap
          (O.transition.firstTwo - 2) O.transition.firstTwo
          (by omega) (by simpa only [hplusOne] using hi.2)
          (by refine ⟨1, ?_⟩; omega)
      omega
  by_contra hne
  have hstrict :
      a.orderSequence.entryOrZero
          (O.transition.firstTwo - 1) <
        b.orderSequence.entryOrZero O.transition.lastZero :=
    lt_of_le_of_ne hupper hne
  have hright := O.transition.rightBoundary
  let gap : Fin n := ⟨O.transition.firstTwo - 2, hgapBound⟩
  have hgapSucc : gap.succ =
      ⟨O.transition.firstTwo - 1, hrightBound⟩ := by
    apply Fin.ext
    change O.transition.firstTwo - 2 + 1 =
      O.transition.firstTwo - 1
    omega
  have hgapCast : gap.castSucc =
      ⟨O.transition.firstTwo - 2, hpreviousBound⟩ := by
    apply Fin.ext
    rfl
  have haGapEq : a.orderGap gap =
      a.orderSequence.entryOrZero
          (O.transition.firstTwo - 1) -
        a.orderSequence.entryOrZero
          (O.transition.firstTwo - 2) := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hpreviousBound]
    change a.order gap.succ - a.order gap.castSucc =
      a.order ⟨O.transition.firstTwo - 1, hrightBound⟩ -
        a.order ⟨O.transition.firstTwo - 2, hpreviousBound⟩
    rw [hgapSucc, hgapCast]
  have hbGapEq : b.orderGap gap =
      b.orderSequence.entryOrZero
          (O.transition.firstTwo - 1) -
        b.orderSequence.entryOrZero
          (O.transition.firstTwo - 2) := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence hrightBound,
      BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence hpreviousBound]
    change b.order gap.succ - b.order gap.castSucc =
      b.order ⟨O.transition.firstTwo - 1, hrightBound⟩ -
        b.order ⟨O.transition.firstTwo - 2, hpreviousBound⟩
    rw [hgapSucc, hgapCast]
  have haEven := a.orderGap_even_of_nonpositive gap (by
    rw [haGapEq, hxPrevious]
    exact sub_nonpos.mpr hstrict.le)
  have hbEven := b.orderGap_even_of_nonpositive gap (by
    rw [hbGapEq, hyPrevious, hright]
    omega)
  rw [haGapEq, hxPrevious] at haEven
  rw [hbGapEq, hyPrevious, hright] at hbEven
  rcases haEven with ⟨ca, hca⟩
  rcases hbEven with ⟨cb, hcb⟩
  omega

end BONG.GoodBONG

end Bong
