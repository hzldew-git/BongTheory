/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma66
import Bong.Bong.Beli2019Lemma67Cross

/-!
# Beli (2019), Lemma 6.7: the left seed of the middle interval

The long no-gap-two branch starts with the identity
`R_{t+1} = S_t = R + 1`.  Its proof is the delicate left-end argument in
Lemma 6.7: Lemma 6.5 supplies a direct or a pair alternative, two-step
monotonicity eliminates most of the pair alternative, and Lemma 6.6 rules
out the two remaining parity configurations.
-/

namespace Bong

open Dyadic

universe u v w

/-- Two nonnegative integer increments whose sum is at most one cannot
both be nonzero. -/
theorem int_left_eq_or_right_eq_of_pair_le_add_one
    {a b c d : Int} (hab : a ≤ b) (hcd : c ≤ d)
    (hpair : b + d ≤ a + (c + 1)) : a = b ∨ c = d := by
  by_cases habEq : a = b
  · exact Or.inl habEq
  · apply Or.inr
    apply le_antisymm hcd
    by_contra hnot
    have habStrict : a < b := lt_of_le_of_ne hab habEq
    have hcdStrict : c < d := lt_of_not_ge hnot
    have habOne : a + 1 ≤ b := Int.add_one_le_iff.mpr habStrict
    have hcdOne : c + 1 ≤ d := Int.add_one_le_iff.mpr hcdStrict
    have hlower := add_le_add habOne hcdOne
    linarith

theorem nat_add_one_sub_two (k : Nat) : (k + 1) - 2 = k - 1 := by
  omega

theorem nat_add_one_sub_one (k : Nat) : (k + 1) - 1 = k := by
  omega

namespace BeliOrderLE.NoGapTwoOuterConsequences

/-- In the nontrivial left outer profile, the final adjacent pair before
the middle interval has equal source and target sums. -/
theorem leftBoundaryPairEq_of_first_lt {n : Nat}
    {x y : BeliOrderSequence n Int}
    (O : BeliOrderLE.NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n →
      y.entryOrZero k < x.entryOrZero k + 2)
    (hfirstLt : O.first < O.transition.lastZero) :
    x.entryOrZero (O.transition.lastZero - 1) +
        x.entryOrZero O.transition.lastZero =
      y.entryOrZero (O.transition.lastZero - 1) +
        y.entryOrZero O.transition.lastZero := by
  have hleftBound : O.transition.lastZero < n := by
    have := O.transition.firstTwo_le_rank
    have := O.transition.lastZero_lt_firstTwo
    omega
  rcases O.leftProfile hfirstLt with
    ⟨hfirstParity, hfirstLtValue, hprofile⟩
  rcases hfirstParity with ⟨d, hd⟩
  have hdPositive : 0 < d := by omega
  have hfirstParity' :
      Even (O.transition.lastZero - O.first) := ⟨d, hd⟩
  have hfirstGap :
      y.entryOrZero O.first = x.entryOrZero O.first + 1 := by
    have hupper := hnoTwo O.first O.firstDifference.bound
    omega
  have hxFirstLast :
      x.entryOrZero O.transition.lastZero =
        x.entryOrZero O.first :=
    hprofile O.transition.lastZero O.first_le_left le_rfl
      hfirstParity'
  have hyFirstLast :
      y.entryOrZero O.first =
        y.entryOrZero O.transition.lastZero := by
    rw [hfirstGap, O.transition.leftBoundary, hxFirstLast]
  have hpreviousParity :
      Even ((O.transition.lastZero - 2) - O.first) := by
    refine ⟨d - 1, ?_⟩
    omega
  have hlastPreviousParity :
      Even (O.transition.lastZero -
        (O.transition.lastZero - 2)) := by
    refine ⟨1, ?_⟩
    omega
  have hxPrevious :
      x.entryOrZero (O.transition.lastZero - 2) =
        x.entryOrZero O.first :=
    hprofile (O.transition.lastZero - 2) (by omega) (by omega)
      hpreviousParity
  have hyLower := y.entryOrZero_le_of_evenGap
    O.first (O.transition.lastZero - 2) (by omega) (by omega)
    hpreviousParity
  have hyUpper := y.entryOrZero_le_of_evenGap
    (O.transition.lastZero - 2) O.transition.lastZero
    (by omega) hleftBound
    hlastPreviousParity
  have hyPrevious :
      y.entryOrZero (O.transition.lastZero - 2) =
        y.entryOrZero O.transition.lastZero := by
    apply le_antisymm hyUpper
    rw [← hyFirstLast]
    exact hyLower
  have hpair := O.leftPairEq (O.transition.lastZero - 2)
    (by omega) hlastPreviousParity
  rw [hxPrevious, ← hxFirstLast, hyPrevious] at hpair
  have hpreviousIndex :
      O.transition.lastZero - 2 + 1 =
        O.transition.lastZero - 1 := by
    omega
  rw [hpreviousIndex] at hpair
  calc
    x.entryOrZero (O.transition.lastZero - 1) +
        x.entryOrZero O.transition.lastZero =
      x.entryOrZero O.transition.lastZero +
        x.entryOrZero (O.transition.lastZero - 1) := add_comm _ _
    _ = y.entryOrZero O.transition.lastZero +
        y.entryOrZero (O.transition.lastZero - 1) := hpair
    _ = y.entryOrZero (O.transition.lastZero - 1) +
        y.entryOrZero O.transition.lastZero := add_comm _ _

end BeliOrderLE.NoGapTwoOuterConsequences

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Equal same-parity endpoints force the comparison shift at every
intermediate index to retain its parity. -/
theorem comparisonShift_ne_add_one_of_equal_even_endpoints
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i k j : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j)
    (hijParity : Even (j.1 - i.1))
    (haEnds : a.order i = a.order j)
    (hbEnds : b.order i = b.order j) :
    b.order k - a.order k ≠
      (b.order i - a.order i) + 1 := by
  intro hshift
  have haMod :=
    (a.beli2019Lemma66_i i j (hik.trans hkj) hijParity haEnds).order_modEq
      k hik hkj
  have hbMod :=
    (b.beli2019Lemma66_i i j (hik.trans hkj) hijParity hbEnds).order_modEq
      k hik hkj
  rw [Int.modEq_iff_dvd] at haMod hbMod
  rcases haMod with ⟨ca, hca⟩
  rcases hbMod with ⟨cb, hcb⟩
  omega

/-- Natural-index, zero-extended form of
`comparisonShift_ne_add_one_of_equal_even_endpoints`. -/
theorem comparisonEntryShift_ne_add_one_of_equal_even_endpoints
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (i k j : Nat) (hj : j < n + 1) (hik : i ≤ k) (hkj : k ≤ j)
    (hijParity : Even (j - i))
    (haEnds : a.orderSequence.entryOrZero i =
      a.orderSequence.entryOrZero j)
    (hbEnds : b.orderSequence.entryOrZero i =
      b.orderSequence.entryOrZero j) :
    b.orderSequence.entryOrZero k -
        a.orderSequence.entryOrZero k ≠
      (b.orderSequence.entryOrZero i -
          a.orderSequence.entryOrZero i) + 1 := by
  have hi : i < n + 1 := hik.trans_lt (hkj.trans_lt hj)
  have hk : k < n + 1 := hkj.trans_lt hj
  let iFin : Fin (n + 1) := ⟨i, hi⟩
  let kFin : Fin (n + 1) := ⟨k, hk⟩
  let jFin : Fin (n + 1) := ⟨j, hj⟩
  have haEnds' : a.order iFin = a.order jFin := by
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence hi,
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hj]
      at haEnds
    change a.order iFin = a.order jFin at haEnds
    exact haEnds
  have hbEnds' : b.order iFin = b.order jFin := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence hj]
      at hbEnds
    change b.order iFin = b.order jFin at hbEnds
    exact hbEnds
  have hne := a.comparisonShift_ne_add_one_of_equal_even_endpoints
    b iFin kFin jFin (by exact hik) (by exact hkj)
    hijParity haEnds' hbEnds'
  intro hshift
  apply hne
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hk,
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence hk,
    BeliOrderSequence.entryOrZero_of_lt b.orderSequence hi,
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence hi]
    at hshift
  change b.order kFin - a.order kFin =
    (b.order iFin - a.order iFin) + 1 at hshift
  exact hshift

/-- The left seed identity `R_{t+1} = S_t = R + 1` in the long
type-II branch of Lemma 6.7. -/
theorem middleSeed_eq_leftTarget
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
        (O.transition.lastZero + 1) =
      b.orderSequence.entryOrZero O.transition.lastZero := by
  have hfirstTwoBound := O.transition.firstTwo_le_rank
  have hleftBound : O.transition.lastZero < n + 1 := by omega
  have hmiddleBound : O.transition.lastZero + 1 < n + 1 := by
    omega
  have hrightBound : O.transition.lastZero + 2 < n + 1 := by
    omega
  have hgapBound : O.transition.lastZero < n := by omega
  let i : RepresentationIndex (n + 1) (n + 1) := {
    val := O.transition.lastZero + 1
    pos := by omega
    lt_large := hmiddleBound
    le_small := hmiddleBound.le }
  have hprefixGap := O.transition.gap_between
    (O.transition.lastZero + 1) (by omega) (by omega)
  have hparity : Int.ModEq 2
      (a.orderSequence.prefixSum i.val)
      (b.orderSequence.prefixSum i.val + 1) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    simp only [i]
    unfold BeliOrderSequence.prefixGap at hprefixGap
    omega
  have hdirectEntry :
      a.orderSequence.entryOrZero
          (O.transition.lastZero + 1) ≤
        b.orderSequence.entryOrZero O.transition.lastZero := by
    rcases a.beli2019Lemma65
        (alphaV := alphaV) (alphaW := alphaW)
        b hdefect i hparity with hdirect | ⟨hi, hpair⟩
    · have hdirectEntryRaw :
          a.orderSequence.entryOrZero i.val ≤
            b.orderSequence.entryOrZero (i.val - 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt
            a.orderSequence i.lt_large,
          BeliOrderSequence.entryOrZero_of_lt
            b.orderSequence
              (show i.val - 1 < n + 1 by
                have := i.lt_large
                omega)]
        simpa only [BeliOrderSequence.entry, orderSequence]
          using hdirect
      have hminusOne : i.val - 1 = O.transition.lastZero := by
        simp only [i]
        omega
      have hcurrent : i.val = O.transition.lastZero + 1 := by
        rfl
      rw [hminusOne, hcurrent] at hdirectEntryRaw
      exact hdirectEntryRaw
    · have hleftPositive : 0 < O.transition.lastZero := by
        have hiPositive := hi.1
        simp only [i] at hiPositive
        omega
      have hpairEntry :
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
          i.val - 2 = O.transition.lastZero - 1 := by
        simpa only [i] using
          nat_add_one_sub_two O.transition.lastZero
      have hminusOne : i.val - 1 = O.transition.lastZero := by
        simpa only [i] using
          nat_add_one_sub_one O.transition.lastZero
      have hplusOne :
          i.val + 1 = O.transition.lastZero + 2 := by
        simp only [i, Nat.add_assoc]
      have hcurrent : i.val = O.transition.lastZero + 1 := by
        rfl
      rw [hminusTwo, hminusOne, hplusOne, hcurrent] at hpairEntry
      have hxPrevious :=
        a.orderSequence.entryOrZero_le_of_evenGap
          (O.transition.lastZero - 1)
          (O.transition.lastZero + 1) (by omega)
          hmiddleBound (by refine ⟨1, ?_⟩; omega)
      have hxCurrent :=
        a.orderSequence.entryOrZero_le_of_evenGap
          O.transition.lastZero
          (O.transition.lastZero + 2) (by omega)
          hrightBound (by refine ⟨1, ?_⟩; omega)
      have hEqualTwoImpossible :
          a.orderSequence.entryOrZero O.transition.lastZero =
            a.orderSequence.entryOrZero
              (O.transition.lastZero + 2) → False := by
        intro hEqualTwo
        by_cases hinterior :
            O.transition.lastZero + 3 < O.transition.firstTwo
        · have hcommon := O.transition.middle
              (O.transition.lastZero + 2) (by omega) hinterior
          have hyMonotone :=
            b.orderSequence.entryOrZero_le_of_evenGap
              O.transition.lastZero
              (O.transition.lastZero + 2) (by omega)
              hrightBound (by refine ⟨1, ?_⟩; omega)
          have hleft := O.transition.leftBoundary
          omega
        · have hfirstTwoEq :
              O.transition.firstTwo =
                O.transition.lastZero + 3 := by
            omega
          have hright := O.transition.rightBoundary
          have hrightIndex :
              O.transition.firstTwo - 1 =
                O.transition.lastZero + 2 := by
            omega
          rw [hrightIndex] at hright
          have hmiddleFirst :
              (O.transition.lastZero + 1) + 1 <
                O.transition.firstTwo := by
            simpa only [Nat.add_assoc] using hlong
          have hcommon := O.transition.middle
            (O.transition.lastZero + 1)
            (Nat.lt_succ_self _) hmiddleFirst
          have hbEnds :
              b.orderSequence.entryOrZero O.transition.lastZero =
                b.orderSequence.entryOrZero
                  (O.transition.lastZero + 2) := by
            have hleft := O.transition.leftBoundary
            omega
          have hne :=
            b.comparisonEntryShift_ne_add_one_of_equal_even_endpoints
              a O.transition.lastZero
              (O.transition.lastZero + 1)
              (O.transition.lastZero + 2) hrightBound
              (by omega) (by omega)
              (by refine ⟨1, ?_⟩; omega) hbEnds hEqualTwo
          apply hne
          have hleft := O.transition.leftBoundary
          omega
      by_cases hfirstLt :
          O.first < O.transition.lastZero
      · have hboundaryPair := O.leftBoundaryPairEq_of_first_lt
          hnoTwo hfirstLt
        have hEqualTwo :
            a.orderSequence.entryOrZero O.transition.lastZero =
              a.orderSequence.entryOrZero
                (O.transition.lastZero + 2) := by
          omega
        exact (hEqualTwoImpossible hEqualTwo).elim
      · have hfirstEq : O.first = O.transition.lastZero := by
          exact le_antisymm O.first_le_left
            (Nat.le_of_not_gt hfirstLt)
        have hpreviousLt :
            O.transition.lastZero - 1 < O.first := by
          rw [hfirstEq]
          exact Nat.sub_lt hleftPositive (by decide)
        have hbefore := O.firstDifference.before
          (O.transition.lastZero - 1) hpreviousLt
        have hleft := O.transition.leftBoundary
        rw [← hbefore, hleft] at hpairEntry
        have hEqual :
            a.orderSequence.entryOrZero
                  (O.transition.lastZero - 1) =
                a.orderSequence.entryOrZero
                  (O.transition.lastZero + 1) ∨
              a.orderSequence.entryOrZero O.transition.lastZero =
                a.orderSequence.entryOrZero
                  (O.transition.lastZero + 2) := by
          apply int_left_eq_or_right_eq_of_pair_le_add_one
          · exact hxPrevious
          · exact hxCurrent
          · simpa only [] using hpairEntry
        rcases hEqual with hEqualPrevious | hEqualTwo
        · have hmiddleFirst :
              (O.transition.lastZero + 1) + 1 <
                O.transition.firstTwo := by
            simpa only [Nat.add_assoc] using hlong
          have hcommon := O.transition.middle
            (O.transition.lastZero + 1)
            (Nat.lt_succ_self _) hmiddleFirst
          have hbEnds :
              b.orderSequence.entryOrZero
                  (O.transition.lastZero - 1) =
                b.orderSequence.entryOrZero
                  (O.transition.lastZero + 1) := by
            calc
              b.orderSequence.entryOrZero
                    (O.transition.lastZero - 1) =
                  a.orderSequence.entryOrZero
                    (O.transition.lastZero - 1) := hbefore.symm
              _ = a.orderSequence.entryOrZero
                    (O.transition.lastZero + 1) := hEqualPrevious
              _ = b.orderSequence.entryOrZero
                    (O.transition.lastZero + 1) := hcommon
          have hindexLeft :
              O.transition.lastZero - 1 ≤
                O.transition.lastZero :=
            Nat.sub_le _ _
          have hindexRight :
              O.transition.lastZero ≤
                O.transition.lastZero + 1 :=
            Nat.le_succ _
          have hintervalParity :
              Even ((O.transition.lastZero + 1) -
                (O.transition.lastZero - 1)) := by
            refine ⟨1, ?_⟩
            omega
          have hne :=
            a.comparisonEntryShift_ne_add_one_of_equal_even_endpoints
              b (O.transition.lastZero - 1)
              O.transition.lastZero
              (O.transition.lastZero + 1) hmiddleBound
              hindexLeft hindexRight hintervalParity
              hEqualPrevious hbEnds
          exfalso
          apply hne
          calc
            b.orderSequence.entryOrZero O.transition.lastZero -
                a.orderSequence.entryOrZero
                  O.transition.lastZero = 1 := by
              rw [hleft]
              ring
            _ = b.orderSequence.entryOrZero
                    (O.transition.lastZero - 1) -
                  a.orderSequence.entryOrZero
                    (O.transition.lastZero - 1) + 1 := by
              rw [← hbefore]
              ring
        · exact (hEqualTwoImpossible hEqualTwo).elim
  have hmiddle := O.transition.middle
    (O.transition.lastZero + 1) (by omega) hlong
  have hleft := O.transition.leftBoundary
  by_contra hne
  have hxNonpositive :
      a.orderSequence.entryOrZero
          (O.transition.lastZero + 1) ≤
        a.orderSequence.entryOrZero O.transition.lastZero := by
    omega
  have hyNonpositive :
      b.orderSequence.entryOrZero
          (O.transition.lastZero + 1) ≤
        b.orderSequence.entryOrZero O.transition.lastZero := by
    omega
  let gap : Fin n := ⟨O.transition.lastZero, hgapBound⟩
  have haGapEq : a.orderGap gap =
      a.orderSequence.entryOrZero
          (O.transition.lastZero + 1) -
        a.orderSequence.entryOrZero O.transition.lastZero := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hmiddleBound,
      BeliOrderSequence.entryOrZero_of_lt
        a.orderSequence hleftBound]
    rfl
  have hbGapEq : b.orderGap gap =
      b.orderSequence.entryOrZero
          (O.transition.lastZero + 1) -
        b.orderSequence.entryOrZero O.transition.lastZero := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence hmiddleBound,
      BeliOrderSequence.entryOrZero_of_lt
        b.orderSequence hleftBound]
    rfl
  have haEven := a.orderGap_even_of_nonpositive gap (by
    rw [haGapEq]
    omega)
  have hbEven := b.orderGap_even_of_nonpositive gap (by
    rw [hbGapEq]
    omega)
  rw [haGapEq] at haEven
  rw [hbGapEq] at hbEven
  rcases haEven with ⟨ca, hca⟩
  rcases hbEven with ⟨cb, hcb⟩
  omega

/-- The full constant middle interval in the long type-II branch. -/
theorem middle_order_eq_leftTarget
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
    ∀ k, O.transition.lastZero < k →
      k + 1 < O.transition.firstTwo →
      a.orderSequence.entryOrZero k =
        b.orderSequence.entryOrZero
          O.transition.lastZero := by
  have hseed := a.middleSeed_eq_leftTarget
    (alphaV := alphaV) (alphaW := alphaW)
    b hdefect O hnoTwo hlong
  exact a.middle_order_eq_leftTarget_of_seed
    (alphaV := alphaV) (alphaW := alphaW)
    b hdefect O.transition hseed

end BONG.GoodBONG

end Bong
