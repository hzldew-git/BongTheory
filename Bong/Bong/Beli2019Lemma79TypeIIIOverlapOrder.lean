/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIRight
import Bong.Bong.Beli2019Lemma72TypeIIIOverlap

/-!
# Beli (2019), Lemma 7.9(i), overlapping type-III profiles

The central-gap-one type-III profile has the type-II prefix congruences.
This file supplies its hard right-even order comparison and then combines it
with the common left and right-odd comparisons at every nonterminal coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- In the right-even class of a central-gap-one type-III profile, the target
current order is bounded by the following source order. -/
theorem lemma79_typeIII_overlap_rightEven_targetCurrent_le_sourceNext
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (k : Nat) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entryOrZero k ≤
      a.orderSequence.entryOrZero (k + 1) := by
  let left := D.outer.transition.lastZero
  let right := D.outer.transition.firstTwo - 1
  let T := b.orderSequence.entryOrZero left
  have hrightEq : right = left + 1 := by
    simp only [right, left]
    rw [D.adjacent]
    omega
  have hleftBound : left < n + 2 := by
    simp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  have hleftGapBound : left < n + 1 := by
    simp only [left]
    have hbound := D.outer.transition.firstTwo_le_rank
    rw [D.adjacent] at hbound
    omega
  let center : Fin (n + 1) := ⟨left, hleftGapBound⟩
  have hgapFormula : a.orderGap center =
      a.orderSequence.entryOrZero right -
        a.orderSequence.entryOrZero left := by
    unfold orderGap
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
          simp only [right]
          have hbound := D.outer.transition.firstTwo_le_rank
          omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
    congr 1
    apply congrArg a.order
    apply Fin.ext
    simp only [center, Fin.val_succ]
    exact hrightEq.symm
  have hoverlap' : a.orderGap center = 1 := by
    simpa only [center, left] using hoverlap
  have hleftBoundary : T =
      a.orderSequence.entryOrZero left + 1 := by
    simpa only [T, left] using D.outer.transition.leftBoundary
  have hsourceRight : a.orderSequence.entryOrZero right = T := by
    rw [hgapFormula] at hoverlap'
    omega
  have htargetRight : b.orderSequence.entryOrZero right = T + 1 := by
    have hboundary := D.outer.transition.rightBoundary
    simpa only [right, hsourceRight] using hboundary
  have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
    k (by simpa only [right] using hright) hlast
      (by simpa only [right] using heven)
  have hcurrent : b.orderSequence.entryOrZero k = T + 1 := by
    exact hcurrentBoundary.trans htargetRight
  rcases heven with ⟨d, hd⟩
  have hbaseNextParity : Even (k + 1 - left) := by
    refine ⟨d + 1, ?_⟩
    omega
  have hnextLower := b.orderSequence.entryOrZero_le_of_evenGap
    left (k + 1) (by omega) hkNext hbaseNextParity
  have htargetNext : T + 1 ≤
      b.orderSequence.entryOrZero (k + 1) := by
    by_contra hnot
    have hnextEq : b.orderSequence.entryOrZero (k + 1) = T := by
      simpa only [T] using le_antisymm (by omega) hnextLower
    let gap : Fin (n + 1) := ⟨k, by omega⟩
    have hgapFormulaNext : b.orderGap gap =
        b.orderSequence.entryOrZero (k + 1) -
          b.orderSequence.entryOrZero k := by
      unfold orderGap
      rw [← b.orderSequence_entryOrZero_eq_order gap.succ,
        ← b.orderSequence_entryOrZero_eq_order gap.castSucc]
      rfl
    have hgapNegative : b.orderGap gap < 0 := by
      rw [hgapFormulaNext, hnextEq, hcurrent]
      omega
    have hgapEven := b.orderGap_even_of_negative gap hgapNegative
    rw [hgapFormulaNext, hnextEq, hcurrent] at hgapEven
    rcases hgapEven with ⟨e, he⟩
    omega
  have htargetSourceNext : b.orderSequence.entryOrZero (k + 1) ≤
      a.orderSequence.entryOrZero (k + 1) := by
    by_cases hkLast : k < D.outer.last
    · have hnextOdd : Odd
          (k + 1 - (D.outer.transition.firstTwo - 1)) :=
        ⟨d, by omega⟩
      have hnextValue := D.outer.source_rightOdd_eq_target_add_one
        D.no_gap_two (k + 1) (by omega) (by omega) hnextOdd
      omega
    · have hkEq : k = D.outer.last := by omega
      have heq := D.outer.lastDifference.after (k + 1)
        (by omega) hkNext
      omega
  omega

set_option maxHeartbeats 5000000 in
/-- Lemma 7.9(i) in the hard right-even class of an overlapping type-III
profile. -/
theorem beli2019Lemma79_i_typeIII_overlap_rightEven
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hdefect : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hdirect : b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk
  · exact Or.inl hdirect
  · let T := b.orderSequence.entryOrZero D.outer.transition.lastZero
    have hrightEq : D.outer.transition.firstTwo - 1 =
        D.outer.transition.lastZero + 1 := by
      rw [D.adjacent]
      omega
    have htargetBoundary : b.orderSequence.entryOrZero
        (D.outer.transition.firstTwo - 1) = T + 1 := by
      let left := D.outer.transition.lastZero
      let right := D.outer.transition.firstTwo - 1
      have hleftBound : left < n + 2 := by
        simp only [left]
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      have hleftGapBound : left < n + 1 := by
        simp only [left]
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega
      let center : Fin (n + 1) := ⟨left, hleftGapBound⟩
      have hgapFormula : a.orderGap center =
          a.orderSequence.entryOrZero right -
            a.orderSequence.entryOrZero left := by
        unfold orderGap
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by
              simp only [right]
              have hbound := D.outer.transition.firstTwo_le_rank
              omega),
          BeliOrderSequence.entryOrZero_of_lt a.orderSequence hleftBound]
        congr 1
        apply congrArg a.order
        apply Fin.ext
        simp only [center, Fin.val_succ, right, left]
        exact hrightEq.symm
      have hoverlap' : a.orderGap center = 1 := by
        simpa only [center, left] using hoverlap
      have hleftBoundary : T =
          a.orderSequence.entryOrZero left + 1 := by
        simpa only [T, left] using D.outer.transition.leftBoundary
      have hsourceRight : a.orderSequence.entryOrZero right = T := by
        rw [hgapFormula] at hoverlap'
        omega
      have hboundary := D.outer.transition.rightBoundary
      simpa only [right, hsourceRight] using hboundary
    have hcurrentBoundary := D.outer.target_rightEven_eq_boundary
      k hright hlast heven
    have hbCurrent : b.orderSequence.entryOrZero k = T + 1 := by
      exact hcurrentBoundary.trans htargetBoundary
    have hcCurrent : c.orderSequence.entryOrZero k ≤ T := by
      rw [b.orderSequence.entryOrZero_of_lt hk] at hbCurrent
      rw [c.orderSequence.entryOrZero_of_lt hk]
      omega
    have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
      c.toBONG hnorm
    have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
        c.orderSequence.entryOrZero 0 := by
      calc
        a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
          rw [a.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
        _ ≤ c.order 0 := hnormOrder
        _ = c.orderSequence.entryOrZero 0 := by
          rw [c.orderSequence.entryOrZero_of_lt (by omega)]
          rfl
    have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
    have hleftValue := D.outer.target_leftEven_eq_first_add_one
      hfirst D.no_gap_two D.outer.transition.lastZero le_rfl hleftEven
    have hreferenceFirst : T ≤ c.orderSequence.entryOrZero 0 := by
      simpa only [T, hleftValue] using hfirstOrder
    have hcParity :=
      c.prefixSum_modEq_mul_of_current_le_reference_le_first
        T k hk hreferenceFirst hcCurrent
    let P := a.beli2019Lemma72_ii_typeIII_overlap b D hfirst hoverlap
    have haParity := P.source_after (k + 1) (by omega) (by omega)
    let X : Int := (((k + 1 : Nat) : Int) * T)
    have hshift : Int.ModEq 2 (X - 1) (X + 1) := by
      rw [Int.modEq_iff_dvd]
      exact ⟨1, by ring⟩
    have hcPlus := hcParity.add
      (Int.ModEq.rfl : Int.ModEq 2 (1 : Int) 1)
    have hparity : Int.ModEq 2
        (a.orderSequence.prefixSum (k + 1))
        (c.orderSequence.prefixSum (k + 1) + 1) := by
      have haShift : Int.ModEq 2
          (a.orderSequence.prefixSum (k + 1)) (X + 1) := by
        have haBase : Int.ModEq 2
            (a.orderSequence.prefixSum (k + 1)) (X - 1) := by
          simpa only [P, T, X] using haParity
        exact haBase.trans hshift
      exact haShift.trans (by simpa only [X] using hcPlus.symm)
    let i : RepresentationIndex (n + 2) (n + 2) := {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := by omega }
    rcases a.beli2019Lemma65 c hdefect i (by
      simpa only [i] using hparity) with hnext | ⟨hi, hpair⟩
    · left
      have hbSource :=
        lemma79_typeIII_overlap_rightEven_targetCurrent_le_sourceNext
          a b D hoverlap k hkNext hright hlast heven
      have hnextEntry : a.orderSequence.entryOrZero (k + 1) ≤
          c.orderSequence.entryOrZero k := by
        rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
          c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
        convert hnext using 1
        apply congrArg c.order
        apply Fin.ext
        simp only [i]
        omega
      rw [← b.orderSequence.entryOrZero_of_lt hk,
        ← c.orderSequence.entryOrZero_of_lt hk]
      exact hbSource.trans hnextEntry
    · right
      have hk0 : 0 < k := by
        have hseparated := D.outer.transition.separated
        omega
      refine ⟨hk0, hkNext, ?_⟩
      have hkTwo : k + 2 < n + 2 := by
        simpa only [i] using hi.2
      have hpairEntry :
          a.orderSequence.entryOrZero (k + 1) +
              a.orderSequence.entryOrZero (k + 2) ≤
            c.orderSequence.entryOrZero (k - 1) +
              c.orderSequence.entryOrZero k := by
        rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
          a.orderSequence_entryOrZero_eq_order ⟨k + 2, hkTwo⟩,
          c.orderSequence_entryOrZero_eq_order ⟨k - 1, by omega⟩,
          c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
        convert hpair using 1
        congr 1
      rcases heven with ⟨d, hd⟩
      have hfirstTwoPos : 0 < D.outer.transition.firstTwo := by
        have hseparated := D.outer.transition.separated
        omega
      have hfirstK : D.outer.transition.firstTwo ≤ k + 1 := by omega
      have hpairParity : Even
          (k + 1 - D.outer.transition.firstTwo) := ⟨d, by omega⟩
      have habPair := D.outer.rightPairEq (k + 1) hfirstK (by omega)
        hpairParity
      have habPair' :
          a.orderSequence.entryOrZero (k + 1) +
              a.orderSequence.entryOrZero (k + 2) =
              b.orderSequence.entryOrZero (k + 1) +
              b.orderSequence.entryOrZero (k + 2) := by
        convert habPair using 1
      have hbTwoStep := b.orderSequence.twoStep k hi.2
      change b.orderSequence.entry k (by omega) ≤
        b.orderSequence.entry (k + 2) hi.2 at hbTwoStep
      calc
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
            b.orderSequence.entry (k + 1) hkNext +
              b.orderSequence.entry (k + 2) hi.2 := by omega
        _ = a.orderSequence.entryOrZero (k + 1) +
              a.orderSequence.entryOrZero (k + 2) := by
          rw [b.orderSequence.entryOrZero_of_lt hkNext,
            b.orderSequence.entryOrZero_of_lt hkTwo] at habPair'
          exact habPair'.symm
        _ ≤ c.orderSequence.entryOrZero (k - 1) +
              c.orderSequence.entryOrZero k := hpairEntry
        _ = c.orderSequence.entry (k - 1) (by omega) +
              c.orderSequence.entry k hk := by
          rw [c.orderSequence.entryOrZero_of_lt (by omega),
            c.orderSequence.entryOrZero_of_lt hk]

/-- Condition 2.1(i) at every nonterminal coordinate of the overlapping
type-III branch. -/
theorem beli2019Lemma79_i_typeIII_overlap_nonterminal
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hlastK : k ≤ D.outer.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hleft : k ≤ D.outer.transition.lastZero
  · exact a.beli2019Lemma79_i_typeIII_leftOuter
      b c D hfirst hac hnorm k hk hleft
  · have hright : D.outer.transition.firstTwo - 1 ≤ k := by
      rw [D.adjacent]
      omega
    rcases Nat.even_or_odd
        (k - (D.outer.transition.firstTwo - 1)) with heven | hodd
    · exact a.beli2019Lemma79_i_typeIII_overlap_rightEven
        b c D hfirst hoverlap hdefectAC hnorm k hk hkNext
          hright hlastK heven
    · exact a.beli2019Lemma79_i_typeIII_rightAlternating
        b c D hac k hk hright hlastK hodd

end BONG.GoodBONG

end Bong
