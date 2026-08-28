/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIIInterior

/-!
# Beli (2019), Lemma 7.9(i): a nonoverlapping type-III terminal switch

This is the endpoint omitted by the former full-span formulation.  The last
unequal coordinate still has a successor, so condition 2.1(i) retains its
adjacent-pair alternative.  In the secondary branch the two coordinates after
the switch are common to the source and target BONGs; two-step monotonicity
therefore replaces the right-profile identity used strictly before the last
difference.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 1200000 in
/-- Condition 2.1(i) at the last unequal coordinate of a nonoverlapping
type-III profile when a common suffix coordinate still follows it. -/
theorem beli2019Lemma79_i_typeIII_nonoverlap_terminalSwitch
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkLast : k = D.outer.last)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (heven : Even (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext' : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext' ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hdirect : b.orderSequence.entry k hk ≤
      c.orderSequence.entry k hk
  · exact Or.inl hdirect
  · let left := D.outer.transition.lastZero
    let C : Int := b.orderSequence.entryOrZero left -
      a.orderSequence.entryOrZero (left + 1)
    let idx : RepresentationIndex (n + 2) (n + 2) := {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le }
    have hlastK : k ≤ D.outer.last := hkLast.le
    have hcurrent : c.orderSequence.entryOrZero k <
        b.orderSequence.entryOrZero k := by
      rw [b.orderSequence.entryOrZero_of_lt hk,
        c.orderSequence.entryOrZero_of_lt hk]
      exact lt_of_not_ge hdirect
    have hiStart : D.outer.transition.lastZero + 2 ≤ k + 1 := by
      rw [← D.adjacent]
      omega
    have hiLast : k + 1 ≤ D.outer.last + 1 := by omega
    have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
    have hrightIndex : D.outer.transition.firstTwo - 1 = left + 1 := by
      simp only [left]
      rw [D.adjacent]
      omega
    have hrightOdd : Odd (D.outer.transition.firstTwo - 1) := by
      rcases hleftEven with ⟨d, hd⟩
      rw [hrightIndex]
      exact ⟨d, by omega⟩
    have hkOdd : Odd k := by
      rcases hrightOdd with ⟨d, hd⟩
      rcases heven with ⟨e, he⟩
      exact ⟨d + e, by omega⟩
    have hiEven : Even (k + 1) := by
      rcases hkOdd with ⟨d, hd⟩
      exact ⟨d + 1, by omega⟩
    have hcomparisonRaw :=
      a.lemma79_typeIII_comparisonPrefix_eq_mixedShift
        b c D hfirst hdefectAB hnotOverlap hinitial hnorm
          k hk hright hlastK heven hcurrent
    have hleftBound : left < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      dsimp only [left]
      rw [D.adjacent] at hbound
      omega
    have hrightBound : left + 1 < n + 2 := by
      have hbound := D.outer.transition.firstTwo_le_rank
      dsimp only [left]
      rw [D.adjacent] at hbound
      omega
    have hcomparison : a.truncatedPrefixDefect c 1 idx.val idx.val =
        (((C : ℚ)) : WithTop ℚ) := by
      rw [← b.orderSequence_entryOrZero_eq_order ⟨left, hleftBound⟩,
        ← a.orderSequence_entryOrZero_eq_order ⟨left + 1, hrightBound⟩]
        at hcomparisonRaw
      simpa only [idx, C, left] using hcomparisonRaw
    have hAlpha : (a.representationAlphaValue c idx : WithTop ℚ) ≤
        (((C : ℚ)) : WithTop ℚ) :=
      (hdefectAC idx).trans_eq hcomparison
    have hgap := (a.beli2019Lemma78_sourceAlpha_and_gap
      b D hfirst hdefectAB hnotOverlap hinitial).2
    have hhalf := a.lemma79_typeIII_mixedShift_lt_representationHalfGap
      b c D hgap k hk hkNext hright hlastK heven hcurrent
    have hprime := a.representationAlphaPrime_le_of_alphaValue_le_of_lt_halfGap
      c idx (((C : ℚ)) : WithTop ℚ) hAlpha (by
        simpa only [idx, C, left] using hhalf)
    have hkPos : 0 < k := by
      have hseparated := D.outer.transition.separated
      omega
    have finishPrimary
        (hprimary : a.representationPrimaryDefect c idx ≤
          (((C : ℚ)) : WithTop ℚ)) :
        b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
          ∃ (hk0 : 0 < k) (hkNext' : k + 1 < n + 2),
            b.orderSequence.entry k hk +
                b.orderSequence.entry (k + 1) hkNext' ≤
              c.orderSequence.entry (k - 1) (by omega) +
                c.orderSequence.entry k hk := by
      have hpair := a.lemma79_typeIII_pair_of_primary_le_mixedShift
        b c D hfirst hdefectAB hnotOverlap hnorm k hk hkNext hright
          hlastK heven hcurrent (by simpa only [idx, C, left] using hprimary)
      exact Or.inr ⟨hkPos, hkNext, by
        simpa only [BeliOrderSequence.entryOrZero_of_lt _ hk,
          BeliOrderSequence.entryOrZero_of_lt _ hkNext,
          BeliOrderSequence.entryOrZero_of_lt _
            (show k - 1 < n + 2 by omega)] using hpair⟩
    by_cases hi : 1 < idx.val ∧ idx.val + 1 < n + 2
    · have hkNextNext : k + 2 < n + 2 := by
        simpa only [idx] using hi.2
      have hcommonNext := D.outer.lastDifference.after
        (k + 1) (by rw [← hkLast]; omega) hkNext
      have hcommonNextNext := D.outer.lastDifference.after
        (k + 2) (by rw [← hkLast]; omega) hkNextNext
      have hbTwoStep := b.orderSequence.twoStep k hkNextNext
      change b.orderSequence.entry k (by omega) ≤
        b.orderSequence.entry (k + 2) hkNextNext at hbTwoStep
      have hbTwoStep' : b.orderSequence.entryOrZero k ≤
          b.orderSequence.entryOrZero (k + 2) := by
        rw [b.orderSequence.entryOrZero_of_lt hk,
          b.orderSequence.entryOrZero_of_lt hkNextNext]
        exact hbTwoStep
      have hcrossEntries : c.orderSequence.entryOrZero k ≤
          a.orderSequence.entryOrZero (k + 2) := by
        calc
          c.orderSequence.entryOrZero k ≤
              b.orderSequence.entryOrZero k := hcurrent.le
          _ ≤ b.orderSequence.entryOrZero (k + 2) := hbTwoStep'
          _ = a.orderSequence.entryOrZero (k + 2) := hcommonNextNext.symm
      have hcross : c.order ⟨idx.val - 1, by
            have := idx.le_small
            omega⟩ ≤ a.order ⟨idx.val + 1, hi.2⟩ := by
        rw [← c.orderSequence_entryOrZero_eq_order
            ⟨idx.val - 1, by have := idx.le_small; omega⟩,
          ← a.orderSequence_entryOrZero_eq_order ⟨idx.val + 1, hi.2⟩]
        simpa only [idx, Nat.add_sub_cancel] using hcrossEntries
      rw [a.representationAlphaPrime_eq_min_primary_current c idx hi hcross]
        at hprime
      rcases min_le_iff.mp hprime with hprimary | hsecondary
      · exact finishPrimary hprimary
      · by_cases hpair : b.orderSequence.entryOrZero k +
              b.orderSequence.entryOrZero (k + 1) ≤
            c.orderSequence.entryOrZero (k - 1) +
              c.orderSequence.entryOrZero k
        · exact Or.inr ⟨hkPos, hkNext, by
            simpa only [BeliOrderSequence.entryOrZero_of_lt _ hk,
              BeliOrderSequence.entryOrZero_of_lt _ hkNext,
              BeliOrderSequence.entryOrZero_of_lt _
                (show k - 1 < n + 2 by omega)] using hpair⟩
        · have hsourcePairLower :
              b.orderSequence.entryOrZero k +
                  b.orderSequence.entryOrZero (k + 1) ≤
                  a.orderSequence.entryOrZero (k + 1) +
                  a.orderSequence.entryOrZero (k + 2) := by
            rw [hcommonNext, hcommonNextNext]
            omega
          have hshift : 0 <
              a.order ⟨idx.val, idx.lt_large⟩ +
                  a.order ⟨idx.val + 1, hi.2⟩ -
                c.order ⟨idx.val - 2, by have := idx.le_small; omega⟩ -
                  c.order ⟨idx.val - 1, by have := idx.le_small; omega⟩ := by
            have hshiftEntries : 0 <
                a.orderSequence.entryOrZero (k + 1) +
                    a.orderSequence.entryOrZero (k + 2) -
                  c.orderSequence.entryOrZero (k - 1) -
                    c.orderSequence.entryOrZero k := by
              omega
            rw [← a.orderSequence_entryOrZero_eq_order
                ⟨idx.val, idx.lt_large⟩,
              ← a.orderSequence_entryOrZero_eq_order
                ⟨idx.val + 1, hi.2⟩,
              ← c.orderSequence_entryOrZero_eq_order
                ⟨idx.val - 2, by have := idx.le_small; omega⟩,
              ← c.orderSequence_entryOrZero_eq_order
                ⟨idx.val - 1, by have := idx.le_small; omega⟩]
            simpa only [idx, Nat.add_sub_cancel,
              show k + 1 + 1 = k + 2 by omega,
              show k + 1 - 2 = k - 1 by omega] using hshiftEntries
          have hsourceAlpha :=
            a.representationSecondarySourceAlpha_le_of_current_le_comparison
              c idx hi C hsecondary hcomparison hshift
          have hpair' := a.lemma79_typeIII_pair_of_sourceAlpha_le_mixedShift
            b c D hfirst hinitial k hk hkPos hkNext hkNextNext hright
              hlastK heven (by simpa only [idx, C, left] using hsourceAlpha)
          exact Or.inr ⟨hkPos, hkNext, by
            simpa only [BeliOrderSequence.entryOrZero_of_lt _ hk,
              BeliOrderSequence.entryOrZero_of_lt _ hkNext,
              BeliOrderSequence.entryOrZero_of_lt _
                (show k - 1 < n + 2 by omega)] using hpair'⟩
    · rw [a.representationAlphaPrime_eq_primary_of_not_interior c idx hi]
        at hprime
      exact finishPrimary hprime

end BONG.GoodBONG

end Bong
