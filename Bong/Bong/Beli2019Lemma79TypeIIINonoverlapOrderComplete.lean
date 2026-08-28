/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal
import Bong.Bong.Beli2019Lemma79TypeIIINonoverlapOrderTerminal

/-!
# Beli (2019), Lemma 7.9(i): complete nonoverlapping type III

The local interior proof, the proper-suffix terminal-switch proof, and the
full-rank determinant-defect endpoint cover every coordinate through the
last difference.  The unchanged suffix then gives the complete order
condition without a full-span assumption.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at every altered coordinate of a normalized,
nonoverlapping type-III profile. -/
theorem beli2019Lemma79_i_typeIII_nonoverlap
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
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
    (k : Nat) (hk : k < n + 2) (hlastK : k ≤ D.outer.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hkNext : k + 1 < n + 2
  · exact a.beli2019Lemma79_i_typeIII_nonterminal
      b c D hfirst horderAC hdefectAB hdefectAC hnotOverlap hinitial
        hnorm k hk hkNext hlastK
  · left
    have hkFinal : k = n + 1 := by omega
    have hlastFull : D.outer.last = n + 1 := by
      have hlastBound := D.outer.lastDifference.bound
      omega
    have hterminal := a.beli2019Lemma79_i_typeIII_nonoverlap_terminal
      b c D hfirst hlastFull hdefectAB hnotOverlap hinitial hnorm
    simpa only [hkFinal] using hterminal

/-- The complete order condition in the nonoverlapping type-III branch. -/
theorem beli2019Lemma79_i_typeIII_nonoverlap_orderCondition
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp horderAC
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  exact BeliOrderLE.of_compare_through_lastDifference
    hacSequence D.outer.lastDifference
      (a.beli2019Lemma79_i_typeIII_nonoverlap
        b c D hfirst horderAC hdefectAB hdefectAC hnotOverlap
          hinitial hnorm)

/-- Condition 2.1(i) at every coordinate of a normalized full-span,
nonoverlapping type-III profile. -/
theorem beli2019Lemma79_i_typeIII_nonoverlap_fullSpan
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (k : Nat) (hk : k < n + 2) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hlastK : k = D.outer.last
  · left
    have hterminal := a.beli2019Lemma79_i_typeIII_nonoverlap_terminal
      b c D hfirst hlast hdefectAB hnotOverlap hinitial hnorm
    simpa only [hlastK, hlast] using hterminal
  · have hkNext : k + 1 < n + 2 := by omega
    have hkLast : k ≤ D.outer.last := by omega
    exact a.beli2019Lemma79_i_typeIII_nonterminal
      b c D hfirst horderAC hdefectAB hdefectAC hnotOverlap hinitial
        hnorm k hk hkNext hkLast

/-- The complete full-span order condition in the nonoverlapping type-III
branch. -/
theorem beli2019Lemma79_i_typeIII_nonoverlap_fullSpan_orderCondition
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  refine { rank := le_rfl, compare := ?_ }
  intro i hi
  exact a.beli2019Lemma79_i_typeIII_nonoverlap_fullSpan
    b c D hfirst hlast horderAB horderAC hdefectAB hdefectAC htotal
      hnotOverlap hinitial hnorm i hi

end BONG.GoodBONG

end Bong
