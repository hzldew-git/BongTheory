/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrderTerminal

/-!
# Beli (2019), Lemma 7.9(i): complete overlapping type-III branch

The existing pointwise theorem covers every coordinate with a successor.
The determinant-parity endpoint theorem covers the final coordinate.  The
unchanged suffix after the last difference then yields the complete order
condition.
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

/-- Condition 2.1(i) at every altered coordinate of an overlapping type-III
profile. -/
theorem beli2019Lemma79_i_typeIII_overlap
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
    (k : Nat) (hk : k < n + 2) (hlast : k ≤ D.outer.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hkNext : k + 1 < n + 2
  · exact a.beli2019Lemma79_i_typeIII_overlap_nonterminal
      b c D hfirst hac hdefectAC hoverlap hnorm k hk hkNext hlast
  · left
    have hlastEq : k = D.outer.last := by
      have hlastBound := D.outer.lastDifference.bound
      omega
    have hright : D.outer.transition.firstTwo - 1 ≤ k :=
      D.outer.right_le_last.trans_eq hlastEq.symm
    have heven : Even
        (k - (D.outer.transition.firstTwo - 1)) := by
      rw [hlastEq]
      exact D.outer.right_even_distance
    exact a.beli2019Lemma79_i_typeIII_overlap_terminal
      b c D hfirst hoverlap hnorm k (by omega) hright hlast heven

/-- The complete order condition for the overlapping type-III branch. -/
theorem beli2019Lemma79_i_typeIII_overlap_orderCondition
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
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    b.RepresentationOrderCondition c le_rfl := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  exact BeliOrderLE.of_compare_through_lastDifference
    hacSequence D.outer.lastDifference
      (a.beli2019Lemma79_i_typeIII_overlap
        b c D hfirst hac hdefectAC hoverlap hnorm)

end BONG.GoodBONG

end Bong
