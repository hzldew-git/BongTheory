/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderLeftOuter

/-!
# Beli (2019), Lemma 7.9(i): the right alternating interval

On the right outer interval of a type-II or type-III profile, entries whose
distance from the right transition is odd have source order one above target
order, while their following adjacent sums agree.  This is case 2 in the
paper's proof of condition 2.1(i).
-/

namespace Bong

namespace BeliOrderLE.NoGapTwoOuterConsequences

variable {n : Nat}
  {x y : BeliOrderSequence n Int}

/-- The last difference has even distance from the right transition. -/
theorem right_even_distance (O : NoGapTwoOuterConsequences x y) :
    Even (O.last - (O.transition.firstTwo - 1)) := by
  by_cases heq : O.transition.firstTwo - 1 = O.last
  · rw [← heq]
    exact ⟨0, by omega⟩
  · have hlt : O.transition.firstTwo - 1 < O.last :=
      lt_of_le_of_ne O.right_le_last heq
    exact (O.rightProfile hlt).1

/-- Target entries at even distance from the right transition all equal the
target boundary entry. -/
theorem target_rightEven_eq_boundary
    (O : NoGapTwoOuterConsequences x y) (k : Nat)
    (hright : O.transition.firstTwo - 1 ≤ k) (hk : k ≤ O.last)
    (heven : Even (k - (O.transition.firstTwo - 1))) :
    y.entryOrZero k =
      y.entryOrZero (O.transition.firstTwo - 1) := by
  by_cases heq : O.transition.firstTwo - 1 = O.last
  · have hkEq : k = O.transition.firstTwo - 1 := by omega
    rw [hkEq]
  · have hlt : O.transition.firstTwo - 1 < O.last :=
      lt_of_le_of_ne O.right_le_last heq
    have hp := O.rightProfile hlt
    rcases hp.1 with ⟨d, hd⟩
    rcases heven with ⟨e, he⟩
    have hlastK : Even (O.last - k) := ⟨d - e, by omega⟩
    have hkValue := hp.2.2 k hright hk hlastK
    have hrightValue := hp.2.2 (O.transition.firstTwo - 1)
      le_rfl O.right_le_last ⟨d, hd⟩
    exact hkValue.trans hrightValue.symm

/-- The source orders at the right boundary and last difference agree. -/
theorem source_rightBoundary_eq_last
    (O : NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2) :
    x.entryOrZero (O.transition.firstTwo - 1) =
      x.entryOrZero O.last := by
  by_cases heq : O.transition.firstTwo - 1 = O.last
  · rw [heq]
  · have hlt : O.transition.firstTwo - 1 < O.last :=
      lt_of_le_of_ne O.right_le_last heq
    have hp := O.rightProfile hlt
    have hlastUpper := hnoTwo O.last O.lastDifference.bound
    have hlastGap : y.entryOrZero O.last = x.entryOrZero O.last + 1 := by
      omega
    have htarget := O.target_rightEven_eq_boundary O.last
      O.right_le_last le_rfl hp.1
    have hboundary := O.transition.rightBoundary
    omega

/-- Source entries at even distance from the right transition all equal the
source boundary entry. -/
theorem source_rightEven_eq_boundary
    (O : NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hright : O.transition.firstTwo - 1 ≤ k)
    (hk : k ≤ O.last)
    (heven : Even (k - (O.transition.firstTwo - 1))) :
    x.entryOrZero k =
      x.entryOrZero (O.transition.firstTwo - 1) := by
  have hrightBound : O.transition.firstTwo - 1 < n := by
    have hfirstTwoBound := O.transition.firstTwo_le_rank
    have hseparated := O.transition.separated
    omega
  have hkBound : k < n := hk.trans_lt O.lastDifference.bound
  have hrightK := x.entryOrZero_le_of_evenGap
    (O.transition.firstTwo - 1) k hright hkBound heven
  rcases O.right_even_distance with ⟨d, hd⟩
  rcases heven with ⟨e, he⟩
  have hlastKParity : Even (O.last - k) := ⟨d - e, by omega⟩
  have hkLast := x.entryOrZero_le_of_evenGap k O.last
    hk O.lastDifference.bound hlastKParity
  have hendpoint := O.source_rightBoundary_eq_last hnoTwo
  exact le_antisymm (hkLast.trans_eq hendpoint.symm) hrightK

/-- At odd distance from the right transition, the source entry is one
above the target entry. -/
theorem source_rightOdd_eq_target_add_one
    (O : NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hright : O.transition.firstTwo - 1 ≤ k)
    (hk : k ≤ O.last)
    (hodd : Odd (k - (O.transition.firstTwo - 1))) :
    x.entryOrZero k = y.entryOrZero k + 1 := by
  rcases hodd with ⟨d, hd⟩
  have hfirstTwoPos : 0 < O.transition.firstTwo := by
    have hseparated := O.transition.separated
    omega
  have hfirst : O.transition.firstTwo ≤ k := by omega
  have hpairParity : Even (k - O.transition.firstTwo) := by
    refine ⟨d, ?_⟩
    omega
  rcases O.right_even_distance with ⟨e, he⟩
  have hkStrict : k < O.last := by omega
  have hpair := O.rightPairEq k hfirst (by
    have hlastBound := O.lastDifference.bound
    omega) hpairParity
  have hnextEven : Even
      (k + 1 - (O.transition.firstTwo - 1)) := ⟨d + 1, by omega⟩
  have hsourceNext := O.source_rightEven_eq_boundary hnoTwo
    (k + 1) (by omega) (by omega) hnextEven
  have htargetNext := O.target_rightEven_eq_boundary
    (k + 1) (by omega) (by omega) hnextEven
  have hboundary := O.transition.rightBoundary
  omega

/-- Adjacent source and target sums agree at odd distance from the right
transition. -/
theorem rightOdd_pair_eq
    (O : NoGapTwoOuterConsequences x y) (k : Nat)
    (hright : O.transition.firstTwo - 1 ≤ k) (hk : k ≤ O.last)
    (hodd : Odd (k - (O.transition.firstTwo - 1))) :
    x.entryOrZero k + x.entryOrZero (k + 1) =
      y.entryOrZero k + y.entryOrZero (k + 1) := by
  rcases hodd with ⟨d, hd⟩
  have hfirstTwoPos : 0 < O.transition.firstTwo := by
    have hseparated := O.transition.separated
    omega
  have hfirst : O.transition.firstTwo ≤ k := by omega
  have hpairParity : Even (k - O.transition.firstTwo) := by
    refine ⟨d, ?_⟩
    omega
  rcases O.right_even_distance with ⟨e, he⟩
  exact O.rightPairEq k hfirst (by
    have hlastBound := O.lastDifference.bound
    omega) hpairParity

end BeliOrderLE.NoGapTwoOuterConsequences

namespace BeliOrderLE

/-- The old order comparison transports at every right-outer coordinate
whose distance from the transition is odd. -/
theorem compare_rightAlternating {n : Nat}
    {x y z : BeliOrderSequence n Int} (hxz : BeliOrderLE x z)
    (O : NoGapTwoOuterConsequences x y)
    (hnoTwo : ∀ k, k < n → y.entryOrZero k < x.entryOrZero k + 2)
    (k : Nat) (hk : k < n)
    (hright : O.transition.firstTwo - 1 ≤ k) (hlast : k ≤ O.last)
    (hodd : Odd (k - (O.transition.firstTwo - 1))) :
    y.entry k hk ≤ z.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n),
        y.entry k hk + y.entry (k + 1) hkNext ≤
          z.entry (k - 1) (by omega) + z.entry k hk := by
  have hcurrentEq := O.source_rightOdd_eq_target_add_one
    hnoTwo k hright hlast hodd
  have hpairEq := O.rightOdd_pair_eq k hright hlast hodd
  apply compare_of_source_bounds hxz k hk
  · omega
  · exact le_of_eq hpairEq.symm

end BeliOrderLE

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Case 2 of Lemma 7.9(i) for a type-II profile. -/
theorem beli2019Lemma79_i_typeII_rightAlternating
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hk : k < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  exact BeliOrderLE.compare_rightAlternating hacSequence D.outer
    D.no_gap_two k hk hright hlast hodd

/-- Case 2 of Lemma 7.9(i) for a type-III profile. -/
theorem beli2019Lemma79_i_typeIII_rightAlternating
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (k : Nat) (hk : k < n + 2)
    (hright : D.outer.transition.firstTwo - 1 ≤ k)
    (hlast : k ≤ D.outer.last)
    (hodd : Odd (k - (D.outer.transition.firstTwo - 1))) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  exact BeliOrderLE.compare_rightAlternating hacSequence D.outer
    D.no_gap_two k hk hright hlast hodd

end BONG.GoodBONG

end Bong
