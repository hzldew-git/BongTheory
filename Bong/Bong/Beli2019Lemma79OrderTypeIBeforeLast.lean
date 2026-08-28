/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeICentralEndpoint
import Bong.Bong.Beli2019Lemma79OrderTypeILeftBoundarySource
import Bong.Bong.Beli2019Lemma79OrderTypeIOuter
import Bong.Bong.Beli2019Lemma79OrderTypeIRight

/-!
# Beli (2019), Lemma 7.9(i): all nonterminal type-I coordinates

The elementary outer classes, the exceptional left predecessor, and the
endpoint-complete central class cover every coordinate strictly before the
last unequal order.  Only the last unequal coordinate remains separate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) at every type-I coordinate strictly before the last
unequal order. -/
theorem beli2019Lemma79_i_typeI_beforeLast
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.anchor_bound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (k : Nat) (hk : k < n + 2) (hlast : k < D.profile.last) :
    b.orderSequence.entry k hk ≤ c.orderSequence.entry k hk ∨
      ∃ (hk0 : 0 < k) (hkNext : k + 1 < n + 2),
        b.orderSequence.entry k hk +
            b.orderSequence.entry (k + 1) hkNext ≤
          c.orderSequence.entry (k - 1) (by omega) +
            c.orderSequence.entry k hk := by
  by_cases hleft : k < C.leftSwitch
  · rcases Nat.even_or_odd k with hkEven | hkOdd
    · exact beli2019Lemma79_i_typeI_leftEven
        a b c D C hnorm k hk hkEven hleft
    · by_cases hstrict : k + 1 < C.leftSwitch
      · exact beli2019Lemma79_i_typeI_leftOdd
          a b c D C hfirst horderAC k hk hkOdd hstrict
      · have hleftPos : 0 < C.leftSwitch := by omega
        have hkEq : k = C.leftSwitch - 1 := by omega
        subst k
        simpa only using beli2019Lemma79_i_typeI_leftPredecessor
          a b c D C hfirst hleftPos horderAB horderAC hdefectAB
            hdefectAC hnorm
  · have hleft' : C.leftSwitch ≤ k := Nat.le_of_not_gt hleft
    by_cases hright : k < C.rightSwitch
    · rcases Nat.even_or_odd k with hkEven | hkOdd
      · have hkNext : k + 1 < n + 2 :=
          (Nat.succ_le_of_lt hright).trans_lt
            (C.right_le_last.trans_lt D.profile.lastDifference.bound)
        have hkTwo : k + 2 < n + 2 := by
          have htwoRight : k + 2 ≤ C.rightSwitch := by
            rcases hkEven with ⟨d, hd⟩
            rcases C.right_even with ⟨e, he⟩
            omega
          exact htwoRight.trans_lt
            (C.right_le_last.trans_lt D.profile.lastDifference.bound)
        exact beli2019Lemma79_i_typeI_centralEven_complete
          a b c D C hfirst horderAB hdefectAB hdefectAC hinitial hnorm
            k hk hkNext hkTwo hkEven hleft' hlast.le hright
      · exact beli2019Lemma79_i_typeI_middleOdd
          a b c D C hfirst horderAC k hk hkOdd hleft' hright
    · have hright' : C.rightSwitch ≤ k := Nat.le_of_not_gt hright
      rcases Nat.even_or_odd k with hkEven | hkOdd
      · have hrightLast : C.rightSwitch < D.profile.last :=
          hright'.trans_lt hlast
        have hkNext : k + 1 < n + 2 :=
          (Nat.succ_le_of_lt hlast).trans_lt
            D.profile.lastDifference.bound
        have hanchorEven : Even D.anchor := by
          by_cases heq : D.profile.first = D.anchor
          · rw [← heq, hfirst]
            exact ⟨0, by omega⟩
          · have hlt : D.profile.first < D.anchor :=
              lt_of_le_of_ne D.profile.first_le_anchor heq
            simpa only [hfirst, Nat.sub_zero] using
              (D.profile.leftProfile hlt).1
        have hlastDistance : Even (D.profile.last - D.anchor) :=
          (D.profile.rightProfile
            (C.anchor_le_right.trans_lt hrightLast)).1
        have hlastEven : Even D.profile.last := by
          rcases hlastDistance with ⟨d, hd⟩
          rcases hanchorEven with ⟨e, he⟩
          exact ⟨e + d, by
            have hanchorLast := C.anchor_le_right.trans_lt hrightLast
            omega⟩
        have hkTwo : k + 2 < n + 2 := by
          have htwoLast : k + 2 ≤ D.profile.last := by
            rcases hkEven with ⟨d, hd⟩
            rcases hlastEven with ⟨e, he⟩
            omega
          exact htwoLast.trans_lt D.profile.lastDifference.bound
        exact beli2019Lemma79_i_typeI_rightEven
          a b c D C hfirst hrightLast hdefectAB hdefectAC hinitial hnorm
            k hk hkNext hkTwo hkEven hleft' hright' hlast
      · have hrightStrict : C.rightSwitch < k := by
          rcases C.right_even with ⟨d, hd⟩
          rcases hkOdd with ⟨e, he⟩
          omega
        exact beli2019Lemma79_i_typeI_rightOdd
          a b c D C hfirst horderAC k hk hkOdd hrightStrict hlast

end BONG.GoodBONG

end Bong
