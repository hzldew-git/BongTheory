/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenBoundaryAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 3: complete type-II/III left interval

Two even coordinates differ by an even amount.  Hence an even coordinate
through the last left-profile coordinate is either at least two positions
before it, or is the transition coordinate itself.  The interior and
boundary theorems therefore cover the complete type-II and type-III case 3.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), case 3, on the complete even type-II left interval. -/
theorem beli2019Lemma79_ii_typeII_even_left
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := ⟨by omega, hiNext⟩
  by_cases hfar : i.val + 2 ≤ D.outer.transition.lastZero
  · exact beli2019Lemma79_ii_typeII_even_left_interior
      a b c D hfirst hdefectAB hdefectAC horderBC hnorm
        i hi hiEven hfar
  · have hlastEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    have hboundary : i.val = D.outer.transition.lastZero := by omega
    exact beli2019Lemma79_ii_typeII_even_leftBoundary
      a b c D hfirst hdefectAC horderBC hnorm
        i hi ⟨d, hd⟩ hboundary

/-- Lemma 7.9(ii), case 3, on the complete even type-III left interval. -/
theorem beli2019Lemma79_ii_typeIII_even_left
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
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
    (hdefectAC : a.RepresentationDefectCondition c)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hi : 1 < i.val ∧ i.val + 1 < n + 2 := ⟨by omega, hiNext⟩
  by_cases hfar : i.val + 2 ≤ D.outer.transition.lastZero
  · exact beli2019Lemma79_ii_typeIII_even_left_interior
      a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial hdefectAC horderBC hnorm i hi hiEven hfar
  · have hlastEven := D.outer.left_even_of_first_eq_zero hfirst
    rcases hiEven with ⟨d, hd⟩
    rcases hlastEven with ⟨e, he⟩
    have hboundary : i.val = D.outer.transition.lastZero := by omega
    exact beli2019Lemma79_ii_typeIII_even_leftBoundary
      a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
        hinitial hdefectAC horderBC hnorm i hi ⟨d, hd⟩ hboundary

end BONG.GoodBONG

end Bong
