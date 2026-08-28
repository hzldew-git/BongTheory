/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapCaseSixInterior
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrder
import Bong.Bong.Beli2019Lemma79CaseSixFirstParity

/-!
# Beli (2019), Lemma 7.9(ii), overlapping case 6: first parity

The zero-third-alpha branch follows from the overlapping form of condition
2.1(i); the positive branch is the candidate estimate proved in the preceding
module.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The zero-third-alpha subcase in the overlapping type-III case-6
interval. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last)
    (hgamma : c.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiNext : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  have hcompare := a.beli2019Lemma79_i_typeIII_overlap_nonterminal
    b c D hfirst hac hdefectAC hoverlap hnorm
      i.val i.lt_large hiNext hbeforeLast.le
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

set_option maxHeartbeats 7000000 in
/-- The complete first comparison-prefix parity branch in nonterminal
overlapping type-III case 6. -/
theorem beli2019Lemma79_typeIII_overlap_caseSix_firstParity
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hoverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ = 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hbeforeLast : i.val < D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hbcEven : Even
      (ordUnit K (b.prefixProduct i.val * c.prefixProduct i.val)))
    (hacOdd : Odd
      (ordUnit K (a.prefixProduct i.val * c.prefixProduct i.val))) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  by_cases hgamma : (1 : ℚ) ≤ c.alphaValue previous
  · exact beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_ge_one
      a b c D hfirst hlast hab hdefectAB hdefectAC htotal hoverlap
        i hright hbeforeLast heven
          (by simpa only [previous] using hgamma) hbcEven hacOdd
  · have hgammaZero : c.alphaValue previous = 0 := by
      by_contra hne
      exact hgamma (c.one_le_alphaValue_of_ne_zero previous hne)
    exact beli2019Lemma79_typeIII_overlap_caseSix_firstParity_of_gamma_eq_zero
      a b c D hfirst hlast hac hdefectAC hoverlap hnorm i hbeforeLast
        (by simpa only [previous] using hgammaZero)

end BONG.GoodBONG

end Bong
