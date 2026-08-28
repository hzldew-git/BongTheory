/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTargetHalfGap
import Bong.Bong.Beli2019Lemma79OrderTypeIIComplete
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal

/-!
# Beli (2019), Lemma 7.9(ii), case 6: zero third alpha

The local order comparison supplied by condition 2.1(i) bounds the
representation alpha by the target self half-gap.  When the target alpha
vanishes, P2 makes that half-gap zero, proving condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The zero-gamma subcase in the type-II case-6 interval. -/
theorem beli2019Lemma79_typeII_caseSix_firstParity_of_gamma_eq_zero
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last)
    (hgamma : c.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiNext : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  have hcompare := a.beli2019Lemma79_i_typeII
    b c D hfirst hac hdefectAC hnorm i.val i.lt_large hbeforeLast.le
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

/-- The zero-gamma subcase in the nonoverlapping type-III case-6
interval. -/
theorem beli2019Lemma79_typeIII_caseSix_firstParity_of_gamma_eq_zero
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (hab : a.RepresentationOrderCondition b le_rfl)
    (hac : a.RepresentationOrderCondition c le_rfl)
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
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbeforeLast : i.val < D.outer.last)
    (hgamma : c.alphaValue ⟨i.val - 1, by omega⟩ = 0) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hiNext : i.val + 1 < n + 2 := by
    rw [hlast] at hbeforeLast
    omega
  have hcompare := a.beli2019Lemma79_i_typeIII_nonterminal
    b c D hfirst hac hdefectAB hdefectAC hnotOverlap
      hinitial hnorm i.val i.lt_large hiNext hbeforeLast.le
  exact lemma79_caseSix_of_gamma_eq_zero_and_compare
    b c i hiNext hcompare hgamma

end BONG.GoodBONG

end Bong
