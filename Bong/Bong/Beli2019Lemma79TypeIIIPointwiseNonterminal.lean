/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenLeftComplete
import Bong.Bong.Beli2019Lemma79DefectTypeIIIOdd
import Bong.Bong.Beli2019Lemma79CaseSixAssembly
import Bong.Bong.Beli2019Lemma79TypeIIIRight

/-!
# Beli (2019), Lemma 7.9(ii): nonterminal nonoverlapping type III

For a type-III profile the left transition and the alternating right profile
are adjacent.  Consequently cases 2 and 3 meet cases 6 and 7 directly, with
no type-II constant core between them.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 9000000 in
-- Adjacency turns every coordinate after the left profile into one of the
-- two right-profile parity classes.
/-- Lemma 7.9(ii) before the last difference in nonoverlapping type III. -/
theorem beli2019Lemma79_ii_typeIII_pointwise_beforeLast_of_nonoverlap
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0) (hlast : D.outer.last = n + 1)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (horderAC : a.RepresentationOrderCondition c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
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
    (hbeforeLast : i.val < D.outer.last) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  by_cases hleft : i.val ≤ D.outer.transition.lastZero
  · rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · have hiTwo : 2 ≤ i.val := by
        rcases hiEven with ⟨d, hd⟩
        have hiPos := i.pos
        omega
      have hiNext : i.val + 1 < n + 2 := by omega
      exact beli2019Lemma79_ii_typeIII_even_left
        a b c D hfirst hlast horderAB hdefectAB htotal hnotOverlap
          hinitial hdefectAC horderBC hnorm i hiTwo hiNext hiEven hleft
    · exact beli2019Lemma79_ii_typeIII_odd_left
        a b c D hfirst hlast horderAB horderAC hdefectAB htotal hnorm
          i hiOdd (by omega)
  · have hright : D.outer.transition.firstTwo - 1 ≤ i.val := by
      rw [D.adjacent]
      omega
    rcases Nat.even_or_odd
        (i.val - (D.outer.transition.firstTwo - 1)) with hiEven | hiOdd
    · exact beli2019Lemma79_ii_typeIII_caseSix
        a b c D hfirst hlast horderAB horderAC hdefectAB hdefectAC
          htotal hnotOverlap hinitial hnorm i hright hbeforeLast hiEven
    · have hrightStrict : D.outer.transition.firstTwo ≤ i.val := by
        rcases hiOdd with ⟨d, hd⟩
        omega
      exact beli2019Lemma79_ii_typeIII_caseSeven
        a b c D hfirst hlast horderAB hdefectAB hdefectAC htotal
          hnotOverlap hinitial hnorm i hrightStrict hbeforeLast hiOdd

end BONG.GoodBONG

end Bong
