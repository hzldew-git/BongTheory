/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Proposition62EqualRank
import Bong.Bong.Beli2019Lemma77TypeINonterminal

/-!
# Beli (2019), Lemma 6.9(v) from representation conditions

Proposition 6.2 now supplies the `W`-sequence order that was previously an
explicit premise of the interval-rigidity layer.  The established neighboring
estimates and telescoping sum therefore prove the nonterminal type-I part of
Lemma 6.9(v) directly from conditions 2.1(i),(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Lemma 6.9(v) for a nonterminal type-I interval, with no explicit
`W(a) ≤ W(b)` premise. -/
theorem beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hleft : C.leftSwitch ≤ k)
    (hright : k < C.rightSwitch) :
    a.alphaLeftEndpoint ⟨k, by
        have hl := D.profile.lastDifference.bound
        omega⟩ =
      b.alphaLeftEndpoint ⟨k, by
        have hl := D.profile.lastDifference.bound
        omega⟩ := by
  have hW := a.weightSequence_le_of_representationConditions
    b horder hdefect
  have hstrict : C.leftSwitch < C.rightSwitch := hleft.trans_lt hright
  have hleftNeighbor : 0 < C.leftSwitch →
      b.weightSequence.entryOrZero (2 * C.leftSwitch - 1) ≤
        a.weightSequence.entryOrZero (2 * C.leftSwitch - 1) + 1 / 2 := by
    intro hleftPos
    exact beli2019Lemma69_v_typeI_leftNeighbor
      a b D C hfirst hleftPos hdefect
  have hrightNeighbor : C.rightSwitch < n + 1 →
      b.weightSequence.entryOrZero (2 * C.rightSwitch) ≤
        a.weightSequence.entryOrZero (2 * C.rightSwitch) + 1 / 2 := by
    intro _
    exact beli2019Lemma69_v_typeI_rightNeighbor
      a b D C hfirst hrightLast hdefect
  have hleftBoundary := lemma69_v_typeI_leftBoundary_of_previous
    a b D C hfirst hstrict hW hleftNeighbor
  have hrightBoundary := lemma69_v_typeI_rightBoundary_of_next
    a b D C hfirst hstrict hW hrightNeighbor
  have hsum := lemma69_v_typeI_weightSegmentSum_eq a b D C hfirst
  exact beli2019Lemma69_v_typeI_of_interval a b D C hW
    hleftBoundary hrightBoundary hsum k hleft hright

/-- The nonterminal type-I branch of Lemma 7.7, deriving Proposition 6.2
internally instead of requesting its conclusion. -/
theorem beli2019Lemma77_typeI_of_rightSwitch_lt_last_from_conditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : Nat) (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hiEven : Even i) (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 < C.rightSwitch) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  have hW := a.weightSequence_le_of_representationConditions
    b horder hdefect
  exact a.beli2019Lemma77_typeI_of_rightSwitch_lt_last b D C hfirst
    hrightLast hdefect hW i hiTwo hiBound hiEven hleft hright

end BONG.GoodBONG

end Bong
