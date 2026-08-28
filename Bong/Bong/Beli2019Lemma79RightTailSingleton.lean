/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailBetaProfile

/-!
# Beli (2019), Lemma 7.9(ii), case 8: singleton strict tails

When the representation boundary is the last changed coordinate, the beta
tail consists of one boundary.  The interval propagation lemma deliberately
handles only distinct endpoints, so this file supplies the reflexive case.
The strict half-gap hypothesis still gives exactly the same odd, positive,
sub-`2e`, and local-formula profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- A one-boundary tail has the complete strict case-8 beta profile as
soon as its alpha is strictly below its half-gap. -/
theorem caseEight_strictBetaSingletonConsequences
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (j : Fin (n + 1))
    (hstrict : b.alphaValue j < b.halfGapValue j) :
    CaseEightStrictBetaTailConsequences b j j := by
  have hodd : IsOddRationalInteger (b.alphaValue j) :=
    b.beli2009Lemma27_iv j (ne_of_lt hstrict)
  have htwoE :
      b.alphaValue j < 2 * (ramificationIndex K : Rat) := by
    have hgap : b.orderGap j < 2 * (ramificationIndex K : Int) := by
      by_contra hnot
      have hlarge : 2 * (ramificationIndex K : Int) <= b.orderGap j :=
        le_of_not_gt hnot
      have heq := b.beli2009Lemma27_ii j hlarge
      exact (ne_of_lt hstrict) heq
    exact (b.beli2009Corollary28_ii j).1.mpr hgap
  have H : CaseEightBetaTailConsequences b j j := by
    refine
      { rightEndpoint_eq := ?_
        value_eq := ?_
        order_modEq := ?_
        alpha_modEq := ?_
        alpha_le := ?_
        gap_le := ?_ }
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      rfl
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      push_cast
      ring
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      exact Int.ModEq.rfl
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      exact RationalModEqTwo.refl hodd.isRationalInteger
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      exact htwoE.le
    · intro k hjk hkj
      have hk : k = j := le_antisymm hkj hjk
      subst k
      exact (b.alphaValue_le_twoE_iff_orderGap_le_twoE j).mp htwoE.le
  exact caseEight_strictBetaTailConsequences b j j H hstrict

end BONG.GoodBONG

end Bong
