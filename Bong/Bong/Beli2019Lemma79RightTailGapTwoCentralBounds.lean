/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeIStrictPrefix
import Bong.Bong.Beli2019Lemma79RightTailGapTwoCentralDefect

/-!
# Beli (2019), Lemma 7.9(ii), case 8: central coefficient bounds

The coefficient `S_u - S_(u+1) + beta_u` is strictly below `2e`.
The point is slightly stronger than the individual inequality
`beta_u < (S_(u+1) - S_u) / 2 + e`: the lower good-BONG gap bound and
positivity of `beta_u` rule out equality at the endpoint.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- The paper's central coefficient is strictly below `2e`. -/
theorem CaseEightStrictBetaTailConsequences.centralCoefficient_lt_twoE
    [Beli2006AlphaLaws.{u, v} K]
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightStrictBetaTailConsequences b first last)
    (hfirstLast : first ≤ last) :
    ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first <
      2 * (ramificationIndex K : Rat) := by
  have hhalf := H.alpha_lt_halfGap first le_rfl hfirstLast
  have hpos := H.alpha_pos first le_rfl hfirstLast
  have hgapLower := b.orderGap_ge_neg_two_mul_e first
  unfold halfGapValue orderGap at hhalf hgapLower
  push_cast at hhalf hgapLower ⊢
  linarith

end BONG.GoodBONG

end Bong
