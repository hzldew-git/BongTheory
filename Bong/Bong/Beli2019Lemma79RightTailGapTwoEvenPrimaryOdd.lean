/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenNonintegralOrders
import Bong.Bong.Beli2019Lemma79RightTailGapOneBounds

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the exceptional primary product

In the exceptional even branch the boundary alpha is exactly its odd order
gap.  Hence the common coefficient on the case-8 beta tail is zero.  If the
signed mixed primary product has odd order, its defect vanishes and the
representation alpha is bounded by `S_(i+1) - T_i`.  Once `T_i` is at least
the first tail order, this is precisely at most `beta_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- In the odd-primary-product alternative of the exceptional even branch,
the case-8 boundary identity converts the primary estimate into
`B_i <= beta_i`. -/
theorem caseEight_gapTwo_even_beta_bound_of_primaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (hboundary : b.alphaValue first = (b.orderGap first : Rat))
    (hcomparison : b.order first.castSucc <=
      c.order (evenTargetPreviousIndex i))
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1)))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  apply WithTop.coe_le_coe.mpr
  have hprimary :=
    representationAlphaValue_le_order_sub_of_primaryProduct_odd
      b c i (b.order first.castSucc) hodd hcomparison
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hgap : b.orderGap first =
      b.order first.succ - b.order first.castSucc := by
    rfl
  rw [hboundary, hgap] at hcentral
  push_cast at hcentral hprimary ⊢
  linarith

end BONG.GoodBONG

end Bong
