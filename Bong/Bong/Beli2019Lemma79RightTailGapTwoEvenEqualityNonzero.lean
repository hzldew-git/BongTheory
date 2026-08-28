/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenEqualityParity
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha

/-!
# Beli (2019), Lemma 7.9(ii), case 8: nonzero alpha in the even equality branch

After the primary mixed defect vanishes, `B_i` is at most
`S_(i+1) - T_i`.  Equality in the domination coefficient rewrites this as
`1 + beta_i - gamma_(i-1)`.  A nonzero alpha invariant is at least one, so
the desired beta bound follows.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- The equality branch satisfies `B_i <= beta_i` whenever the preceding
comparison alpha is nonzero. -/
theorem caseEight_gapTwo_even_beta_bound_of_equality_primaryProduct_odd_of_alpha_ne_zero
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (j : Fin (n + 1))
    (hsource : b.order first.castSucc = c.order j.castSucc + 1)
    (hcoefficient :
      ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) =
      ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat))
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))))
    (halphaNe : c.alphaValue (evenTargetPreviousAlphaIndex i) ≠ 0) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  apply WithTop.coe_le_coe.mpr
  have hprimary :=
    representationAlphaValue_le_order_sub_of_primaryProduct_odd
      b c i (c.order (evenTargetPreviousIndex i)) hodd le_rfl
  have hcoefficientQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) =
        ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first := by
    exact_mod_cast hcoefficient
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hsourceQ : (b.order first.castSucc : Rat) =
      (c.order j.castSucc : Rat) + 1 := by
    exact_mod_cast hsource
  have halphaOne := c.one_le_alphaValue_of_ne_zero
    (evenTargetPreviousAlphaIndex i) halphaNe
  push_cast at hprimary hcoefficientQ hcentral hsourceQ ⊢
  linarith

end BONG.GoodBONG

end Bong
