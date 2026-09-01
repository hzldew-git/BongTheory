/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalEndpoint

/-!
# Ambient consequence of Beli's universal-lattice criterion

This file closes the low-rank case split in the last paragraph of the proof
of Theorem 2.1.  Either alternative in the theorem forces the ambient
quadratic space to represent every nonzero line.  The rank-three endpoint
in Case I uses Lemma 2.11; the rank-three branch in Case II uses Lemma 2.8
and the boundary clause II(c).
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Case I in Theorem 2.1 forces ambient line-universality. -/
theorem UniversalCaseI.isLineUniversal {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseI a)
    (hzero : a.order 0 = 0) :
    q.IsLineUniversal := by
  by_cases hfour : 2 ≤ tail
  · exact a.isLineUniversal_of_two_le_tail hfour
  by_cases hrankTwo : tail = 0
  · exact a.isLineUniversal_of_firstTwoIsotropic
      (h.binaryRankTwo hrankTwo)
  have hrankThree : tail = 1 := by omega
  subst tail
  have hthree : 0 < (1 : Nat) := by omega
  have hnonnegative : 0 ≤ a.order (2 : Fin 3) :=
    a.order_two_nonnegative_of_order_zero_eq_zero hzero
  by_cases habove : 1 < a.order (2 : Fin 3)
  · exact a.isLineUniversal_of_firstTwoIsotropic
      (h.binaryAboveOne hthree habove)
  by_cases hatOne : a.order (2 : Fin 3) = 1
  · exact a.isLineUniversal_of_firstTwoIsotropic
      (h.binaryAtOne hthree hatOne (Or.inl rfl))
  have hthird : a.order (2 : Fin 3) = 0 := by omega
  have hsecond := h.order_one_eq_neg_two_e hzero
  have hisotropic :=
    a.firstThree_isotropic_of_endpoint_order_two_zero
      (tail := 0) hzero hsecond hthird
  exact a.isLineUniversal_of_firstThreeIsotropic hthree hisotropic

/-- Case II in Theorem 2.1 forces ambient line-universality. -/
theorem UniversalCaseII.isLineUniversal {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseII a)
    (hzero : a.order 0 = 0) :
    q.IsLineUniversal := by
  by_cases hfour : 2 ≤ tail
  · exact a.isLineUniversal_of_two_le_tail hfour
  have hrankThree : tail = 1 := by
    have hpositive := h.rankAtLeastThree
    omega
  subst tail
  have hthree : 0 < (1 : Nat) := by omega
  have hnotLarge : ¬ (a.order (1 : Fin 3) = 1 ∨
      1 < a.order (2 : Fin 3)) := by
    intro hlarge
    have := h.no_rank_three_large_branch hlarge
    omega
  have hsecondNe : a.order (1 : Fin 3) ≠ 1 := by
    intro hsecond
    exact hnotLarge (Or.inl hsecond)
  have hthirdLe : a.order (2 : Fin 3) ≤ 1 := by
    by_contra hnot
    exact hnotLarge (Or.inr (by omega))
  have hgapCases :=
    (a.alphaValue_eq_one_consequences (0 : Fin 2) h.alphaOne).2.1
  have hgap : a.orderGap (0 : Fin 2) = a.order (1 : Fin 3) := by
    unfold orderGap
    change a.order (1 : Fin 3) - a.order (0 : Fin 3) =
      a.order (1 : Fin 3)
    rw [hzero]
    omega
  rw [hgap] at hgapCases
  have hsecondLe : a.order (1 : Fin 3) ≤ 0 := by
    rcases hgapCases with hone | hnonpositive
    · exact False.elim (hsecondNe hone)
    · exact hnonpositive.2.2
  have hisotropic :=
    h.ternaryBoundary hsecondLe hthirdLe (Or.inl rfl)
  exact a.isLineUniversal_of_firstThreeIsotropic hthree hisotropic

/-- The right-hand side of Theorem 2.1 includes the ambient universality
needed by the representation reduction in Lemma 2.3. -/
theorem UniversalTheorem21Conditions.isLineUniversal {tail : Nat}
    {a : GoodBONG q L (tail + 2)}
    (h : UniversalTheorem21Conditions a) :
    q.IsLineUniversal := by
  rcases h.2 with hI | hII
  · exact hI.isLineUniversal h.1
  · exact hII.isLineUniversal h.1

end BONG.GoodBONG

end Bong
