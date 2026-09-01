/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalLong
import Bong.Bong.BeliUniversalAmbientCriterion

/-!
# Beli's universal-lattice criterion

This file assembles Lemmas 2.2, 2.3, 2.5, 2.10, 2.13, and 2.14 into
Theorem 2.1.  The first step removes the temporary sharp-defect clause from
Case II(a') by deriving it from II(a) and II(b), exactly as in the final
paragraph of Beli's proof.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The temporary sharp-defect clause II(a') follows from the published
clauses II(a) and II(b). -/
theorem UniversalCaseII.toCaseIIPrime {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseII a)
    (hzero : a.order 0 = 0) : a.UniversalCaseIIPrime := by
  have htailNe : tail ≠ 0 := Nat.ne_of_gt h.rankAtLeastThree
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
  refine ⟨h.rankAtLeastThree, h.alphaOne, ?_⟩
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hconsequences :=
    a.alphaValue_eq_one_consequences (0 : Fin (m + 2)) h.alphaOne
  by_cases hnotEndpoint :
      a.orderGap (0 : Fin (m + 2)) ≠
        2 - 2 * (ramificationIndex K : Int)
  · exact hconsequences.2.2.2 hnotEndpoint
  · have hsecond : a.order 1 =
        2 - 2 * (ramificationIndex K : Int) := by
      rw [← hgapZero]
      exact not_ne_iff.mp hnotEndpoint
    have hthirdNonnegative : 0 ≤ a.order 2 :=
      a.order_two_nonnegative_of_order_zero_eq_zero hzero
    have hthirdUpper : a.order 2 ≤ 1 := by
      by_contra hnot
      have hthirdLarge : 1 < a.order ⟨2, by omega⟩ := by
        have hindex : a.order ⟨2, by omega⟩ = a.order 2 := by
          congr 1
        rw [hindex]
        omega
      obtain ⟨hfour, halpha⟩ := h.alphaThreeBound (Or.inr hthirdLarge)
      have hindexOne : a.order ⟨1, by omega⟩ = a.order 1 := by
        congr 1
      have hindexTwo : a.order ⟨2, by omega⟩ = a.order 2 := by
        congr 1
      have hgapLarge :
          2 * (ramificationIndex K : Int) ≤ a.order 2 - a.order 1 := by
        rw [hsecond]
        omega
      have hdiv : (ramificationIndex K : Int) ≤
          (a.order 2 - a.order 1) / 2 := by omega
      have hupperInt :
          2 * ((ramificationIndex K : Int) -
            (a.order 2 - a.order 1) / 2) - 1 ≤ -1 := by omega
      have hupper : a.universalAlphaThreeUpperBound hfour ≤ (-1 : ℚ) := by
        unfold universalAlphaThreeUpperBound
        rw [hindexOne, hindexTwo]
        exact_mod_cast hupperInt
      have halphaNonnegative :
          0 ≤ a.alphaValue ⟨2, by omega⟩ := (a.alpha_p2 _).1
      linarith
    have hthirdCases : a.order 2 = 0 ∨ a.order 2 = 1 := by omega
    have hgapOne : a.orderGap (1 : Fin (m + 2)) =
        a.order 2 - a.order 1 := by
      unfold orderGap
      congr 1
    have halphaTwo : a.alphaValue (1 : Fin (m + 2)) =
        2 * (ramificationIndex K : ℚ) - 1 := by
      rcases hthirdCases with hthirdZero | hthirdOne
      · have hgap : a.orderGap (1 : Fin (m + 2)) =
            2 * (ramificationIndex K : Int) - 2 := by
          rw [hgapOne, hsecond, hthirdZero]
          omega
        have hhalf := a.beli2009Corollary29_i (1 : Fin (m + 2))
          (Or.inr (Or.inr (Or.inr hgap)))
        rw [hhalf]
        unfold halfGapValue
        rw [hgap]
        push_cast
        ring
      · have hgap : a.orderGap (1 : Fin (m + 2)) =
            2 * (ramificationIndex K : Int) - 1 := by
          rw [hgapOne, hsecond, hthirdOne]
          omega
        have hgapLe : a.orderGap (1 : Fin (m + 2)) ≤
            2 * (ramificationIndex K : Int) := by rw [hgap]; omega
        have hodd : Odd (a.orderGap (1 : Fin (m + 2))) := by
          rw [hgap]
          refine ⟨(ramificationIndex K : Int) - 1, ?_⟩
          omega
        have halpha :=
          (a.alpha_p3 (1 : Fin (m + 2)) hgapLe).2.mpr (Or.inr hodd)
        rw [halpha, hgap]
        exact_mod_cast (rfl :
          2 * (ramificationIndex K : Int) - 1 =
            2 * (ramificationIndex K : Int) - 1)
    have hfirst := a.firstAdjacentDefect_eq_min_raw_alphaTwo
      h.rankAtLeastThree
    have hupper : a.truncatedPrefixDefect a (-1) 0 2 ≤
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) := by
      rw [hfirst, halphaTwo]
      exact min_le_right _ _
    have hendpointValue :
        (1 : ℚ) - ((2 - 2 * (ramificationIndex K : Int) : Int) : ℚ) =
          2 * (ramificationIndex K : ℚ) - 1 := by
      push_cast
      ring
    have hlower :
        (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ) ≤
          a.truncatedPrefixDefect a (-1) 0 2 := by
      have := hconsequences.2.2.1
      rw [hgapZero, hsecond] at this
      rw [hendpointValue] at this
      exact this
    have heq := le_antisymm hupper hlower
    rw [hgapZero, hsecond]
    rw [hendpointValue]
    exact heq

end BONG.GoodBONG

end Bong
