/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalAlpha
import Bong.Bong.DiagonalQuaternaryUniversalityProof

/-!
# The two cases in Beli's universal-lattice criterion

This file gives a boundary-safe statement of the alternatives in Theorem 2.1
of Beli's *Universal integral quadratic forms over dyadic local fields*.
The rank is written as `tail + 2`.  Thus every occurrence of `R₃`, `R₄`, or
`α₃` carries the proof that the corresponding entry exists; the paper's
informal convention `Rᵢ ≫ 0` beyond the rank is not used.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The binary prefix `[a₁,a₂]` is isotropic. -/
def UniversalFirstTwoIsotropic {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  DiagonalIsotropic (a.prefixValues 2 (by omega))

/-- The ternary prefix `[a₁,a₂,a₃]` is isotropic. -/
def UniversalFirstThreeIsotropic {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hthree : 0 < tail) : Prop :=
  DiagonalIsotropic (a.prefixValues 3 (by omega))

/-- The exact right hand side in Theorem 2.1, II(b):
`2(e - floor((R₃-R₂)/2))-1`. -/
noncomputable def universalAlphaThreeUpperBound {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hfour : 1 < tail) : ℚ :=
  2 * ((ramificationIndex K : ℚ) -
      (((a.order ⟨2, by omega⟩ - a.order ⟨1, by omega⟩) / 2 : Int) : ℚ)) - 1

/-- Case I of Beli, Theorem 2.1.  The three fields are the literal clauses
I(a), I(b), and I(c), with the two rank branches separated. -/
structure UniversalCaseI {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop where
  alphaOne : a.alphaValue (0 : Fin (tail + 1)) = 0
  binaryRankTwo : tail = 0 → a.UniversalFirstTwoIsotropic
  binaryAboveOne : ∀ hthree : 0 < tail,
    1 < a.order ⟨2, by omega⟩ → a.UniversalFirstTwoIsotropic
  binaryAtOne : ∀ hthree : 0 < tail,
    a.order ⟨2, by omega⟩ = 1 →
      (tail = 1 ∨ ∃ hfour : 1 < tail,
        2 * (ramificationIndex K : Int) + 1 < a.order ⟨3, by omega⟩) →
      a.UniversalFirstTwoIsotropic

/-- Case II of Beli, Theorem 2.1.  The witness in `alphaThreeBound` is the
paper's conclusion `m ≥ 4`, not an additional hypothesis. -/
structure UniversalCaseII {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop where
  rankAtLeastThree : 0 < tail
  alphaOne : a.alphaValue (0 : Fin (tail + 1)) = 1
  alphaThreeBound :
    (a.order ⟨1, by omega⟩ = 1 ∨
        1 < a.order ⟨2, by omega⟩) →
      ∃ hfour : 1 < tail,
        a.alphaValue ⟨2, by omega⟩ ≤
          a.universalAlphaThreeUpperBound hfour
  ternaryBoundary :
    a.order ⟨1, by omega⟩ ≤ 0 →
    a.order ⟨2, by omega⟩ ≤ 1 →
    (tail = 1 ∨ ∃ hfour : 1 < tail,
      2 * (ramificationIndex K : Int) <
        a.order ⟨3, by omega⟩ - a.order ⟨2, by omega⟩) →
    a.UniversalFirstThreeIsotropic rankAtLeastThree

/-- The complete right-hand side of Theorem 2.1 after the hypotheses
`m ≥ 2` and `R₁ = 0` have been made explicit in the type and conjunction. -/
def UniversalTheorem21Conditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  a.order 0 = 0 ∧ (UniversalCaseI a ∨ UniversalCaseII a)

theorem UniversalCaseI.orderGap_zero_eq_neg_two_e {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseI a) :
    a.orderGap (0 : Fin (tail + 1)) =
      -(2 * (ramificationIndex K : Int)) :=
  (a.alpha_p2 (0 : Fin (tail + 1))).2.mp h.alphaOne

theorem UniversalCaseI.order_one_eq_neg_two_e {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseI a)
    (hzero : a.order 0 = 0) :
    a.order 1 = -(2 * (ramificationIndex K : Int)) := by
  have hgap := h.orderGap_zero_eq_neg_two_e
  unfold orderGap at hgap
  have hzero' :
      a.order (Fin.castSucc (0 : Fin (tail + 1))) = 0 := by
    simpa using hzero
  rw [hzero'] at hgap
  simpa using hgap

theorem UniversalCaseII.tail_ne_zero {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseII a) :
    tail ≠ 0 := Nat.ne_of_gt h.rankAtLeastThree

theorem UniversalCaseII.no_rank_three_large_branch {tail : Nat}
    {a : GoodBONG q L (tail + 2)} (h : UniversalCaseII a)
    (hbranch : a.order ⟨1, by omega⟩ = 1 ∨
      1 < a.order ⟨2, by have := h.rankAtLeastThree; omega⟩) :
    1 < tail := (h.alphaThreeBound hbranch).choose

end BONG.GoodBONG

end Bong
