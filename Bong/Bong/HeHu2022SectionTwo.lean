/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006SectionTwo
import Bong.Bong.Beli2009AlphaMonotonicity
import Bong.Bong.BeliUniversalAlpha
import Bong.Bong.Beli2019MainTheorem

/-!
# He--Hu (2024), Section 2

This file gives direct Lean endpoints for the reusable results in Section 2
of Zilong He and Yong Hu, *On n-universal quadratic forms over dyadic local
fields*, Sci. China Math. 67 (2024), 1481--1506.

The paper uses one-based indices.  A Lean index `i : Fin n` below denotes the
paper index `i + 1`.  In particular, `a.orderGap i`, `a.alphaValue i`, and
`a.heHuAdjacentCappedDefect i` are respectively
`R_(i+2) - R_(i+1)`, `alpha_(i+1)`, and
`d[-a_(i+1) a_(i+2)]`.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace BONG.OrthogonalBasisData

/-- The two displayed numerical conditions (2.2)--(2.3) in He--Hu,
Lemma 2.2.  The absolute-defect predicate is precisely
`ord(-a) + d(-a) >= 0`, expressed without subtraction in `Nat.infinity`. -/
def HeHuGoodBONGCriteria {n : Nat} (X : OrthogonalBasisData q n) : Prop :=
  X.HasWeakTwoStepOrder ∧
    ∀ (i : Fin n) (hi : i.1 + 1 < n),
      0 ≤ ordUnit K (X.adjacentParameter i hi) +
          2 * (ramificationIndex K : Int) ∧
        HasNonnegativeAbsoluteQuadraticDefect
          (-(X.adjacentParameter i hi))

/-- He--Hu, Lemma 2.2: the explicit order-and-defect criterion for an
orthogonal basis to be a good BONG of a lattice. -/
theorem heHu2022Lemma22 {n : Nat} (X : OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.HeHuGoodBONGCriteria := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  rw [X.hasGoodRealization_iff_beli2006Criteria]
  unfold SatisfiesGoodBONGCriteria HeHuGoodBONGCriteria
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
    (X.adjacentParameter i hi)

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

/-- Definition 2.4: He--Hu's `alpha_i`, in zero-based indexing. -/
noncomputable abbrev heHuAlpha {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  a.alpha i

/-- Definition 2.4 and equation (2.5): `d[c a_i ... a_j]`, retaining
the source convention that missing endpoint alpha caps are ignored. -/
noncomputable abbrev heHuTruncatedSegmentDefect {n : Nat}
    (a : GoodBONG q L (n + 1)) (c : Kˣ) (i j : Nat) : WithTop ℚ :=
  a.truncatedSegmentDefect c i j

/-- Definition 2.4 and equation (2.5): the capped adjacent defect
`d[-a_i a_(i+1)]`, with `i` zero-based. -/
noncomputable def heHuAdjacentCappedDefect {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : WithTop ℚ :=
  a.truncatedPrefixDefect a (-1) i.val (i.val + 2)

/-- Corollary 2.3(i): an odd adjacent gap is positive, equivalently every
nonpositive adjacent gap is even. -/
theorem heHu2022Corollary23i {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    (Odd (a.orderGap i) → 0 < a.orderGap i) ∧
      (a.orderGap i ≤ 0 → Even (a.orderGap i)) := by
  constructor
  · intro hodd
    have hadmissible :=
      a.toBONG.adjacentParameter_isBinaryParameterAdmissible
        i.castSucc (Nat.add_lt_add_right i.isLt 1)
    have hnonnegative := hadmissible.ordUnit_nonneg_of_odd (by
      rw [a.toBONG.ordUnit_adjacentParameter i.castSucc
        (Nat.add_lt_add_right i.isLt 1)]
      exact hodd)
    rw [a.toBONG.ordUnit_adjacentParameter i.castSucc
      (Nat.add_lt_add_right i.isLt 1)] at hnonnegative
    have hindex :
        (⟨i.castSucc.val + 1, by
          change i.val + 1 < n + 1
          exact Nat.add_lt_add_right i.isLt 1⟩ : Fin (n + 1)) =
          i.succ := by
      apply Fin.ext
      rfl
    rw [hindex] at hnonnegative
    have hnonnegative' : 0 ≤ a.orderGap i := by
      exact hnonnegative
    have hne : a.orderGap i ≠ 0 := by
      intro hzero
      rw [hzero] at hodd
      exact (Int.not_odd_iff_even.mpr Even.zero) hodd
    exact lt_of_le_of_ne hnonnegative' hne.symm
  · exact a.orderGap_even_of_nonpositive i

/-- Proposition 2.5, with the paper's two conclusions bundled together. -/
structure HeHuProposition25Conclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  leftEndpoint_le : a.alphaLeftEndpoint i ≤ a.alphaLeftEndpoint j
  rightEndpoint_le : a.alphaRightEndpoint j ≤ a.alphaRightEndpoint i
  constantSum : a.adjacentOrderSum i = a.adjacentOrderSum j →
    ∀ k : Fin (n + 1), i ≤ k → k ≤ j →
      a.alphaLeftEndpoint k = a.alphaLeftEndpoint i

/-- He--Hu, Proposition 2.5. -/
theorem heHu2022Proposition25 {n : Nat}
    (a : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i ≤ j) :
    HeHuProposition25Conclusions a i j := by
  refine
    { leftEndpoint_le := a.alphaLeftEndpoint_monotone hij
      rightEndpoint_le := a.alphaRightEndpoint_antitone hij
      constantSum := ?_ }
  intro hsum
  exact (a.beli2009Corollary23 i j hij hsum).leftEndpoint_eq

/-- Proposition 2.6(i)--(vii).  The clauses retain the paper's order:
arithmetic shape and alpha zero; comparison with `2e`; the lower bound and
equality cases; the half-gap cases; the alpha-zero defect bound; and the two
alpha-one assertions. -/
structure HeHuProposition26Conclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  arithmeticShape :
    (0 ≤ a.alphaValue i ∧
        a.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (a.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < a.alphaValue i ∧
        IsRationalHalfInteger (a.alphaValue i))
  alphaZero : a.alphaValue i = 0 ↔
    a.orderGap i = -(2 * (ramificationIndex K : Int))
  compareTwoE :
    (a.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
      a.orderGap i < 2 * (ramificationIndex K : Int)) ∧
    (a.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
      a.orderGap i = 2 * (ramificationIndex K : Int)) ∧
    (2 * (ramificationIndex K : ℚ) < a.alphaValue i ↔
      2 * (ramificationIndex K : Int) < a.orderGap i)
  lowerBound (hgap : a.orderGap i ≤
      2 * (ramificationIndex K : Int)) :
    (a.orderGap i : ℚ) ≤ a.alphaValue i ∧
      (a.alphaValue i = (a.orderGap i : ℚ) ↔
        a.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (a.orderGap i))
  halfGap (hcase :
      2 * (ramificationIndex K : Int) ≤ a.orderGap i ∨
      a.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
      a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    a.alphaValue i = a.halfGapValue i
  alphaZeroDefect (halpha : a.alphaValue i = 0) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i
  alphaOne (halpha : a.alphaValue i = 1) :
    (a.orderGap i = 1 ∨
      (Even (a.orderGap i) ∧
        2 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
        a.orderGap i ≤ 0)) ∧
    ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i ∧
    (a.orderGap i ≠ 2 - 2 * (ramificationIndex K : Int) →
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))
  alphaOneIff (hlower :
      2 - 2 * (ramificationIndex K : Int) < a.orderGap i)
      (hupper : a.orderGap i ≤ 0) :
    a.alphaValue i = 1 ↔
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ)

/-- He--Hu, Proposition 2.6. -/
theorem heHu2022Proposition26 {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    HeHuProposition26Conclusions a i := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  refine
    { arithmeticShape := a.beli2009Corollary28_iii i
      alphaZero := (a.beli2009Lemma27_i i).2
      compareTwoE := a.beli2009Corollary28_ii i
      lowerBound := a.beli2009Lemma27_iii i
      halfGap := a.beli2009Corollary29_i i
      alphaZeroDefect := ?_
      alphaOne := ?_
      alphaOneIff := ?_ }
  · intro halpha
    simpa only [heHuAdjacentCappedDefect] using
      a.cappedAdjacent_ge_two_e_of_alphaValue_eq_zero i halpha
  · intro halpha
    have h := a.alphaValue_eq_one_consequences i halpha
    exact ⟨h.2.1, by simpa only [heHuAdjacentCappedDefect] using h.2.2⟩
  · intro hlower hupper
    simpa only [heHuAdjacentCappedDefect] using
      a.alphaValue_eq_one_iff_cappedAdjacent i hlower hupper

/-- He--Hu, Theorem 2.8.  `RepresentationConditions` unfolds to the four
displayed conditions (i)--(iv), including the exceptional terminal-index
convention in condition (iv). -/
theorem heHu2022Theorem28 {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  beli2019Theorem21 hRank ambient a b

end BONG.GoodBONG

end Bong
