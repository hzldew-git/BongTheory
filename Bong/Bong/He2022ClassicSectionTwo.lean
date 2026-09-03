/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionTwo
import Bong.Bong.Beli2006AlphaP3OddProof
import Bong.Lattice.ClassicIntegrality

/-!
# He (2024), Section 2: invariant and representation preliminaries

This file gives paper-labelled endpoints for the preliminary results in
Zilong He, *On classic n-universal quadratic forms over dyadic local fields*,
manuscripta math. 174 (2024), 559--595.  The publisher version is the semantic
authority.

Paper indices are one based.  A Lean index `i : Fin n` below is the paper
index `i+1`; consequently `orderGap i` is `R_(i+2)-R_(i+1)`.
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

/-- The displayed conditions (2.1)--(2.2) in He, Lemma 2.1. -/
abbrev HeClassicGoodBONGCriteria {n : Nat}
    (X : OrthogonalBasisData q n) : Prop :=
  X.HeHuGoodBONGCriteria

/-- He, Lemma 2.1, restated from the common He--Hu/Beli good-BONG
criterion. -/
theorem he2022ClassicLemma21 {n : Nat} (X : OrthogonalBasisData q n) :
    X.HasGoodRealization ↔ X.HeClassicGoodBONGCriteria :=
  X.heHu2022Lemma22

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

/-- The two alternatives in He, Proposition 2.3(iii). -/
def HeClassicAlphaOneCases {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop :=
  (a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
      a.orderGap i = 1) ∨
    (Even (a.orderGap i) ∧
      4 - 2 * (ramificationIndex K : Int) ≤ a.orderGap i ∧
      a.orderGap i ≤ 0 ∧
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))

/-- All six clauses of He, Proposition 2.2. -/
structure HeClassicProposition22Conclusions {n : Nat}
    (a : GoodBONG q L (n + 2)) : Prop where
  compareTwoE (i : Fin (n + 1)) :
    (2 * (ramificationIndex K : ℚ) < a.alphaValue i ↔
        2 * (ramificationIndex K : Int) < a.orderGap i) ∧
      (a.alphaValue i = 2 * (ramificationIndex K : ℚ) ↔
        a.orderGap i = 2 * (ramificationIndex K : Int)) ∧
      (a.alphaValue i < 2 * (ramificationIndex K : ℚ) ↔
        a.orderGap i < 2 * (ramificationIndex K : Int))
  halfGap (i : Fin (n + 1))
      (hcase :
        2 * (ramificationIndex K : Int) ≤ a.orderGap i ∨
        a.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
        a.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
        a.orderGap i = 2 * (ramificationIndex K : Int) - 2) :
    a.alphaValue i = a.halfGapValue i
  lowerBound (i : Fin (n + 1))
      (hgap : a.orderGap i ≤ 2 * (ramificationIndex K : Int)) :
    (a.orderGap i : ℚ) ≤ a.alphaValue i ∧
      (a.alphaValue i = (a.orderGap i : ℚ) ↔
        a.orderGap i = 2 * (ramificationIndex K : Int) ∨
          Odd (a.orderGap i))
  oddGapFormula (i : Fin (n + 1)) (hodd : Odd (a.orderGap i)) :
    a.alphaValue i =
      min (a.halfGapValue i) (a.orderGap i : ℚ) ∧
      0 < a.orderGap i
  endpointMonotonicity (i j : Fin (n + 1)) (hij : i ≤ j) :
    a.alphaLeftEndpoint i ≤ a.alphaLeftEndpoint j ∧
      a.alphaRightEndpoint j ≤ a.alphaRightEndpoint i
  constantAdjacentSum (i j : Fin (n + 1)) (hij : i ≤ j)
      (hsum : a.adjacentOrderSum i = a.adjacentOrderSum j) :
    ∀ k : Fin (n + 1), i ≤ k → k ≤ j →
      a.alphaLeftEndpoint k = a.alphaLeftEndpoint i

/-- He, Proposition 2.2.  This is a direct re-indexed consequence of the
proved alpha laws used by the He--Hu formalization. -/
theorem he2022ClassicProposition22 {n : Nat}
    (a : GoodBONG q L (n + 2)) :
    HeClassicProposition22Conclusions a := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  refine {
    compareTwoE := ?_
    halfGap := ?_
    lowerBound := ?_
    oddGapFormula := ?_
    endpointMonotonicity := ?_
    constantAdjacentSum := ?_ }
  · intro i
    let C := a.heHu2022Proposition26 i
    exact ⟨C.compareTwoE.2.2, C.compareTwoE.2.1, C.compareTwoE.1⟩
  · intro i hcase
    exact (a.heHu2022Proposition26 i).halfGap hcase
  · intro i hgap
    exact (a.heHu2022Proposition26 i).lowerBound hgap
  · intro i hodd
    constructor
    · by_cases hle : a.orderGap i ≤
          2 * (ramificationIndex K : Int)
      · have halpha :=
          a.alphaValue_eq_orderGap_of_odd_of_le_twoE i hle hodd
        rw [halpha, min_eq_right]
        unfold halfGapValue
        have hleQ : (a.orderGap i : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by
          exact_mod_cast hle
        linarith
      · have hge : 2 * (ramificationIndex K : Int) ≤
            a.orderGap i := by omega
        have halpha := (a.heHu2022Proposition26 i).halfGap (Or.inl hge)
        rw [halpha, min_eq_left]
        unfold halfGapValue
        have hgt : 2 * (ramificationIndex K : Int) <
            a.orderGap i := by omega
        have hgtQ : 2 * (ramificationIndex K : ℚ) <
            (a.orderGap i : ℚ) := by
          exact_mod_cast hgt
        linarith
    · exact (a.heHu2022Corollary23i i).1 hodd
  · intro i j hij
    let C := a.heHu2022Proposition25 i j hij
    exact ⟨C.leftEndpoint_le, C.rightEndpoint_le⟩
  · intro i j hij hsum
    exact (a.heHu2022Proposition25 i j hij).constantSum hsum

/-- All six clauses of He, Proposition 2.3. -/
structure HeClassicProposition23Conclusions {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) : Prop where
  arithmeticShape :
    (0 ≤ a.alphaValue i ∧
        a.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ∧
        IsRationalInteger (a.alphaValue i)) ∨
      (2 * (ramificationIndex K : ℚ) < a.alphaValue i ∧
        IsRationalHalfInteger (a.alphaValue i))
  alphaZero : a.alphaValue i = 0 ↔
    a.orderGap i = -(2 * (ramificationIndex K : Int))
  alphaOne : a.alphaValue i = 1 ↔ a.HeClassicAlphaOneCases i
  alphaOne_ramificationOne
      (he : ramificationIndex K = 1) :
    a.alphaValue i = 1 ↔ a.orderGap i = 0 ∨ a.orderGap i = 1
  alphaZeroDefect (halpha : a.alphaValue i = 0) :
    ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i
  alphaOneDefect (halpha : a.alphaValue i = 1) :
    ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ) ≤
      a.heHuAdjacentCappedDefect i ∧
    (a.orderGap i ≠ 2 - 2 * (ramificationIndex K : Int) →
      a.heHuAdjacentCappedDefect i =
        ((((1 : ℚ) - (a.orderGap i : ℚ)) : ℚ) : WithTop ℚ))
  rawDefectCriterion
      (hraw :
        (((a.orderGap i : Int) : ℚ) : WithTop ℚ) +
            a.adjacentDefect i = 1) :
    a.alphaValue i = 1

/-- He, Proposition 2.3. -/
theorem he2022ClassicProposition23 {n : Nat}
    (a : GoodBONG q L (n + 1)) (i : Fin n) :
    HeClassicProposition23Conclusions a i := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  letI : Beli2009AlphaParityLaws.{u, v} K :=
    beliUniversalAlphaParityLaws
  let C := a.heHu2022Proposition26 i
  refine {
    arithmeticShape := C.arithmeticShape
    alphaZero := C.alphaZero
    alphaOne := ?_
    alphaOne_ramificationOne := ?_
    alphaZeroDefect := C.alphaZeroDefect
    alphaOneDefect := ?_
    rawDefectCriterion := ?_ }
  · constructor
    · intro halpha
      rcases C.alphaOne halpha with ⟨hgap, _hbound, hsharp⟩
      rcases hgap with hone | heven
      · exact Or.inl (Or.inr hone)
      · by_cases hendpoint :
          a.orderGap i = 2 - 2 * (ramificationIndex K : Int)
        · exact Or.inl (Or.inl hendpoint)
        · right
          rcases heven.1 with ⟨z, hz⟩
          refine ⟨⟨z, hz⟩, ?_, heven.2.2, hsharp hendpoint⟩
          omega
    · intro hcases
      rcases hcases with hendpoints | hinterior
      · exact a.alphaValue_eq_one_of_orderGap_eq_endpoint i
          (hendpoints.elim Or.inl Or.inr)
      · have hePos : (1 : Int) ≤ ramificationIndex K := by
          exact_mod_cast ramificationIndex_pos (K := K)
        exact (C.alphaOneIff (by omega) hinterior.2.2.1).2
          hinterior.2.2.2
  · intro he
    constructor
    · intro halpha
      rcases (C.alphaOne halpha).1 with hone | heven
      · exact Or.inr hone
      · left
        rw [he] at heven
        norm_num at heven
        omega
    · intro hgap
      apply a.alphaValue_eq_one_of_orderGap_eq_endpoint i
      rw [he]
      norm_num
      exact hgap.elim Or.inl Or.inr
  · intro halpha
    exact (C.alphaOne halpha).2
  · intro hraw
    have hupper : a.alphaValue i ≤ 1 := by
      have h := a.alpha_le_rightDefectCandidate (i := i) (j := i) le_rfl
      rw [← a.coe_alphaValue] at h
      have hcandidate :
          a.rightDefectCandidate i i =
            (((a.orderGap i : Int) : ℚ) : WithTop ℚ) +
              a.adjacentDefect i := by
        unfold rightDefectCandidate orderGap
        rfl
      rw [hcandidate, hraw] at h
      exact_mod_cast h
    have hne : a.alphaValue i ≠ 0 := by
      intro hzero
      have hgap := C.alphaZero.mp hzero
      have hdefectNeTop : a.adjacentDefect i ≠ ⊤ := by
        intro htop
        rw [htop, add_top] at hraw
        exact WithTop.top_ne_coe hraw
      let d : ℚ := (a.adjacentDefect i).untop hdefectNeTop
      have hd : (d : WithTop ℚ) = a.adjacentDefect i :=
        WithTop.coe_untop _ _
      have hrawQ : (a.orderGap i : ℚ) + d = 1 := by
        have hraw' := hraw
        rw [← hd, ← WithTop.coe_add] at hraw'
        exact WithTop.coe_eq_coe.mp hraw'
      have hdefectLarge :
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
            a.adjacentDefect i := by
        have heNatInt :
            (ramificationIndex K : Int) =
              ((ramificationIndex K : Nat) : Int) := rfl
        rw [hgap, heNatInt] at hrawQ
        have hdLarge : ((2 * ramificationIndex K : Nat) : ℚ) < d := by
          push_cast at hrawQ ⊢
          linarith
        rw [← hd]
        exact_mod_cast hdLarge
      have hsquare := isSquare_of_two_mul_e_lt_defectOrder
        (K := K) (a.adjacentProduct i) (by
          simpa only [adjacentDefect] using hdefectLarge)
      have htop : a.adjacentDefect i = ⊤ := by
        unfold adjacentDefect
        exact defectOrder_eq_top_of_isSquare hsquare
      exact hdefectNeTop htop
    exact le_antisymm hupper (a.heHuOne_le_alphaValue_of_ne_zero i hne)

/-- Equations (2.5)--(2.6): for a nonempty good BONG, classic
integrality is detected by its first order and its first adjacent sum. -/
theorem isClassicIntegral_iff_firstOrders {n : Nat}
    (a : GoodBONG q L (n + 2)) :
    Lattice.IsClassicIntegral q L ↔
      0 ≤ a.order 0 ∧ 0 ≤ a.order 0 + a.order 1 := by
  rcases a.toBONG.beliCorollary44_iv_unconditional a.good with
    ⟨s, hscale, horder⟩
  change 2 * ordUnit K s =
    min (2 * a.order 0) (a.order 0 + a.order 1) at horder
  have hclassic : Lattice.IsClassicIntegral q L ↔
      0 ≤ ordUnit K s := by
    change Lattice.scaleIdeal q L ≤ Lattice.unitIdeal (K := K) ↔ _
    rw [hscale, Lattice.unitIdeal,
      Lattice.principalIdeal_le_iff_ord_ge
        (Units.ne_zero s) (one_ne_zero : (1 : K) ≠ 0),
      ord_one, ← coe_ordUnit]
    exact WithTop.coe_nonneg
  rw [hclassic]
  constructor
  · intro hs
    have hmin : 0 ≤
        min (2 * a.order 0) (a.order 0 + a.order 1) := by
      omega
    have hparts := (le_min_iff.mp hmin)
    exact ⟨by omega, hparts.2⟩
  · rintro ⟨hfirst, hsum⟩
    have hmin : 0 ≤
        min (2 * a.order 0) (a.order 0 + a.order 1) :=
      le_min (by omega) hsum
    omega

/-- He, Theorem 2.5: Beli's representation theorem in the notation of the
classic paper. -/
theorem he2022ClassicTheorem25 {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  a.heHu2022Theorem28 hRank ambient b

end BONG.GoodBONG

end Bong
