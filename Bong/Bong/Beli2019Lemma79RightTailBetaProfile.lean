/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AlphaLocalFormula
import Bong.Bong.Beli2019Lemma79RightTailPropagation

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the strict beta profile

If the final beta lies strictly below its half-gap candidate, no earlier
beta on the constant-right-endpoint tail can attain its half-gap candidate.
Otherwise monotonicity of adjacent order sums is reversed.  Lemma 2.7 then
makes every beta a positive odd integer strictly below `2e`, and Remark 1.1
selects the capped adjacent-defect term in the local alpha formula.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V} {n : Nat}

/-- The arithmetic profile of every beta on the strict case-8 tail. -/
structure CaseEightStrictBetaTailConsequences
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1)) : Prop
    extends CaseEightBetaTailConsequences b first last where
  alpha_lt_halfGap (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.alphaValue j < b.halfGapValue j
  alpha_odd (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    IsOddRationalInteger (b.alphaValue j)
  alpha_pos (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    0 < b.alphaValue j
  alpha_lt_twoE (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    b.alphaValue j < 2 * (ramificationIndex K : Rat)
  local_formula (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
    (b.alphaValue j : WithTop Rat) =
      (((b.order j.succ - b.order j.castSucc : Int) : Rat) :
          WithTop Rat) +
        b.truncatedPrefixDefect b (-1) j.val (j.val + 2)

/-- On a constant right-endpoint interval, attaining the half-gap at an
earlier boundary contradicts a strict half-gap inequality at the end. -/
theorem CaseEightBetaTailConsequences.alpha_lt_halfGap_of_last
    [Beli2006AlphaLaws.{u, v} K]
    {b : GoodBONG q M (n + 2)} {first last : Fin (n + 1)}
    (H : CaseEightBetaTailConsequences b first last)
    (hlastStrict : b.alphaValue last < b.halfGapValue last)
    (j : Fin (n + 1)) (hfirst : first <= j) (hlast : j <= last) :
    b.alphaValue j < b.halfGapValue j := by
  by_cases hjLast : j = last
  · simpa only [hjLast] using hlastStrict
  · have hjLastLt : j < last := lt_of_le_of_ne hlast hjLast
    have hvalueLast := H.value_eq last (hfirst.trans hlast) le_rfl
    have hvalueJ := H.value_eq j hfirst hlast
    have hsum := b.adjacentOrderSum_monotone hjLastLt.le
    have hsumQ :
        ((b.order j.castSucc + b.order j.succ : Int) : Rat) <=
          ((b.order last.castSucc + b.order last.succ : Int) : Rat) := by
      exact_mod_cast hsum
    have hjLe := b.alphaValue_le_halfGapValue j
    apply lt_of_le_of_ne hjLe
    intro hjEq
    unfold adjacentOrderSum at hsum
    unfold halfGapValue orderGap at hlastStrict hjEq
    push_cast at hvalueLast hvalueJ hsumQ hlastStrict hjEq
    linarith

/-- The complete strict beta profile used after the opening reductions of
case 8. -/
theorem caseEight_strictBetaTailConsequences
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (first last : Fin (n + 1))
    (H : CaseEightBetaTailConsequences b first last)
    (hlastStrict : b.alphaValue last < b.halfGapValue last) :
    CaseEightStrictBetaTailConsequences b first last := by
  have hhalf (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
      b.alphaValue j < b.halfGapValue j :=
    H.alpha_lt_halfGap_of_last hlastStrict j hfirst hlast
  have hodd (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
      IsOddRationalInteger (b.alphaValue j) :=
    b.beli2009Lemma27_iv j (ne_of_lt (hhalf j hfirst hlast))
  have hpos (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) : 0 < b.alphaValue j := by
    have hnonnegative := (b.beli2009Lemma27_i j).1
    apply lt_of_le_of_ne hnonnegative
    intro hzero
    rcases hodd j hfirst hlast with ⟨z, hzOdd, hz⟩
    have hzZero : z = 0 := by
      have hzRat : (z : Rat) = 0 := hz.symm.trans hzero.symm
      exact_mod_cast hzRat
    subst z
    exact Int.not_odd_iff_even.mpr (by simp) hzOdd
  have htwoE (j : Fin (n + 1)) (hfirst : first <= j)
      (hlast : j <= last) :
      b.alphaValue j < 2 * (ramificationIndex K : Rat) := by
    have hgap : b.orderGap j < 2 * (ramificationIndex K : Int) := by
      by_contra hnot
      have hlarge : 2 * (ramificationIndex K : Int) <= b.orderGap j :=
        le_of_not_gt hnot
      have heq := b.beli2009Lemma27_ii j hlarge
      exact (ne_of_lt (hhalf j hfirst hlast)) heq
    exact (b.beli2009Corollary28_ii j).1.mpr hgap
  refine
    { toCaseEightBetaTailConsequences := H
      alpha_lt_halfGap := hhalf
      alpha_odd := hodd
      alpha_pos := hpos
      alpha_lt_twoE := htwoE
      local_formula := ?_ }
  intro j hfirst hlast
  have hlocal := b.alpha_eq_min_halfGap_add_cappedAdjacent j
  have hstrict : (b.alphaValue j : WithTop Rat) <
      b.halfGapCandidate j := by
    rw [← b.coe_halfGapValue]
    exact_mod_cast hhalf j hfirst hlast
  let candidate : WithTop Rat :=
    (((b.order j.succ - b.order j.castSucc : Int) : Rat) :
        WithTop Rat) +
      b.truncatedPrefixDefect b (-1) j.val (j.val + 2)
  have hcandidate : candidate <= b.halfGapCandidate j := by
    by_contra hnot
    have hhalfLe : b.halfGapCandidate j <= candidate := le_of_not_ge hnot
    have heq : (b.alphaValue j : WithTop Rat) =
        b.halfGapCandidate j := by
      rw [hlocal, min_eq_left hhalfLe]
    exact (ne_of_lt hstrict) heq
  rw [hlocal, show min (b.halfGapCandidate j) candidate = candidate by
    exact min_eq_right hcandidate]

end BONG.GoodBONG

end Bong
