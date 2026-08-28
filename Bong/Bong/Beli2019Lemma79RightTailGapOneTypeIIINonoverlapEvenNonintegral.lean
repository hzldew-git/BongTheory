/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOrderBounds
import Bong.Bong.Beli2019Lemma79RightTailGapTwoNonintegralHalfGap

/-!
# Beli (2019), Lemma 7.9(ii), case 8: nonintegral even type-III branch

A nonintegral `gamma_(i-1)` gives the strict half-gap estimate
`B_i < S_(i+1) - T_(i-1)`.  The type-III order chain puts
`T_(i-1) >= S`, so this is strictly below the tail formula
`beta_i = S_(i+1) - S`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The nonintegral preceding alpha satisfies the even type-III beta bound. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_nonintegral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hnotIntegral : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.outer.last hlast
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  have hfirstLast : first <= last := by
    change D.outer.last <= i.val - 1
    have hiPos := i.pos
    omega
  have hformulaData := beli2019Lemma79_typeIII_caseEight_gapOne_formula
    a b D last (by
      change D.outer.last <= last.val
      exact hfirstLast)
      (by simpa only [first, last] using H) (by
        simpa only [last] using hstrictLast)
  have hformula := hformulaData.2 last
    (by simpa only [first, last] using hfirstLast) le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hformula
  have hpreviousLower :=
    beli2019Lemma79_typeIII_nonoverlap_even_previousOrder_ge_tailBase
      a b c D hfirst hdefect hnotOverlap hnorm hlast i hiEven hiTwo
  have halphaLt :=
    representationAlphaValue_lt_order_sub_previous_of_not_integral
      b c i hiTwo hnotIntegral
  apply WithTop.coe_le_coe.mpr
  apply le_of_lt
  have hpreviousLowerQ :
      (b.order first.castSucc : Rat) <=
        (c.order (evenTargetPreviousAlphaIndex i).castSucc : Rat) := by
    exact_mod_cast hpreviousLower
  push_cast at halphaLt hformula hpreviousLowerQ
  simp only [last] at hformula
  linarith

end BONG.GoodBONG

end Bong
