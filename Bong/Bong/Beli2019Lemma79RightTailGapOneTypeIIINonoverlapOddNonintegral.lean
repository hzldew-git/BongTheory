/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd nonintegral type-III branch

For nonintegral `gamma_(i-1)`, the alpha is strictly above `2e`.  Combined
with strict domination and the exact low witness order `R + 1`, this bounds
the integral cross-gap by `beta_i`; the half-gap representation candidate
then closes the odd-index estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The strict low-witness branch with nonintegral `gamma_(i-1)` satisfies
the odd nonoverlapping type-III beta estimate. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_of_nonintegral
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (j : Fin (n + 1))
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hstrict :
      ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) <
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat))
    (hnotIntegral : ¬ IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.outer.last hlast
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  let reference : Int :=
    a.orderSequence.entryOrZero D.outer.transition.lastZero
  let centralQ : Rat :=
    ((b.order
          (Fin.mk D.outer.transition.lastZero (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) -
        a.order
          (Fin.mk (D.outer.transition.lastZero + 1) (by
            have hbound := D.outer.transition.firstTwo_le_rank
            rw [D.adjacent] at hbound
            omega)) : Int) : Rat)
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
  have hcentralReference : centralQ =
      ((reference - b.order first.castSucc + 2 : Int) : Rat) := by
    simpa only [centralQ, reference, first] using
      beli2019Lemma79_typeIII_nonoverlap_central_eq_reference_sub_base_add_two
        a b D hlast
  have halphaLarge : 2 * (ramificationIndex K : Rat) <
      c.alphaValue p := by
    rcases c.beli2009Corollary28_iii p with hsmall | hlarge
    · exact False.elim (hnotIntegral (by
        simpa only [p] using hsmall.2.2))
    · exact hlarge.1
  have hstrictQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue p < centralQ := by
    exact_mod_cast hstrict
  have hjOrderQ : (c.order j.castSucc : Rat) =
      (reference : Rat) + 1 := by
    exact_mod_cast hjOrder
  have hcrossLt :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) : Int) : Rat) <
        b.alphaValue last + 1 := by
    rw [hcentralReference] at hstrictQ
    push_cast at hstrictQ hjOrderQ halphaLarge hformula ⊢
    simp only [first, last] at hstrictQ hformula
    linarith
  rcases H.alpha_odd last hfirstLast le_rfl with
    ⟨w, hwOdd, hw⟩
  have hcrossLeInt :
      b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) <= w := by
    have hcast :
        ((b.order (Fin.mk i.val i.lt_large) -
            c.order (evenTargetPreviousIndex i) +
            2 * (ramificationIndex K : Int) : Int) : Rat) <
          ((w + 1 : Int) : Rat) := by
      rw [hw] at hcrossLt
      push_cast at hcrossLt ⊢
      linarith
    have hint : b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) < w + 1 := by
      exact_mod_cast hcast
    omega
  have hcrossLe :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) +
          2 * (ramificationIndex K : Int) : Int) : Rat) <=
        b.alphaValue last := by
    rw [hw]
    exact_mod_cast hcrossLeInt
  have hbetaPos := H.alpha_pos last hfirstLast le_rfl
  have hhalf :
      ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) / 2 +
          (ramificationIndex K : Rat) <= b.alphaValue last := by
    push_cast at hcrossLe ⊢
    linarith
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i <= b.representationHalfGap c i :=
      b.representationAlpha_le_halfGap c i
    _ <= (b.alphaValue last : WithTop Rat) := by
      unfold representationHalfGap
      exact_mod_cast hhalf
    _ = _ := by rfl

end BONG.GoodBONG

end Bong
