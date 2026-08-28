/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: integral even type-III branch

If the retained domination coefficient is strictly below `R - S + 2`
and the final comparison alpha is integral, the primary candidate is
strictly below `beta_i + 1`.  Integrality rounds this to the desired
weak beta estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The strict low-witness branch with integral `gamma_(i-1)` satisfies
`B_i <= beta_i`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_strict_integral
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
    (hiTwo : 2 <= i.val) (j : Fin (n + 1))
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
    (hintegral : IsRationalInteger
      (c.alphaValue (evenTargetPreviousAlphaIndex i))) :
    (b.representationAlphaValue c i : WithTop Rat) <=
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := Fin.mk D.outer.last hlast
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
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
  apply WithTop.coe_le_coe.mpr
  have hprimaryTop :=
    lemma79_even_representationAlphaValue_le_primaryCoefficient
      b c i hiTwo
  have hprimary : b.representationAlphaValue c i <=
      ((b.order (Fin.mk i.val i.lt_large) -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) := by
    exact_mod_cast hprimaryTop
  have hstrictQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) < centralQ := by
    exact_mod_cast hstrict
  have hprimaryLt :
      ((b.order (Fin.mk i.val i.lt_large) -
        c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) <
        b.alphaValue (caseEightLastAlphaIndex i) + 1 := by
    have hjOrderQ : (c.order j.castSucc : Rat) =
        (reference : Rat) + 1 := by
      exact_mod_cast hjOrder
    rw [hcentralReference] at hstrictQ
    push_cast at hstrictQ hjOrderQ hformula ⊢
    simp only [first] at hstrictQ
    simp only [last] at hformula
    linarith
  rcases hintegral with ⟨z, hz⟩
  rcases H.alpha_odd last hfirstLast le_rfl with ⟨w, hwOdd, hw⟩
  have hw' : b.alphaValue (caseEightLastAlphaIndex i) = (w : Rat) := by
    simpa only [last] using hw
  have hcoefficientInt :
      b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) + z <= w := by
    have hcast :
        ((b.order (Fin.mk i.val i.lt_large) -
            c.order (evenTargetPreviousIndex i) + z : Int) : Rat) <
          ((w + 1 : Int) : Rat) := by
      rw [hz, hw'] at hprimaryLt
      push_cast at hprimaryLt ⊢
      linarith
    have hint : b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) + z < w + 1 := by
      exact_mod_cast hcast
    omega
  calc
    b.representationAlphaValue c i <=
        ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) := hprimary
    _ <= b.alphaValue last := by
      rw [hz, hw]
      push_cast
      exact_mod_cast hcoefficientInt
    _ = _ := by rfl

end BONG.GoodBONG

end Bong
