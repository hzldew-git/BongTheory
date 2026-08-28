/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenEqualityParity
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenEqualityNonzero

/-!
# Beli (2019), Lemma 7.9(ii), case 8: complete even type-III equality branch

The odd signed primary product and the length-`i` prefix congruence imply
that the final comparison order has the same parity as the strict-tail
base `S`.  Domination equality gives the lower bound `T_i >= S - 1`, so
parity improves it to `T_i >= S`; the odd primary product then proves the
final beta estimate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The equality alternative selected by capped domination satisfies the
even nonoverlapping type-III beta estimate. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_beta_bound_of_equality
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
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (j : Fin (n + 1))
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hcoefficient :
      ((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) =
      ((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat))
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1)))) :
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
  have hcoefficientQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue p = centralQ := by
    simpa only [p, centralQ] using hcoefficient
  have hjOrderQ : (c.order j.castSucc : Rat) =
      (reference : Rat) + 1 := by
    exact_mod_cast hjOrder
  have hcurrentFormula :
      (c.order (evenTargetPreviousIndex i) : Rat) =
        (b.order first.castSucc : Rat) - 1 + c.alphaValue p := by
    rw [hcentralReference] at hcoefficientQ
    push_cast at hcoefficientQ hjOrderQ
    linarith
  have halphaNonneg : (0 : Rat) <= c.alphaValue p :=
    (c.alpha_p2 p).1
  have hcurrentLowerQ :
      (b.order first.castSucc : Rat) - 1 <=
        (c.order (evenTargetPreviousIndex i) : Rat) := by
    linarith
  have hcurrentLower : b.order first.castSucc - 1 <=
      c.order (evenTargetPreviousIndex i) := by
    exact_mod_cast hcurrentLowerQ
  have hformulaInt : exists beta : Int, Odd beta /\
      b.order (Fin.mk i.val i.lt_large) - b.order first.castSucc = beta := by
    rcases H.alpha_odd last hfirstLast le_rfl with ⟨beta, hbetaOdd, hbeta⟩
    refine ⟨beta, hbetaOdd, ?_⟩
    have hformulaQ : b.alphaValue last =
        ((b.order (Fin.mk i.val i.lt_large) -
          b.order first.castSucc : Int) : Rat) := by
      simpa only [first, last] using hformula
    exact_mod_cast hformulaQ.symm.trans hbeta
  rcases hformulaInt with ⟨beta, hbetaOdd, hbeta⟩
  have hsumOdd : Odd
      (b.orderSequence.prefixSum (i.val + 1) +
        c.orderSequence.prefixSum (i.val - 1)) := by
    have ordUnit_neg_eq (x : Kˣ) : ordUnit K (-x) = ordUnit K x := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      simpa using ord_neg K (x : K)
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have hneg : ordUnit K (-1 : Kˣ) = 0 := by
      rw [ordUnit_neg_eq, hone]
    have horder : ordUnit K
          ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
            c.prefixProduct (i.val - 1)) =
        b.orderSequence.prefixSum (i.val + 1) +
          c.orderSequence.prefixSum (i.val - 1) := by
      rw [ordUnit_mul, ordUnit_mul, hneg, zero_add,
        b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (i.val + 1) (by
            have hi := i.lt_large
            omega),
        c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
          (i.val - 1) (by
            have hi := i.lt_large
            omega)]
    rw [horder] at hodd
    exact hodd
  have htargetEntry : b.orderSequence.entryOrZero i.val =
      b.order (Fin.mk i.val i.lt_large) := by
    simpa using b.orderSequence_entryOrZero_eq_order
      (Fin.mk i.val i.lt_large)
  have hcomparisonEntry : c.orderSequence.entryOrZero (i.val - 1) =
      c.order (evenTargetPreviousIndex i) := by
    simpa only [evenTargetPreviousIndex] using
      c.orderSequence_entryOrZero_eq_order (evenTargetPreviousIndex i)
  have hcomparisonPrefix : c.orderSequence.prefixSum i.val =
      c.orderSequence.prefixSum (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1) := by
    have hiDecompose : i.val = (i.val - 1) + 1 := by
      have hiPos := i.pos
      omega
    calc
      c.orderSequence.prefixSum i.val =
          c.orderSequence.prefixSum ((i.val - 1) + 1) := by
        exact congrArg c.orderSequence.prefixSum hiDecompose
      _ = c.orderSequence.prefixSum (i.val - 1) +
          c.orderSequence.entryOrZero (i.val - 1) := by
        rw [c.orderSequence.prefixSum_succ]
  rw [Int.modEq_iff_dvd] at hprefix
  rcases hprefix with ⟨prefixShift, hprefixShift⟩
  rcases hsumOdd with ⟨sumHalf, hsumFormula⟩
  rcases hbetaOdd with ⟨betaHalf, hbetaFormula⟩
  rw [b.orderSequence.prefixSum_succ, htargetEntry] at hsumFormula
  rw [hcomparisonPrefix, hcomparisonEntry] at hprefixShift
  have hcurrentBaseEven : Even
      (c.order (evenTargetPreviousIndex i) - b.order first.castSucc) := by
    refine ⟨b.orderSequence.prefixSum i.val + prefixShift + betaHalf -
      sumHalf, ?_⟩
    omega
  have hcurrentLowerFinal : b.order first.castSucc <=
      c.order (evenTargetPreviousIndex i) := by
    rcases hcurrentBaseEven with ⟨d, hd⟩
    omega
  apply WithTop.coe_le_coe.mpr
  have hprimary :=
    representationAlphaValue_le_order_sub_of_primaryProduct_odd
      b c i (c.order (evenTargetPreviousIndex i)) hodd le_rfl
  push_cast at hprimary hformula
  simp only [first, last] at hformula
  have hcurrentLowerFinalQ :
      (b.order first.castSucc : Rat) <=
        (c.order (evenTargetPreviousIndex i) : Rat) := by
    exact_mod_cast hcurrentLowerFinal
  linarith

end BONG.GoodBONG

end Bong
