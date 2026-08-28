/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenNonintegral
import Bong.Bong.Beli2019Lemma79EvenTypeIEqualityParity
import Bong.Bong.Beli2019Lemma79EvenTargetParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: even type-III equality parity

Equality in the domination coefficient identifies two comparison right
alpha endpoints.  Lemma 7.3(ii) then gives the comparison prefix class
`R + 1`, while the type-III tail gives the target prefix class `R`.
Their signed primary product therefore has odd order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Equality in the low-witness domination chain makes the signed primary
product at an even nonoverlapping type-III coordinate have odd order. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_equality_primaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
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
    (hself : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
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
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val)
    (hjOrder : c.order j.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1)
    (hjPair : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
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
              omega)) : Int) : Rat)) :
    Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))) := by
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
  have hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
    rw [hself]
    simpa only [centralQ] using hjPair
  have hjOrderCurrent : c.order j.castSucc = (reference + 2) - 1 := by
    simp only [reference]
    omega
  have heq : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((show Rat from
          (((reference + 2) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop Rat) := by
    calc
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
          (centralQ : WithTop Rat) := by
        simpa only [centralQ] using hself
      _ = ((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
            WithTop Rat) := by
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        simpa only [centralQ] using hcoefficient.symm
      _ = ((show Rat from
          (((reference + 2) -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
            WithTop Rat) := by
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        rw [hjOrderCurrent]
        push_cast
        ring
  have hendpoint := lemma79_even_rightEndpoint_eq_of_domination_equality
    c i hiTwo j hjBefore (reference + 2) hjOrderCurrent hjDefect heq
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstLower : reference + 1 <=
      c.orderSequence.entryOrZero 0 := by
    change a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 <=
      c.orderSequence.entryOrZero 0
    rw [hsourceLeft,
      show a.orderSequence.entryOrZero 0 =
          a.order (0 : Fin (n + 2)) by
        simpa using a.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2)),
      show c.orderSequence.entryOrZero 0 =
          c.order (0 : Fin (n + 2)) by
        simpa using c.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2))]
    exact hnormOrder
  have hcRaw := lemma79_typeI_even_thirdPrefix_modEq_of_rightEndpoint_eq
    c i hiTwo hiEven j hjEven hjBefore (reference + 1) hfirstLower
      (by simpa only [reference] using hjOrder) hendpoint
  have hcountPreviousOne : Int.ModEq 2
      (((i.val - 1 : Nat) : Int)) 1 := by
    rcases hiEven with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    have hoddNat : Odd (i.val - 1) := by
      refine ⟨d - 1, ?_⟩
      omega
    have hoddInt : Odd (((i.val - 1 : Nat) : Int)) := by
      exact_mod_cast hoddNat
    exact modEq_two_one_of_odd hoddInt
  have hc : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * (reference + 1)) :=
    hcRaw.trans (by
      simpa only [one_mul] using
        (hcountPreviousOne.mul_right (reference + 1)).symm)
  have hfirstTail : first <= last := by
    change D.outer.last <= i.val - 1
    have hiPos := i.pos
    omega
  have hbReference :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefix_modEq_reference
      a b D hfirst hdefect hnotOverlap hlast H hfirstTail
        hstrictLast (i.val + 1) (by omega) (by
          rw [caseEightLastAlphaIndex_val]
          have hiPos := i.pos
          omega)
  have hbShift : Int.ModEq 2
      (((i.val + 1 : Nat) : Int) * reference)
      (((i.val + 1 : Nat) : Int) * ((reference + 1) + 1)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨((i.val + 1 : Nat) : Int), ?_⟩
    ring
  have hb : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * ((reference + 1) + 1)) :=
    hbReference.trans hbShift
  have hiPrefixBound : i.val + 1 <= n + 2 := by
    have hi := i.lt_large
    omega
  exact lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEven hiTwo hiPrefixBound (reference + 1) hb hc

end BONG.GoodBONG

end Bong
