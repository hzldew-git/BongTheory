/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenComplete
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 8: odd type-III domination

Extended capped domination is applied to the even comparison prefix of
length `i - 1`.  A witness of order at least `R + 2` proves the beta
estimate immediately; otherwise the norm floor forces exact order `R + 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Odd comparison-prefix domination either closes the beta estimate or
returns an exact low witness together with both capped inequalities. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_or_exists_lowWitness
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.outer.last hlast) (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hiOdd : Odd i.val)
    (hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
      (((b.order
            (Fin.mk D.outer.transition.lastZero (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) -
          a.order
            (Fin.mk (D.outer.transition.lastZero + 1) (by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega)) : Int) : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) <=
        (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) \/
      exists j : Fin (n + 1), Even j.val /\ j.val + 1 < i.val - 1 /\
        c.order j.castSucc =
          a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 /\
        c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
          (((b.order
                (Fin.mk D.outer.transition.lastZero (by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega)) -
              a.order
                (Fin.mk (D.outer.transition.lastZero + 1) (by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega)) : Int) : Rat) : WithTop Rat) /\
        (((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) <=
          ((b.order
                (Fin.mk D.outer.transition.lastZero (by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega)) -
              a.order
                (Fin.mk (D.outer.transition.lastZero + 1) (by
                  have hbound := D.outer.transition.firstTwo_le_rank
                  rw [D.adjacent] at hbound
                  omega)) : Int) : Rat) := by
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
  have hiTwo : 2 <= i.val := by
    have hlastOdd := beli2019Lemma79_typeIII_last_odd a b D hfirst
    rcases hlastOdd with ⟨d, hd⟩
    omega
  have hfirstLast : first <= last := by
    change D.outer.last <= i.val - 1
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
  have hlengthEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    omega
  have hlengthPos : 0 < i.val - 1 := by omega
  have hnextBound : i.val - 1 < n + 2 :=
    (Nat.sub_le i.val 1).trans_lt i.lt_large
  rcases c.exists_even_capped_domination_order_bound_through_next
      (i.val - 1) hlengthPos hnextBound hlengthEven with
    ⟨j, hjEven, hjlt, hjPair, hjCoefficient⟩
  have hprevious :
      (Fin.mk (i.val - 1) hnextBound : Fin (n + 2)) =
        evenTargetPreviousIndex i := by
    apply Fin.ext
    rfl
  have hpreviousAlpha :
      (Fin.mk (i.val - 1 - 1) (by omega) : Fin (n + 1)) =
        evenTargetPreviousAlphaIndex i := by
    apply Fin.ext
    rfl
  rw [hcomparison] at hjPair hjCoefficient
  rw [hprevious, hpreviousAlpha] at hjCoefficient
  have hjCoefficientQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) <= centralQ := by
    exact_mod_cast hjCoefficient
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hreferenceLower : reference + 1 <=
      c.order (0 : Fin (n + 2)) := by
    change a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 <=
      c.order (0 : Fin (n + 2))
    rw [hsourceLeft,
      show a.orderSequence.entryOrZero 0 =
          a.order (0 : Fin (n + 2)) by
        simpa using a.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2))]
    exact hnormOrder
  have hzeroCurrentEntry := c.orderSequence.entryOrZero_le_of_evenGap
    0 j.val (Nat.zero_le _) (by omega) hjEven
  have hzeroCurrent : c.order (0 : Fin (n + 2)) <=
      c.order j.castSucc := by
    have hzeroEntry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    have hjEntry : c.orderSequence.entryOrZero j.val =
        c.order j.castSucc := by
      simpa using c.orderSequence_entryOrZero_eq_order j.castSucc
    rw [hzeroEntry, hjEntry] at hzeroCurrentEntry
    exact hzeroCurrentEntry
  by_cases hhigh : reference + 2 <= c.order j.castSucc
  · left
    apply WithTop.coe_le_coe.mpr
    have hprimaryTop :=
      lemma79_even_representationAlphaValue_le_primaryCoefficient
        b c i hiTwo
    have hprimary : b.representationAlphaValue c i <=
        ((b.order (Fin.mk i.val i.lt_large) -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) := by
      exact_mod_cast hprimaryTop
    have hhighQ : (reference : Rat) + 2 <=
        (c.order j.castSucc : Rat) := by
      exact_mod_cast hhigh
    rw [hcentralReference] at hjCoefficientQ
    push_cast at hprimary hjCoefficientQ hhighQ hformula
    simp only [last] at hformula
    linarith
  · right
    have hjOrder : c.order j.castSucc = reference + 1 := by
      have hlower : reference + 1 <= c.order j.castSucc :=
        hreferenceLower.trans hzeroCurrent
      omega
    refine ⟨j, hjEven, hjlt, ?_, hjPair, ?_⟩
    · simpa only [reference] using hjOrder
    · simpa only [centralQ] using hjCoefficientQ

end BONG.GoodBONG

end Bong
