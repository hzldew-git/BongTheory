/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapOddFullRank
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapParity
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddSeparatedDefect

/-!
# Beli (2019), Lemma 7.9(ii), case 8: separated odd type-III prefixes

If the odd comparison self-prefix differs from the central target prefix,
sharp multiplication bounds the mixed primary defect by `R - S + 2`.
The comparison-order bound `T_i >= R + 2` then proves `B_i <= beta_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The unequal comparison-prefix alternative at an odd nonoverlapping
type-III index already satisfies the final beta estimate. -/
theorem beli2019Lemma79_typeIII_nonoverlap_odd_beta_bound_of_comparisonPrefix_ne
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      ⟨D.outer.transition.lastZero, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩ ≠ 1)
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last + 1 ≤ i.val)
    (H : CaseEightStrictBetaTailConsequences b
      ⟨D.outer.last, hlast⟩ (caseEightLastAlphaIndex i))
    (hstrictLast : b.alphaValue (caseEightLastAlphaIndex i) <
      a.alphaValue (caseEightLastAlphaIndex i))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hiOdd : Odd i.val)
    (hcomparisonNe : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) ≠
        (((b.order ⟨D.outer.transition.lastZero, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ -
            a.order ⟨D.outer.transition.lastZero + 1, by
              have hbound := D.outer.transition.firstTwo_le_rank
              rw [D.adjacent] at hbound
              omega⟩ : Int) : Rat) : WithTop Rat)) :
    (b.representationAlphaValue c i : WithTop Rat) ≤
      (b.alphaValue (caseEightLastAlphaIndex i) : WithTop Rat) := by
  let first : Fin (n + 1) := ⟨D.outer.last, hlast⟩
  let last : Fin (n + 1) := caseEightLastAlphaIndex i
  let centralQ : Rat :=
    ((b.order ⟨D.outer.transition.lastZero, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ -
        a.order ⟨D.outer.transition.lastZero + 1, by
          have hbound := D.outer.transition.firstTwo_le_rank
          rw [D.adjacent] at hbound
          omega⟩ : Int) : Rat)
  have htarget :=
    beli2019Lemma79_typeIII_nonoverlap_targetPrefixDefect_at_oddIndex_complete
      a b D hfirst hdefect hnotOverlap hinitial hlast i hafter H
        hstrictLast hiOdd
  have hmixed := caseEight_gapTwo_odd_mixedDefect_le_of_comparisonPrefix_ne
    b c i hiOdd (centralQ : WithTop Rat)
      (by simpa only [centralQ] using htarget)
      (by simpa only [centralQ] using hcomparisonNe)
  have hcomparisonOrder :=
    beli2019Lemma79_typeIII_nonoverlap_odd_comparisonOrder_ge_reference_add_two
      a b c D hfirst hdefect hnotOverlap hnorm hlast i hafter H
        hstrictLast hprefix hiOdd
  have hfirstLast : first ≤ last := by
    change D.outer.last ≤ i.val - 1
    have hiPos := i.pos
    omega
  have hformulaData := beli2019Lemma79_typeIII_caseEight_gapOne_formula
    a b D last (by
      change D.outer.last ≤ last.val
      exact hfirstLast)
      (by simpa only [first, last] using H) hstrictLast
  have hformula := hformulaData.2 last
    (by simpa only [first, last] using hfirstLast) le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hformula
  have hcentralReference : centralQ =
      ((a.orderSequence.entryOrZero D.outer.transition.lastZero -
          b.order first.castSucc + 2 : Int) : Rat) := by
    simpa only [centralQ, first] using
      beli2019Lemma79_typeIII_nonoverlap_central_eq_reference_sub_base_add_two
        a b D hlast
  have harith :
      ((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) + centralQ ≤
        b.alphaValue last := by
    have hcomparisonQ :
        (a.orderSequence.entryOrZero D.outer.transition.lastZero : Rat) + 2 ≤
          (c.order (evenTargetPreviousIndex i) : Rat) := by
      exact_mod_cast hcomparisonOrder
    rw [hcentralReference]
    push_cast at hformula hcomparisonQ ⊢
    simp only [first, last] at hformula ⊢
    linarith
  rw [b.coe_representationAlphaValue c i]
  calc
    b.representationAlpha c i ≤ b.representationPrimaryDefect c i :=
      b.representationAlpha_le_primary c i
    _ ≤
        ((((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) :
              WithTop Rat) + (centralQ : WithTop Rat)) := by
      unfold representationPrimaryDefect
      simpa only [evenTargetPreviousIndex] using
        add_le_add_right hmixed
          ((((b.order ⟨i.val, i.lt_large⟩ -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) :
              WithTop Rat))
    _ ≤ (b.alphaValue last : WithTop Rat) := by
      exact_mod_cast harith
    _ = _ := by rfl

end BONG.GoodBONG

end Bong
